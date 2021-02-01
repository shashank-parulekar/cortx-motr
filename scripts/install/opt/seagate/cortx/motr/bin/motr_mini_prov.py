#!/usr/bin/env python3
#
# Copyright (c) 2021 Seagate Technology LLC and/or its Affiliates
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# For any questions about this software or licensing,
# please email opensource@seagate.com or cortx-questions@seagate.com.
#
import sys
import errno
import os
import re
import subprocess
from cortx.utils.conf_store import Conf

MOTR_SYS_FILE = "/etc/sysconfig/motr"
MOTR_CONFIG_SCRIPT = "/opt/seagate/cortx/motr/libexec/motr_cfg.sh"
LNET_CONF_FILE = "/etc/modprobe.d/lnet.conf"
SYS_CLASS_NET_DIR = "/sys/class/net/"
MOTR_SYS_CFG = "/etc/sysconfig/motr"
FSTAB = "/etc/fstab"
TIMEOUT_SECS = 120
MACHINE_ID_LEN = 32

class MotrError(Exception):
    """ Generic Exception with error code and output """

    def __init__(self, rc, message, *args):
        self._rc = rc
        self._desc = message % (args)

    def __str__(self):
        return f"error[{self._rc}]: {self._desc}"


def execute_command(self, cmd, timeout_secs = TIMEOUT_SECS, verbose = False):
    ps = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          shell=True)
    stdout, stderr = ps.communicate(timeout=timeout_secs);
    stdout = str(stdout, 'utf-8')
    if self._debug or verbose:
        sys.stdout.write(f"[CMD] {cmd}\n")
        sys.stdout.write(f"[OUT]\n{stdout}\n")
        sys.stdout.write(f"[RET] {ps.returncode}\n")
    if ps.returncode != 0:
        raise MotrError(ps.returncode, f"\"{cmd}\" command execution failed")
    return stdout, ps.returncode

def check_type(var, vtype, msg):
    if not isinstance(var, vtype):
        raise MotrError(errno.EINVAL, f"Invalid {msg} type. Expected: {vtype}")


def get_current_node(self):
    """Get current node name using machine-id."""
    cmd = "cat /etc/machine-id"
    machine_id = execute_command(self, cmd)
    machine_id = machine_id[0].split('\n')[0]

    check_type(machine_id, str, "machine-id")
    if len(machine_id) != MACHINE_ID_LEN:
        raise MotrError(errno.EINVAL, "Invalid machine-id length."
                        f" Expected: {MACHINE_ID_LEN}"
                        f" Actual: {len(machine_id)}")

    try:
        current_node = Conf.get(self._index, 'cluster>server_nodes')[machine_id]
    except:
        raise MotrError(errno.EINVAL, "Current node not found")

    check_type(current_node, str, "current node")
    return current_node


def restart_services(self, services):
    for service in services:
        sys.stdout.write(f"Restarting {service} service\n")
        cmd = f"systemctl stop {service}"
        execute_command(self, cmd)
        cmd = f"systemctl start {service}"
        execute_command(self, cmd)
        cmd = f"systemctl status {service}"
        execute_command(self, cmd)

def validate_file(file):
    if not os.path.exists(file):
        raise MotrError(errno.ENOENT, f"{file} not exist")

def is_hw_node(self):
    try:
        node_type = Conf.get(self._index,
                    f'cluster>{self._server_id}')['node_type']
    except:
        raise MotrError(errno.EINVAL, "node_type not found")
    check_type(node_type, str, "node type")
    if node_type == "HW":
        return True
    else:
        return False

def validate_motr_rpm(self):
    '''
        1. check m0tr.ko exists in current kernel modules
        2. check /etc/sysconfig/motr
    '''
    cmd = "uname -r"
    cmd_res = execute_command(self, cmd)
    op = cmd_res[0]
    kernel_ver = op.replace('\n', '')
    check_type(kernel_ver, str, "kernel version")

    kernel_module = f"/lib/modules/{kernel_ver}/kernel/fs/motr/m0tr.ko"
    sys.stdout.write(f"Checking for {kernel_module}\n")
    validate_file(kernel_module)

    sys.stdout.write(f"Checking for {MOTR_SYS_FILE}\n")
    validate_file(MOTR_SYS_FILE)


def motr_config(self):
    is_hw = is_hw_node(self)
    if is_hw:
        sys.stdout.write(f"Executing {MOTR_CONFIG_SCRIPT}")
        execute_command(self, MOTR_CONFIG_SCRIPT, verbose = True)

def configure_net(self):
    """Wrapper function to detect lnet/libfabric transport."""
    try:
        transport_type = Conf.get(self._index,
            f'cluster>{self._server_id}')['network']['data']['transport_type']
    except:
        raise MotrError(errno.EINVAL, "transport_type not found")
    check_type(transport_type, str, "transport_type")

    if transport_type == "lnet":
        configure_lnet(self)
    elif transport_type == "libfabric":
        configure_libfabric(self)
    else:
        raise MotrError(errno.EINVAL, "Unknown data transport type\n")

def configure_lnet(self):
    '''
       Get iface and /etc/modprobe.d/lnet.conf params from
       conf store. Configure lnet. Start lnet service
    '''
    try:
        iface = Conf.get(self._index,
        f'cluster>{self._server_id}')['network']['data']['private_interfaces']
        iface = iface[0]
    except:
        raise MotrError(errno.EINVAL, "private_interfaces[0] not found\n")

    sys.stdout.write(f"Validate private_interfaces[0]: {iface}\n")
    cmd = f"ip addr show {iface}"
    execute_command(self, cmd)

    try:
        iface_type = Conf.get(self._index,
            f'cluster>{self._server_id}')['network']['data']['interface_type']
    except:
        raise MotrError(errno.EINVAL, "interface_type not found\n")

    lnet_config = (f"options lnet networks={iface_type}({iface}) "
                  f"config_on_load=1  lnet_peer_discovery_disabled=1\n")
    sys.stdout.write(f"lnet config: {lnet_config}")

    with open(LNET_CONF_FILE, "w") as fp:
        fp.write(lnet_config)

    restart_services(self, ["lnet"])

def configure_libfabric(self):
    raise MotrError(errno.EINVAL, "libfabric not implemented\n")


def swap_on(self):
    cmd = "swapon -a"
    execute_command(self, cmd)

def swap_off(self):
    cmd = "swapoff -a"
    execute_command(self, cmd)

def add_swap_fstab(self, dev_name):
    '''
        1. check swap entry found in /etc/fstab
        2. if found, do nothing
        3. if not found, add swap entry in /etc/fstab
    '''
    swap_entry = f"{dev_name}    swap    swap    defaults        0 0\n"
    swap_found = False
    swap_off(self)
    try:
        with open(FSTAB, "r") as fp:
            lines = fp.readlines()
            for line in lines:
                ret = line.find(dev_name)
                if ret == 0:
                    swap_found = True
                    sys.stdout.write(f"Swap entry found: {swap_entry}\n")
    except:
        swap_on(self)
        raise MotrError(errno.EINVAL, f"Cant read f{FSTAB}\n")


    try:
        if not swap_found:
            with open(FSTAB, "a") as fp:
                fp.write(swap_entry)
            sys.stdout.write(f"Swap entry added: {swap_entry}\n")
    except:
        raise MotrError(errno.EINVAL, f"Cant append f{FSTAB}\n")
    finally:
        swap_on(self)

def del_swap_fstab_by_vg_name(self, vg_name):

    swap_off(self)

    cmd = f"sed -i '/{vg_name}/d' {FSTAB}"
    execute_command(self, cmd)

    swap_on(self)

def create_swap(self, swap_dev):

    sys.stdout.write(f"Make swap of {swap_dev}\n")
    cmd = f"mkswap -f {swap_dev}"
    execute_command(self, cmd)

    sys.stdout.write(f"Test {swap_dev} swap device\n")
    cmd = f"test -e {swap_dev}"
    execute_command(self, cmd)

    sys.stdout.write(f"Adding {swap_dev} swap device to {FSTAB}\n")
    add_swap_fstab(self, swap_dev)


def create_lvm(self, index, metadata_dev):
    '''
        1. validate /etc/fstab
        2. validate metadata device file
        3. check requested volume group exist
        4. if exist, remove volume group and swap related with it.
           because if user request same volume group with different device.
        5. If not exist, create volume group and lvm
        6. create swap from lvm
    '''

    metadata_dev = f"{metadata_dev}2"
    index = index + 1
    node_name = self._server_id
    vg_name = f"vg_{node_name}_md{index}"
    lv_swap_name = f"lv_main_swap{index}"
    lv_md_name = f"lv_raw_md{index}"
    swap_dev = f"/dev/{vg_name}/{lv_swap_name}"

    sys.stdout.write(f"metadata device: {metadata_dev}\n")

    sys.stdout.write(f"Checking for {FSTAB}\n")
    validate_file(FSTAB)

    sys.stdout.write(f"Checking for {metadata_dev}\n")
    validate_file(metadata_dev)

    cmd = f"fdisk -l {metadata_dev}"
    execute_command(self, cmd)

    try:
        cmd = f"vgs {vg_name}"
        execute_command(self, cmd)
    except MotrError:
        pass
    else:
        sys.stdout.write(f"Removing {vg_name} volume group\n")

        del_swap_fstab_by_vg_name(self, vg_name)

        cmd = f"vgchange -an {vg_name}"
        execute_command(self, cmd)

        cmd = f"vgremove {vg_name} -ff"
        execute_command(self, cmd)

    sys.stdout.write(f"Creating physical volume from {metadata_dev}\n")
    cmd = f"pvcreate {metadata_dev} --yes"
    execute_command(self, cmd)

    sys.stdout.write(f"Creating {vg_name} volume group from {metadata_dev}\n")
    cmd = f"vgcreate {vg_name} {metadata_dev}"
    execute_command(self, cmd)

    sys.stdout.write(f"Adding {node_name} tag to {vg_name} volume group\n")
    cmd = f"vgchange --addtag {node_name} {vg_name}"
    execute_command(self, cmd)

    sys.stdout.write("Scanning volume group\n")
    cmd = "vgscan --cache"
    execute_command(self, cmd)

    sys.stdout.write(f"Creating {lv_swap_name} lvm from {vg_name}\n")
    cmd = f"lvcreate -n {lv_swap_name} {vg_name} -l 51%VG --yes"
    execute_command(self, cmd)

    sys.stdout.write(f"Creating {lv_md_name} lvm from {vg_name}\n")
    cmd = f"lvcreate -n {lv_md_name} {vg_name} -l 100%FREE --yes"
    execute_command(self, cmd)

    create_swap(self, swap_dev)


def config_lvm(self):
    """Create volume group and lvm for swap and metadata."""
    try:
        metadata_devices = Conf.get(self._index,
                f'cluster>{self._server_id}')['storage']['metadata_devices']
    except:
        raise MotrError(errno.EINVAL, "metadata_devices not found\n")
    check_type(metadata_devices, list, "metadata_devices")
    
    sys.stdout.write(f"\nlvm metadata_devices: {metadata_devices}\n\n")

    for device in metadata_devices:
        create_lvm(self, metadata_devices.index(device), device)


def get_lnet_xface() -> str:
    """Get lnet interface."""
    lnet_xface = None
    try:
        with open(LNET_CONF_FILE, 'r') as f:
            # Obtain interface name
            for line in f.readlines():
                if len(line.strip()) <= 0: continue
                tokens = re.split(r'\W+', line)
                if len(tokens) > 4:
                    lnet_xface = tokens[4]
                    break
    except:
        raise MotrError(errno.EINVAL, f"Cant parse {LNET_CONF_FILE}")

    if lnet_xface == None:
        raise MotrError(errno.EINVAL,
                        f"Cant obtain iface details from {LNET_CONF_FILE}")
    if lnet_xface not in os.listdir(SYS_CLASS_NET_DIR):
        raise MotrError(errno.EINVAL,
                        f"Invalid iface {lnet_xface} in lnet.conf")
    return lnet_xface

def check_pkgs(self, pkgs):
    """Check rpm packages."""
    for pkg in pkgs:
        ret = 1
        cmd = f"rpm -q {pkg}"

        try:
            cmd_res = execute_command(self, cmd)
            ret = cmd_res[1]
        except MotrError:
            pass

        if ret == 0:
            sys.stdout.write(f"rpm found: {pkg}\n")
        else:
            raise MotrError(errno.ENOENT, f"Missing rpm: {pkg}")

def get_nids(self, nodes):
    """Get lnet nids of all available nodes in cluster."""
    nids = []

    for node in nodes.values():
        try:
            hostname = Conf.get(self._index, f'cluster>{node}>hostname')
        except:
            raise MotrError(errno.EINVAL, f"{node} hostname not found")

        check_type(hostname, str, "hostname")

        if self._server_id == node:
            cmd = "lctl list_nids"
        else:
            cmd = (f"ssh  -o \"StrictHostKeyChecking=no\" {hostname}"
                    " lctl list_nids")
        op = execute_command(self, cmd)
        nids.append(op[0].rstrip("\n"))

    return nids

def lnet_ping(self):
    """Lnet lctl ping on all available nodes in cluster."""
    try:
        nodes = Conf.get(self._index, 'cluster>server_nodes')
    except:
        raise MotrError(errno.EINVAL, "Server nodes not found")

    check_type(nodes, dict, "server_nodes")

    nids = get_nids(self, nodes)

    sys.stdout.write("lnet pinging on all nodes in cluster\n")
    sys.stdout.write("motr_setup init MUST be performed on all nodes before "
                      "executing this\n")
    for nid in nids:
       cmd = f"lctl ping {nid}"
       sys.stdout.write(f"lctl ping on: {nid}\n")
       execute_command(self, cmd)

def test_lnet(self):
    '''
        1. check lustre rpm
        2. validate lnet interface which was configured in init
        3. ping on lnet interface
        4. lctl ping on all nodes in cluster. motr_setup init MUST be performed
           on all nodes before executing this step.
    '''
    search_lnet_pkgs = ["kmod-lustre-client", "lustre-client"]
    check_pkgs(self, search_lnet_pkgs)

    lnet_xface = get_lnet_xface()
    sys.stdout.write(f"lnet interface found: {lnet_xface}\n")

    cmd = f"ip addr show {lnet_xface}"
    cmd_res = execute_command(self, cmd)
    ip_addr = cmd_res[0]

    try:
        ip_addr = ip_addr.split("inet ")[1].split("/")[0]
        sys.stdout.write(f"lnet interface ip: {ip_addr}\n")
    except:
        raise MotrError(errno.EINVAL, f"Cant parse {lnet_xface} ip addr")

    sys.stdout.write(f"ping on: {ip_addr}\n")
    cmd = f"ping -c 3 {ip_addr}"
    execute_command(self, cmd)

    lnet_ping(self)
