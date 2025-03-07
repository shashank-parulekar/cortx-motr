#!/usr/bin/env bash
#
# Copyright (c) 2020-2021 Seagate Technology LLC and/or its Affiliates
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
TOPDIR="$(dirname "$0")/../../../"

. "${TOPDIR}/spiel/st/m0t1fs_spiel_sns_common_inc.sh"
. "${TOPDIR}/motr/st/utils/sns_repair_common_inc.sh"
. "${TOPDIR}/m0t1fs/linux_kernel/st/common.sh"
. "${TOPDIR}/m0t1fs/linux_kernel/st/m0t1fs_common_inc.sh"
. "${TOPDIR}/m0t1fs/linux_kernel/st/m0t1fs_client_inc.sh"
. "${TOPDIR}/m0t1fs/linux_kernel/st/m0t1fs_server_inc.sh"
. "${TOPDIR}/m0t1fs/linux_kernel/st/m0t1fs_sns_common_inc.sh"
S=3
N=3
K=3
P=15
export MOTR_CLIENT_ONLY=1

spiel_sns_repair_and_rebalance_test()
{
	local fail_device1=1
	local fail_device2=9
	local fail_device3=3

	echo "Starting SNS repair testing ..."
	prepare_datafiles_and_objects || return "$?"
	motr_read_verify 0          || return "$?"

	for ((i=0; i < ${#IOSEP[*]}; i++)) ; do
		ios_eps="$ios_eps -S ${lnet_nid}:${IOSEP[$i]}"
	done

	#######################################################################
	#  Now starting SPIEL sns repair/rebalance abort/continue testing     #
	#######################################################################

	echo "Set Failure device: $fail_device1 $fail_device2"
	disk_state_set "failed" "$fail_device1" "$fail_device2" || return $?
	motr_read_verify 0 || return $?
	disk_state_get "$fail_device1" "$fail_device2" || return "$?"
	echo "Device $fail_device1 and $fail_device2 failed. Do dgmode read"

	echo "Start SNS repair (1)."
	disk_state_set "repair" "$fail_device1" "$fail_device2" || return "$?"
	spiel_sns_repair_start
	sleep 2
	echo "Abort SNS repair (1)."
	spiel_sns_repair_abort

	echo "wait for sns repair (1)."
	spiel_wait_for_sns_repair || return "$?"

	motr_read_verify 0 || return "$?"

	echo "start SNS repair again (2).."
	spiel_sns_repair_start
	sleep 3

	# Another device failed during the above SNS repair.
	# We need to abort current SNS first, and then we start SNS repair again.
	echo "Abort SNS repair (2).."
	spiel_sns_repair_abort

	echo "wait for sns repair abort (2).."
	spiel_wait_for_sns_repair || return "$?"

        echo "failing another device ($fail_device3)"
        disk_state_set "failed" "$fail_device3" || return "$?"
	disk_state_set "repair" "$fail_device3" || return "$?"

	echo "start SNS repair again (3)..."
	spiel_sns_repair_start
	sleep 3

	echo "wait for the third sns repair (3)..."
	spiel_wait_for_sns_repair || return "$?"

	disk_state_set "repaired" "$fail_device1" "$fail_device2" "$fail_device3" || return "$?"
	echo "SNS Repair done."
	motr_read_verify 0 || return "$?"

	disk_state_get "$fail_device1" "$fail_device2" "$fail_device3" || return "$?"

	disk_state_set "rebalance" "$fail_device1" "$fail_device2" "$fail_device3" || return "$?"
	disk_state_get "$fail_device1" "$fail_device2" "$fail_device3" || return "$?"
        sleep 2
	echo "Starting SNS Re-balance.. (1)"
	spiel_sns_rebalance_start
	sleep 2
	echo "wait for sns rebalance"
	spiel_wait_for_sns_rebalance || return "$?"
	disk_state_set "online" "$fail_device1" "$fail_device2" "$fail_device3" || return "$?"
	echo "SNS Rebalance done."

	motr_read_verify 0 || return "$?"

	disk_state_get "$fail_device1" "$fail_device2" "$fail_device3" || return "$?"

	#CORTX-30750: Commenting this testcase temporarily, while we are debugging the panic in degraded read
	#Refer CORTX-30750 for more details
        #echo "Testing SNS rebalance abort with new disk failure..."
	#rebalance_abort 1 9 || return "$?"

	#echo "Testing SNS rebalance abort with repaired disk failure..."
	#rebalance_abort 1 1 || return "$?"
	#######################################################################
	#  End                                                                #
	#######################################################################

	return 0
}

test_repaired_device_failure()
{
	local fail_device1=$1

	disk_state_get "$fail_device1" || return "$?"

	disk_state_set "rebalance" "$fail_device1" || return "$?"
	echo "Starting SNS Rebalance.."
	spiel_sns_rebalance_start

        echo "wait for sns Re-balance"
        spiel_wait_for_sns_rebalance || return "$?"
	sleep 2

	disk_state_set "online" "$fail_device1" || return "$?"
	echo "SNS Rebalance done."

	motr_read_verify 0 || return "$?"
	disk_state_get "$fail_device1" || return "$?"
}

test_new_device_failure()
{
	local fail_device1=$1
	local fail_device2=$2

	echo "Set $fail_device2 to "failed""
	disk_state_set "failed" "$fail_device2" || return "$?"
	disk_state_set "repair" "$fail_device2" || return "$?"

	echo "Start SNS repair again"
	spiel_sns_repair_start
	sleep 2

	echo "wait for the sns repair"
	spiel_wait_for_sns_repair || return "$?"
	motr_read_verify 0 || return "$?"

	disk_state_set "repaired" "$fail_device2" || return "$?"

	disk_state_get "$fail_device1" "$fail_device2" || return "$?"

	disk_state_set "rebalance" "$fail_device1" "$fail_device2" || return "$?"
	echo "Starting SNS Rebalance.."
	spiel_sns_rebalance_start

        echo "wait for sns Re-balance"
        spiel_wait_for_sns_rebalance || return "$?"
	sleep 2

	disk_state_set "online" "$fail_device1" "$fail_device2" || return "$?"
	echo "SNS Rebalance done."

	motr_read_verify 0 || return "$?"
	disk_state_get "$fail_device1" "$fail_device2" || return "$?"
}

rebalance_abort()
{
	local fail_device1=$1
	local fail_device2=$2

	echo "Set Failure device: $fail_device1"
	disk_state_set "failed" "$fail_device1" || return "$?"

	echo "Start SNS repair."
        echo "set $fail_device1 to repairing"
	disk_state_set "repair" "$fail_device1" || return "$?"
	spiel_sns_repair_start
	sleep 2

	echo "wait for sns repair to finish."
	spiel_wait_for_sns_repair || return "$?"

	disk_state_set "repaired" "$fail_device1" || return "$?"
	echo "SNS Repair done."
	motr_read_verify 0 || return "$?"

	disk_state_set "rebalance" "$fail_device1" || return "$?"
	disk_state_get "$fail_device1" || return "$?"
        sleep 2
	echo "Starting SNS Re-balance.."
	spiel_sns_rebalance_start
	sleep 2
        echo "Abort SNS Rebalance"
        spiel_sns_rebalance_abort
        echo "wait for sns Re-balance abort (1)"
        spiel_wait_for_sns_rebalance || return $?

	echo "Set $fail_device1 back to "repaired""
	disk_state_set "repaired" "$fail_device1" || return "$?"
	if [ "$fail_device1" -eq "$fail_device2" ]
	then
		test_repaired_device_failure "$fail_device1" || return "$?"
	else
		test_new_device_failure "$fail_device1" "$fail_device2" || return "$?"
	fi
}

main()
{
	local rc=0

	sandbox_init

	NODE_UUID=$(uuidgen)
	local multiple_pools=0
	motr_service start $multiple_pools "$stride" "$N" "$K" "$S" "$P" || {
		echo "Failed to start Motr Service."
		return 1
	}

        spiel_prepare

	if [[ $rc -eq 0 ]] && ! spiel_sns_repair_and_rebalance_test ; then
		echo "Failed: SNS repair failed.."
		rc=1
	fi

        spiel_cleanup

	motr_service stop || {
		echo "Failed to stop Motr Service."
		rc=1
	}

	if [ $rc -eq 0 ]; then
		sandbox_fini
	else
		echo "Test log available at $MOTR_TEST_LOGFILE."
	fi
	return $rc
}

trap unprepare EXIT
main
report_and_exit spiel-sns-repair $?
