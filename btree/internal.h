/* -*- C -*- */
/*
 * Copyright (c) 2013-2021 Seagate Technology LLC and/or its Affiliates
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * For any questions about this software or licensing,
 * please email opensource@seagate.com or cortx-questions@seagate.com.
 *
 */

#pragma once

#ifndef __MOTR_BTREE_INTERNAL_H__
#define __MOTR_BTREE_INTERNAL_H__

#include "be/op.h"   /* m0_be_op */
#include "format/format.h" /* struct m0_format_header */
#include "format/format_xc.h" /* struct m0_format_header */
#include "fid/fid.h"
#include "fid/fid_xc.h"

/**
 * @defgroup btree
 *
 * @{
 */

struct m0_btree_oimpl;

enum m0_btree_node_format_version {
	M0_BTREE_NODE_FORMAT_VERSION_1 = 1,

	/* future versions, uncomment and update M0_BE_BNODE_FORMAT_VERSION */
	/*M0_BTREE_NODE_FORMAT_VERSION_2,*/
	/*M0_BTREE_NODE_FORMAT_VERSION_3,*/

	/** Current version, should point to the latest version present */
	M0_BTREE_NODE_FORMAT_VERSION = M0_BTREE_NODE_FORMAT_VERSION_1
};

struct m0_btree_cursor {
	struct m0_buf    bc_key;
	struct m0_buf    bc_val;
	struct m0_btree *bc_arbor;
	struct m0_be_op  bc_op;
};

struct td;
struct m0_btree {
	const struct m0_btree_type *t_type;
	unsigned                    t_height;
	struct td                  *t_desc;
};

/**
 * Common node header.
 *
 * This structure is located at the beginning of every node, right after
 * m0_format_header. It is used by the segment operations (node_op) to identify
 * node and tree types.
 */
struct node_header {
	uint32_t      h_node_type;
	uint32_t      h_tree_type;
	uint64_t      h_gen;
	struct m0_fid h_fid;
	uint64_t      h_opaque;
} M0_XCA_RECORD M0_XCA_DOMAIN(be);

/**
 *  Structure of the node in persistent store.
 */
struct ff_head {
	struct m0_format_header  ff_fmt;    /*< Node Header */
	struct node_header       ff_seg;    /*< Node type information */

	/**
	 * The above 2 structures should always be together with node_header
	 * following the m0_format_header.
	 */

	uint16_t                 ff_used;   /*< Count of records */
	uint8_t                  ff_shift;  /*< Node size as pow-of-2 */
	uint8_t                  ff_level;  /*< Level in Btree */
	uint16_t                 ff_ksize;  /*< Size of key in bytes */
	uint16_t                 ff_vsize;  /*< Size of value in bytes */
	struct m0_format_footer  ff_foot;   /*< Node Footer */
	void                    *ff_opaque; /*< opaque data */
	/**
	 *  This space is used to host the Keys and Values upto the size of the
	 *  node
	 */
} M0_XCA_RECORD M0_XCA_DOMAIN(be);

struct fkvv_head {
	struct m0_format_header  fkvv_fmt;    /*< Node Header */
	struct node_header       fkvv_seg;    /*< Node type information */

	/**
	 * The above 2 structures should always be together with node_header
	 * following the m0_format_header.
	 */

	uint16_t                 fkvv_used;   /*< Count of records */
	uint8_t                  fkvv_shift;  /*< Node size as pow-of-2 */
	uint8_t                  fkvv_level;  /*< Level in Btree */
	uint16_t                 fkvv_ksize;  /*< Size of key in bytes */
	struct m0_format_footer  fkvv_foot;   /*< Node Footer */
	void                    *fkvv_opaque; /*< opaque data */
	/**
	 *  This space is used to host the Keys and Values upto the size of the
	 *  node
	 */
} M0_XCA_RECORD M0_XCA_DOMAIN(be);

struct dir_rec {
	uint32_t key_offset;
	uint32_t val_offset;
} M0_XCA_RECORD M0_XCA_DOMAIN(be);
struct vkvv_head {
	struct m0_format_header  vkvv_fmt;        /*< Node Header */
	struct node_header       vkvv_seg;        /*< Node type information */
	/**
	 * The above 2 structures should always be together with node_header
	 * following the m0_format_header.
	 */

	uint16_t                 vkvv_used;       /*< Count of records */
	uint8_t                  vkvv_shift;      /*< Node size as pow-of-2 */
	uint8_t                  vkvv_level;      /*< Level in Btree */
	uint32_t                 vkvv_dir_offset; /*< Offset pointing to dir */

	struct m0_format_footer  vkvv_foot;       /*< Node Footer */
	void                    *vkvv_opaque;     /*< opaque data */
	/**
	 *  This space is used to host the Keys, Values and Directory upto the
	 *  size of the node.
	 */
} M0_XCA_RECORD M0_XCA_DOMAIN(be);

/** @} end of btree group */
#endif /* __MOTR_BTREE_INTERNAL_H__ */

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  fill-column: 80
 *  scroll-step: 1
 *  End:
 */
/*
 * vim: tabstop=8 shiftwidth=8 noexpandtab textwidth=80 nowrap
 */
