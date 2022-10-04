/* -*- C -*- */
/*
 * Copyright (c) 2013-2020 Seagate Technology LLC and/or its Affiliates
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


#define M0_TRACE_SUBSYSTEM M0_TRACE_SUBSYS_UT
//#include <unistd.h>             /* mincore */
#include <sys/mman.h>           /* mincore */
#include <string.h>             /* memcmp */

#include "lib/trace.h"

#include "be/alloc.h"

#include "lib/memory.h"         /* m0_addr_is_aligned */
#include "lib/misc.h"           /* M0_SET_ARR0 */
#include "lib/thread.h"         /* m0_thread */
#include "lib/arith.h"          /* m0_rnd64 */
#include "lib/finject.h"        /* m0_fi_enable_once */

#include "ut/ut.h"              /* M0_UT_ASSERT */

#include "be/ut/helper.h"       /* m0_be_ut_backend */
#include "be/op.h"              /* m0_be_op */
#include "be/alloc_internal.h"  /* be_alloc_chunk */

enum {
	BE_UT_ALLOC_SEG_SIZE = 0x40000,
	BE_UT_ALLOC_SIZE     = 0x80,
	BE_UT_ALLOC_SHIFT    = 13,
	BE_UT_ALLOC_PTR_NR   = 0x20,
	BE_UT_ALLOC_NR       = 0x800,
	BE_UT_ALLOC_MT_NR    = 0x100,
	BE_UT_ALLOC_THR_NR   = 0x4,
};

struct be_ut_alloc_thread_state {
	struct m0_thread ats_thread;
	/** pointers array for this thread */
	void            *ats_ptr[BE_UT_ALLOC_PTR_NR];
	/** number of interations for this thread */
	int              ats_nr;
};

static struct m0_be_ut_backend         be_ut_alloc_backend;
static struct m0_be_ut_seg             be_ut_alloc_seg;
static struct be_ut_alloc_thread_state be_ut_ts[BE_UT_ALLOC_THR_NR];

M0_INTERNAL void m0_be_ut_alloc_init_fini(void)
{
	struct m0_be_ut_seg     ut_seg = {};
	struct m0_be_seg       *seg;
	struct m0_be_allocator *a;
	int                     rc;

	m0_be_ut_seg_init(&ut_seg, NULL, BE_UT_ALLOC_SEG_SIZE);
	seg = ut_seg.bus_seg;
	a = m0_be_seg_allocator(seg);
	rc = m0_be_allocator_init(a, seg);
	M0_UT_ASSERT(rc == 0);
	m0_be_allocator_fini(a);
	m0_be_ut_seg_fini(&ut_seg);
}

M0_INTERNAL void m0_be_ut_alloc_create_destroy(void)
{
	struct m0_be_ut_seg ut_seg;

	m0_be_ut_backend_init(&be_ut_alloc_backend);
	m0_be_ut_seg_init(&ut_seg, &be_ut_alloc_backend, BE_UT_ALLOC_SEG_SIZE);

	m0_be_ut_seg_allocator_init(&ut_seg, &be_ut_alloc_backend);

	m0_be_ut_seg_allocator_fini(&ut_seg, &be_ut_alloc_backend);

	m0_be_ut_seg_fini(&ut_seg);
	m0_be_ut_backend_fini(&be_ut_alloc_backend);
	M0_SET0(&be_ut_alloc_backend);
}

static void be_ut_alloc_ptr_handle(struct m0_be_allocator  *a,
				   void                   **p,
				   uint64_t                *seed)
{
	struct m0_be_ut_backend *ut_be = &be_ut_alloc_backend;
	m0_bcount_t              size;
	unsigned                 shift;

	size  = m0_rnd64(seed) % BE_UT_ALLOC_SIZE + 1;
	shift = m0_rnd64(seed) % BE_UT_ALLOC_SHIFT;

	if (*p == NULL) {
		M0_BE_UT_TRANSACT(ut_be, tx, cred,
			  (m0_be_allocator_credit(a, M0_BAO_ALLOC_ALIGNED,
						 size, shift, &cred),
			   m0_be_alloc_stats_credit(a, &cred)),
			  (M0_BE_OP_SYNC(op,
				 m0_be_alloc_aligned(a, tx, &op, p, size,
						     shift,
						     M0_BITS(M0_BAP_NORMAL),
						     false)),
			   m0_be_alloc_stats_capture(a, tx)));
		M0_UT_ASSERT(*p != NULL);
		M0_UT_ASSERT(m0_addr_is_aligned(*p, shift));
	} else {
		M0_BE_UT_TRANSACT(ut_be, tx, cred,
			  (m0_be_allocator_credit(a, M0_BAO_FREE_ALIGNED,
						 size, shift, &cred),
			   m0_be_alloc_stats_credit(a, &cred)),
			  (M0_BE_OP_SYNC(op,
					m0_be_free_aligned(a, tx, &op, *p,
							   false)),
			   m0_be_alloc_stats_capture(a, tx)));
		*p = NULL;
	}
}

static void be_ut_alloc_thread(int index)
{
	struct be_ut_alloc_thread_state *ts = &be_ut_ts[index];
	struct m0_be_allocator          *a;
	uint64_t                         seed = index;
	int                              i;
	int                              j;

	a = m0_be_seg_allocator(be_ut_alloc_seg.bus_seg);
	M0_UT_ASSERT(a != NULL);
	M0_SET_ARR0(ts->ats_ptr);
	for (j = 0; j < ts->ats_nr; ++j) {
		i = m0_rnd64(&seed) % ARRAY_SIZE(ts->ats_ptr);
		be_ut_alloc_ptr_handle(a, &ts->ats_ptr[i], &seed);
	}
	for (i = 0; i < BE_UT_ALLOC_PTR_NR; ++i) {
		if (ts->ats_ptr[i] != NULL) {
			be_ut_alloc_ptr_handle(a, &ts->ats_ptr[i], &seed);
		}
	}
	m0_be_ut_backend_thread_exit(&be_ut_alloc_backend);
}

static void be_ut_alloc_mt(int nr)
{
	struct m0_be_ut_backend *ut_be  = &be_ut_alloc_backend;
	struct m0_be_ut_seg     *ut_seg = &be_ut_alloc_seg;
	int                      rc;
	int                      i;

	M0_SET_ARR0(be_ut_ts);
	for (i = 0; i < nr; ++i) {
		be_ut_ts[i].ats_nr = nr == 1 ? BE_UT_ALLOC_NR :
					       BE_UT_ALLOC_MT_NR;
	}

	m0_be_ut_backend_init(ut_be);
	m0_be_ut_seg_init(ut_seg, ut_be, BE_UT_ALLOC_SEG_SIZE);
	m0_be_ut_seg_allocator_init(ut_seg, ut_be);
	for (i = 0; i < nr; ++i) {
		rc = M0_THREAD_INIT(&be_ut_ts[i].ats_thread, int, NULL,
				    &be_ut_alloc_thread, i,
				    "#%dbe_ut_alloc", i);
		M0_UT_ASSERT(rc == 0);
	}
	for (i = 0; i < nr; ++i) {
		m0_thread_join(&be_ut_ts[i].ats_thread);
		m0_thread_fini(&be_ut_ts[i].ats_thread);
	}
	m0_be_ut_seg_allocator_fini(ut_seg, ut_be);
	m0_be_ut_seg_fini(ut_seg);
	m0_be_ut_backend_fini(ut_be);
	M0_SET0(ut_be);
}

M0_INTERNAL void m0_be_ut_alloc_multiple(void)
{
	be_ut_alloc_mt(1);
}

M0_INTERNAL void m0_be_ut_alloc_concurrent(void)
{
	be_ut_alloc_mt(BE_UT_ALLOC_THR_NR);
}

static void be_ut_alloc_credit_log(struct m0_be_allocator  *a,
				   enum m0_be_allocator_op  optype,
				   const char              *optype_str,
				   m0_bcount_t              size,
				   unsigned                 shift)
{
	struct m0_be_tx_credit cred = {};

	m0_be_allocator_credit(a, optype, size, shift, &cred);
	M0_LOG(M0_INFO,
	       "m0_be_allocator_credit(): "
	       "optype = %d (%s), size = %" PRIi64 ", shift = %d, "
	       "credit = "BETXCR_F,
	       optype, optype_str, size, shift, BETXCR_P(&cred));
}

M0_INTERNAL void m0_be_ut_alloc_info(void)
{
	struct m0_be_allocator *a;
	struct m0_be_ut_seg     ut_seg;
	m0_bcount_t             size;
	unsigned                shift;

	m0_be_ut_backend_init(&be_ut_alloc_backend);
	m0_be_ut_seg_init(&ut_seg, &be_ut_alloc_backend, BE_UT_ALLOC_SEG_SIZE);
	m0_be_ut_seg_allocator_init(&ut_seg, &be_ut_alloc_backend);
	a = m0_be_seg_allocator(ut_seg.bus_seg);

	be_ut_alloc_credit_log(a, M0_BAO_CREATE,       "create", 0, 0);
	be_ut_alloc_credit_log(a, M0_BAO_DESTROY,      "destroy", 0, 0);
	be_ut_alloc_credit_log(a, M0_BAO_FREE,         "free", 0, 0);
	be_ut_alloc_credit_log(a, M0_BAO_FREE_ALIGNED, "free_aligned", 0, 0);

	for (size = 1; size <= 0x1000; size *= 4)
		be_ut_alloc_credit_log(a, M0_BAO_ALLOC, "alloc", size, 0);
	for (shift = 0; shift <= 12; shift += 1) {
		be_ut_alloc_credit_log(a, M0_BAO_ALLOC_ALIGNED, "alloc_aligned",
				       0x100, shift);
	}

	m0_be_ut_seg_allocator_fini(&ut_seg, &be_ut_alloc_backend);
	m0_be_ut_seg_fini(&ut_seg);
	m0_be_ut_backend_fini(&be_ut_alloc_backend);
	M0_SET0(&be_ut_alloc_backend);
}

/* segment and memory allocation sizes to test */
enum {
	BE_UT_OOM_SEG_START     = 0x1900,
	BE_UT_OOM_SEG_STEP      = 0x42,
	BE_UT_OOM_SEG_STEP_NR   = 0x4,
	BE_UT_OOM_ALLOC_START   = 0x1,
	BE_UT_OOM_ALLOC_STEP    = 0x1,
	BE_UT_OOM_ALLOC_STEP_NR = 0x4,
};

static void be_ut_alloc_oom_case(struct m0_be_allocator *a,
				 m0_bcount_t             alloc_size)
{
	uint64_t   ptrs_nr_max = a->ba_seg->bs_size / alloc_size + 1;
	uint64_t   ptrs_nr     = 0;
	uint64_t   i;
	void     **ptrs;

	M0_ALLOC_ARR(ptrs, ptrs_nr_max);
	M0_UT_ASSERT(ptrs != NULL);

	while (true) {
		M0_UT_ASSERT(ptrs_nr < ptrs_nr_max);
		M0_BE_UT_TRANSACT(&be_ut_alloc_backend, tx, cred,
		  m0_be_allocator_credit(a, M0_BAO_ALLOC, alloc_size, 0, &cred),
		  M0_BE_OP_SYNC(op, m0_be_alloc(a, tx, &op,
						&ptrs[ptrs_nr], alloc_size)));
		if (ptrs[ptrs_nr] == NULL)
			break;

		++ptrs_nr;
	}

	M0_UT_ASSERT(ptrs_nr > 1);

	for (i = 0; i < ptrs_nr; ++i) {
		M0_BE_UT_TRANSACT(&be_ut_alloc_backend, tx, cred,
			  m0_be_allocator_credit(a, M0_BAO_FREE, 0, 0, &cred),
			  M0_BE_OP_SYNC(op, m0_be_free(a, tx, &op, ptrs[i])));
	}

	m0_free(ptrs);
}

M0_INTERNAL void m0_be_ut_alloc_oom(void)
{
	struct m0_be_allocator *a;
	struct m0_be_ut_seg     ut_seg;
	int                     seg_size_start;
	int                     seg_step;
	int                     alloc_step;

	m0_be_ut_backend_init(&be_ut_alloc_backend);

	m0_be_ut_seg_init(&ut_seg, &be_ut_alloc_backend, 0x10000);
	seg_size_start = m0_be_seg_reserved(ut_seg.bus_seg) +
			 BE_UT_OOM_SEG_START;
	m0_be_ut_seg_fini(&ut_seg);

	for (seg_step = 0; seg_step < BE_UT_OOM_SEG_STEP_NR; ++seg_step) {
		m0_be_ut_seg_init(&ut_seg, &be_ut_alloc_backend,
				  m0_round_up(seg_size_start +
					      seg_step * BE_UT_OOM_SEG_STEP,
					      m0_pagesize_get()));
		m0_be_ut_seg_allocator_init(&ut_seg, &be_ut_alloc_backend);
		a = m0_be_seg_allocator(ut_seg.bus_seg);

		for (alloc_step = 0; alloc_step < BE_UT_OOM_ALLOC_STEP_NR;
		     ++alloc_step) {
			be_ut_alloc_oom_case(a, BE_UT_OOM_ALLOC_START +
					     alloc_step * BE_UT_OOM_ALLOC_STEP);
		}
		m0_be_ut_seg_allocator_fini(&ut_seg, &be_ut_alloc_backend);
		m0_be_ut_seg_fini(&ut_seg);
	}
	m0_be_ut_backend_fini(&be_ut_alloc_backend);
	M0_SET0(&be_ut_alloc_backend);
}

M0_INTERNAL void m0_be_ut_alloc_spare(void)
{
	struct {
		bool     do_free;
		uint64_t zonemask;
		bool     should_fail;
		int      fi;
	} scenario[] = {
		{ false, M0_BITS(M0_BAP_NORMAL), false, 0 },
		{ false, M0_BITS(M0_BAP_NORMAL), true , 0 },
		{ true,  M0_BITS(M0_BAP_NORMAL), false, 0 },
		{ false, M0_BITS(M0_BAP_NORMAL), false, 0 },
		{ false, M0_BITS(M0_BAP_REPAIR), false, 0 },
		{ false, M0_BITS(M0_BAP_NORMAL), true,  0 },
		{ true,  M0_BITS(M0_BAP_NORMAL), false, 3 },
		{ true,  M0_BITS(M0_BAP_REPAIR), false, 4 }
	};
	struct m0_be_ut_backend        ut_be = {};
	struct m0_be_ut_seg            ut_seg;
	struct m0_be_allocator        *a;
	m0_bcount_t                    size;
	void                          *ptrs[ARRAY_SIZE(scenario)] = {};
	struct m0_be_allocator_stats   stats_before = {};
	struct m0_be_allocator_stats   stats_after = {};
	int                            i;

	M0_ENTRY();

	m0_be_ut_backend_init(&ut_be);

	/* Reserve 50% for M0_BAP_REPAIR zone. */
	m0_fi_enable_once("be_ut_seg_allocator_initfini", "repair_zone_50");
	m0_be_ut_seg_init(&ut_seg, &ut_be, BE_UT_ALLOC_SEG_SIZE);
	m0_be_ut_seg_allocator_init(&ut_seg, &ut_be);
	a = m0_be_seg_allocator(ut_seg.bus_seg);
	M0_UT_ASSERT(a != NULL);

	size = (BE_UT_ALLOC_SEG_SIZE - m0_be_seg_reserved(a->ba_seg)) / 3;

	for (i = 0 ; i < ARRAY_SIZE(scenario) ; ++i) {
		m0_be_alloc_stats(a, &stats_before);

		if (scenario[i].do_free) {
			M0_LOG(M0_INFO,
			       "ut_alloc_spare #%d do free ptrs[%d] %p",
			       i, scenario[i].fi, ptrs[scenario[i].fi]);

			M0_BE_UT_TRANSACT(&ut_be, tx, cred,
			  m0_be_allocator_credit(a, M0_BAO_FREE, 0, 0, &cred),
			  M0_BE_OP_SYNC(op, m0_be_free(a, tx, &op,
						       ptrs[scenario[i].fi])));
		} else {
			M0_BE_UT_TRANSACT(&ut_be, tx, cred,
			  (m0_be_allocator_credit(a, M0_BAO_ALLOC_ALIGNED,
						  size, BE_UT_ALLOC_SHIFT,
						  &cred),
					   m0_be_alloc_stats_credit(a, &cred)),
					  (M0_BE_OP_SYNC(op,
						 m0_be_alloc_aligned(a, tx, &op,
						     &ptrs[i], size,
						     BE_UT_ALLOC_SHIFT,
						     scenario[i].zonemask,
						     false)),
					   m0_be_alloc_stats_capture(a, tx)));
			M0_UT_ASSERT(
				(ptrs[i] == NULL) == scenario[i].should_fail);
		}
		m0_be_alloc_stats(a, &stats_after);

		M0_UT_ASSERT(ergo(scenario[i].zonemask & M0_BITS(M0_BAP_REPAIR),
			(stats_before.bas_space_used == stats_after.bas_space_used) &&
			(stats_before.bas_space_free == stats_after.bas_space_free)));
	}

	m0_be_ut_backend_fini(&ut_be);
	M0_SET0(&ut_be);
	M0_LOG(M0_INFO, "m0_be_ut_alloc_spare OK");

	M0_LEAVE();
}

M0_INTERNAL void m0_be_ut_alloc_align(void)
{
	/**
	 * In this UT, we are testing the functionality of m0_be_alloc_aligned()
	 * when chunk_align parameter is set to true.
	 *
	 * 1. Allocate multiple chunks with chunk_align set to true.
	 * 2. Verify the alignment of all the allocated chunks.
	 * 3. Delete some of the allocated chunks.
	 * 4. Verify the alignment of the remaining chunks.
	 * 5. Delete remaining of the allocated chunks.
	 */
	struct m0_be_ut_backend *ut_be    = &be_ut_alloc_backend;
	struct m0_be_ut_seg     *ut_seg   = &be_ut_alloc_seg;
	struct m0_be_allocator  *a;
	void                    *ut_ptr[BE_UT_ALLOC_PTR_NR];
	int                      ut_nr    = BE_UT_ALLOC_PTR_NR;
	uint64_t                 j;
	int                      i;
	int                      ut_shift = BE_UT_ALLOC_SHIFT - 1;
	int                      ut_size;
	bool                     ut_tval;
	int                      chunk_header_size = m0_be_chunk_header_size();
	char                    *iptr;

	m0_be_ut_backend_init(ut_be);
	m0_be_ut_seg_init(ut_seg, ut_be, BE_UT_ALLOC_SEG_SIZE);
	m0_be_ut_seg_allocator_init(ut_seg, ut_be);

	a = m0_be_seg_allocator(ut_seg->bus_seg);
	M0_UT_ASSERT(a != NULL);
	M0_SET_ARR0(ut_ptr);

	m0_mutex_lock(&a->ba_lock);
	M0_UT_ASSERT(m0_be_allocator__invariant(a));
	m0_mutex_unlock(&a->ba_lock);

	/* Alloc chunks with chunk_align parameter set as true */
	for (i = 0; i < ut_nr; i++) {
		j = i;
		ut_size = m0_rnd64(&j) % BE_UT_ALLOC_SIZE + 1;

		M0_BE_UT_TRANSACT(ut_be, tx, cred,
			  (m0_be_allocator_credit(a, M0_BAO_ALLOC_ALIGNED,
						  ut_size, ut_shift, &cred),
			   m0_be_alloc_stats_credit(a, &cred)),
			  (M0_BE_OP_SYNC(op,
				 m0_be_alloc_aligned(a, tx, &op, &ut_ptr[i],
						     ut_size, ut_shift,
						     M0_BITS(M0_BAP_NORMAL),
						     true)),
			   m0_be_alloc_stats_capture(a, tx)));
		M0_UT_ASSERT(ut_ptr[i] != NULL);
	}
	m0_mutex_lock(&a->ba_lock);
	M0_UT_ASSERT(m0_be_allocator__invariant(a));
	m0_mutex_unlock(&a->ba_lock);

	/* Verify the alignment of the chunks */
	for (i = 0; i < ut_nr; i++) {
		iptr = (char *)ut_ptr[i];
		iptr = iptr - chunk_header_size;
		M0_UT_ASSERT(m0_addr_is_aligned(iptr, ut_shift));
	}

	/* Delete the even numbered chunks */
	for (i = 0; i < ut_nr; i += 2) {
		j = i;
		ut_size = m0_rnd64(&j) % BE_UT_ALLOC_SIZE + 1;

		M0_BE_UT_TRANSACT(ut_be, tx, cred,
			  (m0_be_allocator_credit(a, M0_BAO_FREE_ALIGNED,
						  ut_size, ut_shift, &cred),
			   m0_be_alloc_stats_credit(a, &cred)),
			  (M0_BE_OP_SYNC(op,
					 m0_be_free_aligned(a, tx, &op,
							    ut_ptr[i], false)),
			   m0_be_alloc_stats_capture(a, tx)));
		ut_ptr[i] = NULL;
	}
	m0_mutex_lock(&a->ba_lock);
	M0_UT_ASSERT(m0_be_allocator__invariant(a));
	m0_mutex_unlock(&a->ba_lock);

	/* Verify the alignment of the remaining chunks */
	for (i = 1; i < ut_nr; i += 2) {
		if (ut_ptr[i] != NULL) {
			iptr = (char *)ut_ptr[i];
			iptr = iptr - chunk_header_size;
			M0_UT_ASSERT(m0_addr_is_aligned(iptr, ut_shift));
		}
	}

	/* Delete remaining chunks */
	for (i = 1; i < ut_nr; i += 2) {
		if (ut_ptr[i] != NULL) {
			j = i;
			ut_size = m0_rnd64(&j) % BE_UT_ALLOC_SIZE + 1;

			M0_BE_UT_TRANSACT(ut_be, tx, cred,
				(m0_be_allocator_credit(a, M0_BAO_FREE_ALIGNED,
							ut_size, ut_shift,
							&cred),
				 m0_be_alloc_stats_credit(a, &cred)),
				(M0_BE_OP_SYNC(op,
					       m0_be_free_aligned(a, tx, &op,
								  ut_ptr[i],
								  false)),
				 m0_be_alloc_stats_capture(a, tx)));
			ut_ptr[i] = NULL;
		}
	}
	m0_mutex_lock(&a->ba_lock);
	M0_UT_ASSERT(m0_be_allocator__invariant(a));
	m0_mutex_unlock(&a->ba_lock);

	/**
	 * 1. Allocate multiple chunks with some having chunk_align set to true
	 *    and the remaining having chunk_align as false.
	 * 2. Verify the alignment of all the allocated chunks.
	 * 3. Delete some of the allocated chunks.
	 * 4. Verify the alignment of the remaining chunks.
	 * 5. Delete remaining of the allocated chunks.
	 */

	M0_SET_ARR0(ut_ptr);

	/**
	 *  Alloc half memory with chunk_align parameter set as true and
	 *  remaining with chunk_align set as false.
	 */
	for (i = 0; i < ut_nr; i++) {
		j = i;
		ut_size  = m0_rnd64(&j) % BE_UT_ALLOC_SIZE + 1;
		ut_tval  = i % 2 == 0 ? true : false;
		ut_shift = i % 2 == 0 ? BE_UT_ALLOC_SHIFT - 1 :
					BE_UT_ALLOC_SHIFT;

		M0_BE_UT_TRANSACT(ut_be, tx, cred,
			  (m0_be_allocator_credit(a, M0_BAO_ALLOC_ALIGNED,
						  ut_size, ut_shift, &cred),
			   m0_be_alloc_stats_credit(a, &cred)),
			  (M0_BE_OP_SYNC(op,
					 m0_be_alloc_aligned(a, tx, &op,
						     &ut_ptr[i],
						     ut_size, ut_shift,
						     M0_BITS(M0_BAP_NORMAL),
						     ut_tval)),
			   m0_be_alloc_stats_capture(a, tx)));
		M0_UT_ASSERT(ut_ptr[i] != NULL);
	}
	m0_mutex_lock(&a->ba_lock);
	M0_UT_ASSERT(m0_be_allocator__invariant(a));
	m0_mutex_unlock(&a->ba_lock);

	/* Verify the alignment of the chunks */
	for (i = 0; i < ut_nr; i++) {
		if (i % 2 == 0) {
			iptr = (char *)ut_ptr[i];
			iptr = iptr - chunk_header_size;
			M0_UT_ASSERT(m0_addr_is_aligned(iptr,
							BE_UT_ALLOC_SHIFT - 1));
		} else
			M0_UT_ASSERT(
			m0_addr_is_aligned(ut_ptr[i], BE_UT_ALLOC_SHIFT));
	}

	/**
	 *  Delete every third chunk to make sure that both type of chunks are
	 *  deleted.
	 */
	for (i = 0; i < ut_nr; i += 3) {
		j = i;
		ut_size  = m0_rnd64(&j) % BE_UT_ALLOC_SIZE + 1;
		ut_shift = i % 2 == 0 ? BE_UT_ALLOC_SHIFT - 1 :
					BE_UT_ALLOC_SHIFT;
		M0_BE_UT_TRANSACT(ut_be, tx, cred,
			  (m0_be_allocator_credit(a, M0_BAO_FREE_ALIGNED,
						  ut_size, ut_shift, &cred),
			   m0_be_alloc_stats_credit(a, &cred)),
			  (M0_BE_OP_SYNC(op,
					 m0_be_free_aligned(a, tx, &op,
							    ut_ptr[i], false)),
			   m0_be_alloc_stats_capture(a, tx)));
		ut_ptr[i] = NULL;
	}
	m0_mutex_lock(&a->ba_lock);
	M0_UT_ASSERT(m0_be_allocator__invariant(a));
	m0_mutex_unlock(&a->ba_lock);

	/* Verify the alignment of the remaining chunks */
	for (i = 0; i < ut_nr; i++) {
		if (i % 3  == 0)
			continue;
		if (ut_ptr[i] != NULL) {
			if (i % 2 == 0) {
				iptr = (char *)ut_ptr[i];
				iptr = iptr - chunk_header_size;
				M0_UT_ASSERT(m0_addr_is_aligned(iptr,
							BE_UT_ALLOC_SHIFT - 1));
			} else
				M0_UT_ASSERT(m0_addr_is_aligned(ut_ptr[i],
							    BE_UT_ALLOC_SHIFT));
		}
	}

	/* Delete remaining chunks */
	for (i = 0; i < ut_nr; i++) {
		if (i % 3  == 0)
			continue;
		if (ut_ptr[i] != NULL) {
			j = i;
			ut_size  = m0_rnd64(&j) % BE_UT_ALLOC_SIZE + 1;
			ut_shift = i % 2 == 0 ? BE_UT_ALLOC_SHIFT - 1 :
						BE_UT_ALLOC_SHIFT;
			M0_BE_UT_TRANSACT(ut_be, tx, cred,
				(m0_be_allocator_credit(a, M0_BAO_FREE_ALIGNED,
							ut_size, ut_shift,
							&cred),
				 m0_be_alloc_stats_credit(a, &cred)),
				(M0_BE_OP_SYNC(op,
					       m0_be_free_aligned(a, tx, &op,
								  ut_ptr[i],
								  false)),
				 m0_be_alloc_stats_capture(a, tx)));
			ut_ptr[i] = NULL;
		}
	}

	m0_mutex_lock(&a->ba_lock);
	M0_UT_ASSERT(m0_be_allocator__invariant(a));
	m0_mutex_unlock(&a->ba_lock);
	m0_be_ut_seg_allocator_fini(ut_seg, ut_be);
	m0_be_ut_seg_fini(ut_seg);
	m0_be_ut_backend_fini(ut_be);

	M0_SET0(ut_be);
}

M0_INTERNAL void m0_be_ut_alloc_unmap(void)
{
	struct m0_be_ut_backend *ut_be  = &be_ut_alloc_backend;
	struct m0_be_ut_seg     *ut_seg = &be_ut_alloc_seg;
	struct m0_be_allocator  *a;
	int                      rc;
	int                      i = 0;
	int                      j;
	int                      k;
	void                    *p = NULL;
	struct m0_be_tx          tx;
	struct m0_be_tx_credit   cred = {};
	uint32_t                 test_page_count;
	const uint32_t           page_size = m0_pagesize_get();
	const unsigned           shift = m0_pageshift_get() - 1;
	struct {
		uint16_t         page_count[5];
			}        spaces_cfg[] = {
						{.page_count = {1, 1, 1, 1, 1}},
						{.page_count = {2, 2, 2, 2, 2}},
						{.page_count = {3, 3, 3, 3, 3}},
						{.page_count = {1, 1, 2, 2, 2}},
						{.page_count = {2, 1, 2, 1, 2}},
						{.page_count = {2, 2, 1, 2, 2}}
					    };
	void                    *spaces[ARRAY_SIZE(spaces_cfg[0].page_count)];
	uint64_t                 space_to_alloc;
	unsigned char           *expected_page_load_map;
	unsigned char           *actual_page_load_map;

	m0_be_ut_backend_init(ut_be);
	m0_be_ut_seg_init(ut_seg, ut_be, BE_UT_ALLOC_SEG_SIZE);
	m0_be_ut_seg_allocator_init(ut_seg, ut_be);

	a = m0_be_seg_allocator(be_ut_alloc_seg.bus_seg);
	M0_UT_ASSERT(a != NULL);

	/**
	 * Following tests are covered:
	 * 1)  Memory is NOT unmapped when UNMAP flag is NOT SET.
	 * 2)  Memory is unmapped when UNMAP flag is SET. Also the unmapping
	 *     skips the 1st CPU page which contains the chunk header.
	 * 3)  If the previous chunk has already been freed and unmapped, then
	 *     freeing and unmapping the current chunk will cause a merge and
	 *     the complete chunk is unmapped (including the chunk header space
	 *     which contained the chunk header)
	 * 4)  If the next chunk has already been freed and unmapped (except the
	 *     chunk header page of the next chunk) then after unmapping of the
	 *     current chunk is done the page containing the chunk header of the
	 *     next chunk is also unmapped.
	 * 5)  If the previous and next chunks have been freed and unmapped and
	 *     unmapping the current chunk will unmap the current chunk and next
	 *     chunk completely (including the chunk header of these two
	 *     chunks), only the chunk header of the previous chunk will remain
	 *     mapped.
	 * 6)  Test above scenarios with a smaller chunk which sits the chunk
	 *     header and the allocated space within one CPU page.
	 */
	/**
	 * In first test we:
	 * 1)  Allocate 5 chunk-aligned spaces of same size from BE segmentm and
	 *     fill them so that all the page_count are loaded in memory.
	 * 2)  Free 3rd space with UNMAP flag NOT-SET and confirm the space is
	 *     NOT unmapped after the free.
	 * 3)  Allocate space of same size as before so that we get the same 3rd
	 *     space which we had released earlier.
	 * 4)  Free 3rd space with UNMAP flag SET and confirm the space is not
	 *     mapped only for the freed space. The first PAGE of this space
	 *     will still stay mapped as it contains the chunk header which the
	 *     free routine will not unmap.
	 * 5)  Allocate space of same size as before so that we get the same 3rd
	 *     space which we had released above. Fill the space with random
	 *     data so that the page_count are loaded in memory by the OS.
	 * 6)  Free 2nd space with UNMAP flag NOT-SET and confirm this space is
	 *     still mapped after the free.
	 * 7)  Free 3rd space with UNMAP flag SET and confirm that only this
	 *     space (minus 1st page containing chunk header) is unmapped. The
	 *     2nd space should still be mapped.
	 * 8)  Allocate 2nd space and 3rd space and fill them with data to load
	 *     the page_count in memory.
	 * 9)  Free 2nd space with UNMAP flag set and confirm that only this
	 *     space (minus 1st page) is unmapped.
	 * 10) Free 3rd space with UNMAP flag set and confirm that complete area
	 *     of 3rd space is unmapped (including the 1st page containing the
	 *     chunk header). Also confirm that the 2nd space is still unmapped
	 *     the same way as in above step.
	 * 11) Allocate 2nd and 3rd spaces and fill them with data to load the
	 *     page_count in memory.
	 * 12) Free 4th space with UNMAP flag set and confirm that only this
	 *     space (minus the 1st page of this space) is unmapped.
	 * 13) Free 3rd space with UNMAP flag set and confirm that this space
	 *     without the 1st page of this space is unmapped. Also the 1st page
	 *     of the 4th space should now have been unmapped.
	 * 14) Free all the five allocated spaces.
	 */

	for (i = 0; i < ARRAY_SIZE(spaces_cfg); i++) {
		cred = M0_BE_TX_CB_CREDIT(0, 0, 0);
		test_page_count = 0;

		for (j = 0; j < ARRAY_SIZE(spaces_cfg[i].page_count); j++)
			test_page_count += spaces_cfg[i].page_count[j];

		expected_page_load_map = m0_alloc(test_page_count);
		actual_page_load_map = m0_alloc(test_page_count);

		/**
		 *  Account for all the credits needed while running this test
		 *  iteration. Instead of getting accurate credit numbers we ask
		 *  for a large number hoping we never exceed this one.
		 */
		for (j = 0; j < 20; j++) {
			m0_be_allocator_credit(a, M0_BAO_ALLOC_ALIGNED,
					       test_page_count * page_size,
					       shift, &cred);

			m0_be_allocator_credit(a, M0_BAO_FREE,
					       test_page_count * page_size,
					       shift, &cred);
		}

		m0_be_ut_tx_init(&tx, ut_be);
		m0_be_tx_prep(&tx, &cred);
		rc = m0_be_tx_open_sync(&tx);
		M0_ASSERT(rc == 0);

		/**
		 * Allocate the spaces to use and load them in memory by
		 * attempting to write a few bytes in every page.
		 */
		for (j = 0; j < ARRAY_SIZE(spaces); j++) {
			space_to_alloc = spaces_cfg[i].page_count[j] *
					 page_size;
			space_to_alloc -= sizeof(struct be_alloc_chunk);
			M0_BE_OP_SYNC(op,
				      m0_be_alloc_aligned(a, &tx, &op,
							  &(spaces[j]),
							  space_to_alloc, shift,
							  M0_BITS(M0_BAP_NORMAL),
							  true)
				      );
			M0_ASSERT(spaces[j] != NULL);

			/**
			 *  Confirm this allocated space follows the end
			 *  address of the prev allocation
			 */
			M0_ASSERT(ergo(j != 0,
				       spaces[j - 1] +
				       spaces_cfg[i].page_count[j - 1] *
				       page_size == spaces[j]));

			p = spaces[j];
			for (k = 0; k < spaces_cfg[i].page_count[j]; k++) {
				*(uint64_t *)p = 0;
				p += page_size;
			}
		}

		/* Assume all the pages are loaded in memory */
		for (j = 0; j < test_page_count; j++)
			expected_page_load_map[j] = 1;

		/* Verify if kernel agrees */
		rc = mincore(spaces[0] - sizeof(struct be_alloc_chunk),
			     test_page_count * page_size, actual_page_load_map);
		M0_ASSERT(rc == 0);

		M0_ASSERT(memcmp(actual_page_load_map, expected_page_load_map,
				 test_page_count) == 0);



		/* Release all the allocated resource for this test iteration */
		for (j = 0; j < ARRAY_SIZE(spaces); j++) {
			M0_BE_OP_SYNC(op, m0_be_free_aligned(a, &tx, &op, spaces[j], false));
		}

		/* Assume ONLY the first page is loaded in memory */
		expected_page_load_map[0] = 1;
		for (j = 1; j < test_page_count; j++)
			expected_page_load_map[j] = 0;

		/** TBD - Remove the next block before checkin */
		{
			void *addr = spaces[0] - sizeof(struct be_alloc_chunk) +
				     page_size;
			uint64_t size = (test_page_count - 1) * page_size;
			m0_bcount_t file_offset = (m0_bcount_t)(addr - ut_seg->bus_seg->bs_addr);

			munmap(addr, size);
			rc = madvise(addr, size, MADV_NORMAL);
			M0_ASSERT(rc == -1 && errno == ENOMEM); /** Assert BE segment unmapped*/

			p = mmap(addr, size, PROT_READ | PROT_WRITE,
				 MAP_FIXED | MAP_PRIVATE | MAP_NORESERVE,
				 m0_stob_fd(ut_seg->bus_seg->bs_stob), file_offset);
			rc = madvise(addr, size, MADV_NORMAL);
			M0_ASSERT(rc == 0);
		}

		rc = mincore(spaces[0] - sizeof(struct be_alloc_chunk),
			     test_page_count * page_size, actual_page_load_map);
		M0_ASSERT(rc == 0);

		M0_ASSERT(memcmp(actual_page_load_map, expected_page_load_map,
				 test_page_count) == 0);

		m0_be_tx_close_sync(&tx);
		m0_be_tx_fini(&tx);
	}

	m0_be_ut_seg_allocator_fini(ut_seg, ut_be);
	m0_be_ut_seg_fini(ut_seg);
	m0_be_ut_backend_fini(ut_be);
	M0_SET0(ut_be);
}

#undef M0_TRACE_SUBSYSTEM

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
