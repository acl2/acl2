; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "common-system-level-utils")
(include-book "paging/common-paging-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection non-marking-view-proof-utilities
  :parents (proof-utilities debugging-code-proofs)

  :short "General-purpose code-proof libraries to include in the
  system-level non-marking view (with A/D flag updates off)"

  :long "<p>When reasoning about an supervisor-mode program in the
  system-level <i>non-marking</i> view of the x86 ISA model, include
  the book @('x86isa/proofs/utilities/sys-view/non-marking-view-top')
  to make use of some standard rules you would need to control the
  symbolic simulation of the program.</p>

  <p>If unwinding the @('(x86-run ... x86)') expression during your
  proof attempt does not result in a 'clean' expression (i.e., one
  entirely in terms of updates made to the initial state as opposed to
  in terms of @(see x86-fetch-decode-execute) or @(see x86-run)), then
  there is a good chance that you're missing some preconditions, or
  that the existing rules are not good enough.  In any case, it can
  help to @(see acl2::monitor) the existing rules to figure out what's
  wrong.  Feel free to send on suggestions for new rules or improving
  existing ones!</p>

  <p>You can monitor the following rules, depending on the kind of
  subgoals you see, to get some clues.  You can find definitions of
  these rules in @(see unwind-x86-interpreter-in-non-marking-view).</p>

  <ul>

    <li>When the subgoal has calls of @('x86-run'): <br/>
        Monitor @('x86-run-opener-not-ms-not-zp-n').
   </li>

    <li>When the subgoal has calls of @(see x86-fetch-decode-execute): <br/>
        Monitor @('x86-fetch-decode-execute-opener').
   </li>

   <li>When monitoring @('x86-fetch-decode-execute-opener') tells you
    that a hypothesis involving @(see get-prefixes) was not rewritten
    to @('t'): <br/>
    Monitor
    @('get-prefixes-opener-lemma-no-prefix-byte') or
    @('get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix'). <br/>
    Note that if the instruction under consideration has prefix
    bytes, you should monitor one of these rules instead: <br/>
    @('get-prefixes-opener-lemma-group-1-prefix') <br/>
    @('get-prefixes-opener-lemma-group-2-prefix') <br/>
    @('get-prefixes-opener-lemma-group-3-prefix') <br/>
    @('get-prefixes-opener-lemma-group-4-prefix').
  </li>

    <li>When monitoring other rules above indicates that an
    instruction is not being fetched successfully using @(see rb):
    <br/>
    Monitor @('one-read-with-rb-from-program-at-in-non-marking-view').
    </li>

   <li>When monitoring other rules above indicates that ACL2 can't
    resolve that the program remained unchanged (@(see
    program-at)) after a write operation @(see wb) occurred: <br/>
    Monitor @('program-at-wb-disjoint-in-non-marking-view'). <br/>
    <br/>
    An instance of where monitoring this rule might be helpful is when
    the @('program-at') hypothesis of
    @('one-read-with-rb-from-program-at-in-non-marking-view') is not
    being relieved.
   </li>

   <li>When inferring the canonical nature of a linear address:<br/>
    Monitor @('member-p-canonical-address-listp'). <br/>
    <br/>
    This is useful if you believe that the canonical nature of a
    linear address should be inferable from the canonical nature of a
    list of addresses, of which that address is a member.  An instance
    of where monitoring this rule
    might be helpful is when the @('member-p') hypothesis of
    @('one-read-with-rb-from-program-at-in-non-marking-view') is not
    being relieved.
   </li>

   <li>When reasoning about disjointness/overlap of memory regions: <br/>
   @('rb-wb-disjoint-in-non-marking-view') <br/>
   @('rb-wb-equal-in-non-marking-view') <br/>
   @('la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view') <br/>
   @('all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-in-non-marking-view')
   </li>

 </ul>

 <p>When symbolically simulating supervisor-mode programs, you might
 also want to do the following, which replaces ACL2's default ancestor
 check with something simpler:</p>

 <code>
 (local (include-book \"tools/trivial-ancestors-check\" :dir :system))
 (local (acl2::use-trivial-ancestors-check))
 </code>

")

(defsection unwind-x86-interpreter-in-non-marking-view
  :parents (non-marking-view-proof-utilities)

  ;; A benefit of defining this topic (apart from letting the user
  ;; view the definitions of the rules) is that if the rule names
  ;; mentioned in the parent topic are changed, the manual build
  ;; process will complain about broken links, and we'll know to
  ;; modify these two doc topics.

  :short "Definitions of rules to monitor in the system-level
  non-marking view"

  :long "

 <h3>Rules about @('x86-run') and @('x86-fetch-decode-execute')</h3>

 @(def x86-run-opener-not-ms-not-zp-n)

 @(def x86-fetch-decode-execute-opener)

 <h3>Rules about @('get-prefixes')</h3>

 @(def get-prefixes-opener-lemma-no-prefix-byte)

 @(def get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix)

 @(def get-prefixes-opener-lemma-group-1-prefix)

 @(def get-prefixes-opener-lemma-group-2-prefix)

 @(def get-prefixes-opener-lemma-group-3-prefix)

 @(def get-prefixes-opener-lemma-group-4-prefix)

 <h3>Rules related to instruction fetches and program location</h3>

 @(def one-read-with-rb-from-program-at-in-non-marking-view)

 @(def program-at-wb-disjoint-in-non-marking-view)

 <h3>Rules related to canonical linear addresses</h3>

 @(def member-p-canonical-address-listp)

 <h3>Rules related to disjointness/overlap of memory regions</h3>

  @(def rb-wb-disjoint-in-non-marking-view)
  @(def rb-wb-equal-in-non-marking-view)
  @(def la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view)
  @(def all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-in-non-marking-view)
")

(local (xdoc::set-default-parents non-marking-view-proof-utilities))

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix)
;; (acl2::why ia32e-la-to-pa-values-and-mv-nth-1-wb)
;; (acl2::why one-read-with-rb-from-program-at-in-non-marking-view)
;; (acl2::why combine-bytes-many-reads-with-rb-from-program-at-in-non-marking-view)
;; (acl2::why program-at-wb-disjoint-in-non-marking-view)
;; (acl2::why rb-wb-disjoint-in-non-marking-view)
;; (acl2::why disjointness-of-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view)

;; ======================================================================

;; Lemmas about memory writes:

(defthm xr-mem-wb-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n lin-addr :w x86)))
                (disjoint-p (list index)
                            (mv-nth 1 (las-to-pas n lin-addr :w x86)))
                (not (marking-view x86))
                (not (app-view x86)))
           (equal (xr :mem index (mv-nth 1 (wb n lin-addr w value x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (wb write-to-physical-memory disjoint-p member-p)
                                   ((:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

(defthm mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-view
  (implies (and (bind-free (find-l-addrs-from-las-to-pas '(n addr) r-w-x mfc state)
                           (n addr))
                ;; <1,a> is a subset of <n,addr>.
                (<= addr a)
                (< a (+ n addr))
                (not (mv-nth 0 (las-to-pas n addr r-w-x x86)))
                (not (marking-view x86))
                (posp n) (integerp a))
           (equal (mv-nth 0 (ia32e-la-to-pa a r-w-x x86)) nil)))

(defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-view
  (implies (and
            ;; <1,a> is a subset of <n,addr>.
            (<= addr a)
            (< a (+ n addr))
            (not (mv-nth 0 (las-to-pas n addr r-w-x x86)))
            (not (marking-view x86))
            (posp n) (integerp a))
           (member-p (mv-nth 1 (ia32e-la-to-pa a r-w-x x86))
                     (mv-nth 1 (las-to-pas n addr r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm mv-nth-1-ia32e-la-to-pa-not-member-of-mv-nth-1-las-to-pas
  (implies (and (bind-free (find-l-addrs-from-las-to-pas '(n-1 addr-1) r-w-x-1 mfc state)
                           (n-1 addr-1))
                (disjoint-p (mv-nth 1 (las-to-pas n-1 addr-1 r-w-x-1 x86))
                            (mv-nth 1 (las-to-pas n-2 addr-2 r-w-x-2 x86)))
                ;; <1,a> is a subset of <n-1,addr-1>.
                (<= addr-1 a) (< a (+ n-1 addr-1))
                (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x-1 x86)))
                (not (marking-view x86))
                (posp n-1) (integerp a))
           (equal (member-p (mv-nth 1 (ia32e-la-to-pa a r-w-x-1 x86))
                            (mv-nth 1 (las-to-pas n-2 addr-2 r-w-x-2 x86)))
                  nil))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (e/d* (disjoint-p member-p)
          (mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-view))
    :use ((:instance mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-view
                     (n n-1) (addr addr-1) (r-w-x r-w-x-1) (a a))))))

(defthm las-to-pas-values-and-xw-mem-not-member-in-non-marking-view
  (implies (and (not (member-p index (all-xlation-governing-entries-paddrs n lin-addr x86)))
                (not (marking-view x86)))
           (and (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x (xw :mem index byte x86)))
                       (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x (xw :mem index byte x86)))
                       (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))))
  :hints (("Goal"
           :in-theory (e/d* (disjoint-p member-p)
                            (xlation-governing-entries-paddrs)))))

;; ======================================================================

;; Lemmas about interaction of writes and paging walkers:

(defthm rm-low-32-wb-in-non-marking-view-disjoint
  (implies (and (not (mv-nth 0 (las-to-pas n addr :w x86)))
                (disjoint-p (addr-range 4 index)
                            (mv-nth 1 (las-to-pas n addr :w x86)))
                (not (marking-view x86)))
           (equal (rm-low-32 index (mv-nth 1 (wb n addr w value x86)))
                  (rm-low-32 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32 disjoint-p member-p)
                                   (write-to-physical-memory
                                    (:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

(defthm rm-low-64-wb-in-non-marking-view-disjoint
  (implies (and (not (mv-nth 0 (las-to-pas n addr :w x86)))
                (disjoint-p (addr-range 8 index)
                            (mv-nth 1 (las-to-pas n addr :w x86)))
                (not (marking-view x86))
                (integerp index))
           (equal (rm-low-64 index (mv-nth 1 (wb n addr w value x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                            (wb (:meta acl2::mv-nth-cons-meta)
                                force (force))))))

(defthm las-to-pas-values-in-non-marking-view-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p (all-xlation-governing-entries-paddrs n lin-addr x86) p-addrs)
                (physical-address-listp p-addrs)
                (not (marking-view x86)))
           (and (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))))
  :hints (("Goal" :induct (las-to-pas n lin-addr r-w-x x86)
           :in-theory (e/d* (disjoint-p disjoint-p-commutative) (xlation-governing-entries-paddrs)))))

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (marking-view x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table
                             xlation-governing-entries-paddrs-for-page-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (marking-view x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory
                             xlation-governing-entries-paddrs-for-page-directory)
                            (wb
                             xlation-governing-entries-paddrs-for-page-table
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (marking-view x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            (wb
                             xlation-governing-entries-paddrs-for-page-directory
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (marking-view x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table
                             xlation-governing-entries-paddrs-for-pml4-table)
                            (wb
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p (xlation-governing-entries-paddrs lin-addr x86)
                            (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (marking-view x86))
                (canonical-address-p lin-addr))
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (mv-nth 1 (wb n write-addr w value x86))))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa
                             xlation-governing-entries-paddrs)
                            (wb
                             xlation-governing-entries-paddrs-for-pml4-table
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
                (disjoint-p (all-xlation-governing-entries-paddrs n lin-addr x86)
                            (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (marking-view x86)))
           (and
            (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
            (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))))
  :hints (("Goal"
           :induct (cons (all-xlation-governing-entries-paddrs n lin-addr x86)
                         (las-to-pas n lin-addr r-w-x (mv-nth 1 (wb n-w write-addr w value x86))))
           :in-theory (e/d* (las-to-pas)
                            (wb
                             xlation-governing-entries-paddrs
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================

;; Lemmas about interaction of memory reads and writes:

(defthm rb-wb-disjoint-in-non-marking-view
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas n-r  read-addr  r-x x86))
                 (mv-nth 1 (las-to-pas n-w write-addr   :w x86)))
                (disjoint-p
                 (all-xlation-governing-entries-paddrs n-r read-addr x86)
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (app-view x86))
                (not (marking-view x86))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
           (and
            (equal (mv-nth 0 (rb n-r read-addr r-x (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (rb n-r read-addr r-x x86)))
            (equal (mv-nth 1 (rb n-r read-addr r-x (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (rb n-r read-addr r-x x86)))))
  :hints (("Goal" :do-not-induct t)))

(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint-in-non-marking-view
  ;; Similar to rb-wb-disjoint-in-non-marking-view
  (implies (and (disjoint-p p-addrs
                            (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
                (not (app-view x86))
                (not (marking-view x86)))
           (equal (read-from-physical-memory p-addrs (mv-nth 1 (wb n-w write-addr w value x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthmd rb-wb-equal-in-non-marking-view
  (implies (and (equal
                 (mv-nth 1 (las-to-pas n-r read-addr r-x x86))
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (disjoint-p
                 (all-xlation-governing-entries-paddrs n-r read-addr x86)
                 (mv-nth 1 (las-to-pas n-r read-addr r-x x86)))
                (no-duplicates-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (app-view x86))
                (not (marking-view x86))
                (not (mv-nth 0 (las-to-pas n-r read-addr r-x x86)))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
           (equal (mv-nth 1 (rb n-r read-addr r-x (mv-nth 1 (wb n-w write-addr w value x86))))
                  (loghead (ash (nfix n-w) 3) value)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* () (force (force))))))

;; ======================================================================

;; las-to-pas error:

(local
 (defthmd mv-nth-0-las-to-pas-subset-p-in-non-marking-view-helper-0
   (implies (and (equal addr-2 addr-1)
                 ;; <n-2,addr-2> is a subset of <n-1,addr-1>.
                 (<= (+ n-2 addr-2) (+ n-1 addr-2))
                 (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
                 (posp n-1))
            (equal (mv-nth 0 (las-to-pas n-2 addr-2 r-w-x x86))
                   nil))))

(local
 (defthmd mv-nth-0-las-to-pas-subset-p-in-non-marking-view-helper-1
   (implies (and (signed-byte-p 48 addr-1)
                 (<= (+ addr-1 n-2) (+ addr-1 n-1))
                 (not (mv-nth 0 (ia32e-la-to-pa addr-1 r-w-x x86)))
                 (not (mv-nth 0 (las-to-pas (+ -1 n-1) (+ 1 addr-1) r-w-x x86)))
                 (not (xr :marking-view nil x86))
                 (integerp n-1)
                 (< 0 n-2))
            (not (mv-nth 0 (las-to-pas n-2 addr-1 r-w-x x86))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance mv-nth-0-las-to-pas-subset-p-in-non-marking-view-helper-0
                             (addr-2 addr-1)))))))

(defthmd mv-nth-0-las-to-pas-subset-p-in-non-marking-view
  (implies (and (bind-free (find-l-addrs-from-las-to-pas '(n-1 addr-1) r-w-x mfc state)
                           (n-1 addr-1))
                (syntaxp (and (not (eq n-1 n-2)) (not (eq addr-1 addr-2))))
                (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
                ;; <n-2,addr-2> is a (not strict) subset of <n-1,addr-1>.
                (<= addr-1 addr-2)
                (<= (+ n-2 addr-2) (+ n-1 addr-1))
                (not (marking-view x86))
                (posp n-1) (posp n-2) (integerp addr-2))
           (equal (mv-nth 0 (las-to-pas n-2 addr-2 r-w-x x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p-in-non-marking-view-helper-1)
                                   ()))))

;; ======================================================================

;; Lemmas about program-at:

(defthm program-at-nil-when-translation-error
  (implies (and (mv-nth 0 (las-to-pas (len bytes) prog-addr :x x86))
                (not (app-view x86)))
           (equal (program-at prog-addr bytes x86) nil))
  :hints (("Goal" :in-theory (e/d* (program-at) (force (force))))))

(defthm no-errors-when-translating-program-bytes-in-non-marking-view
  ;; This rule will help in fetching instruction bytes given relevant
  ;; information about the program (using program-at).

  ;; If I use (not (mv-nth 0 (las-to-pas n-bytes prog-addr :x x86)))
  ;; instead of (program-at prog-addr bytes x86) hypothesis below, this
  ;; rule would become as horrendously expensive as
  ;; mv-nth-0-las-to-pas-subset-p-in-non-marking-view.

  (implies (and (bind-free
                 (find-program-at-info 'prog-addr 'bytes mfc state)
                 (prog-addr bytes))
                (program-at prog-addr bytes x86)

                ;; We don't need the following hypothesis because we
                ;; have program-at-nil-when-translation-error.
                ;; (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x x86)))

                ;; <n,addr> is a subset of <(len bytes),prog-addr>.
                (<= prog-addr addr)
                (< (+ n addr) (+ (len bytes) prog-addr))
                (posp n) (integerp addr)
                (not (app-view x86))
                (not (marking-view x86)))
           (equal (mv-nth 0 (las-to-pas n addr :x x86)) nil))
  :hints (("Goal"
           :use ((:instance program-at-nil-when-translation-error))
           :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p-in-non-marking-view)
                            (program-at-nil-when-translation-error)))))

(defthm program-at-wb-disjoint-in-non-marking-view
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
             (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
            (disjoint-p
             (all-xlation-governing-entries-paddrs (len bytes) prog-addr x86)
             (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
            (not (app-view x86))
            (not (marking-view x86))
            (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
           (equal (program-at prog-addr bytes (mv-nth 1 (wb n-w write-addr w value x86)))
                  (program-at prog-addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (program-at) (rb wb)))))

;; ======================================================================

;; Lemmas about memory reads:

(defthm read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa-in-non-marking-view
  (implies (not (marking-view x86))
           (equal (read-from-physical-memory
                   p-addrs (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))


(defthmd rb-unwinding-thm-in-non-marking-view
  (implies (and (not (mv-nth 0 (rb n lin-addr r-w-x x86)))
                (posp n)
                (not (marking-view x86)))
           (equal (mv-nth 1 (rb n lin-addr r-w-x x86))
                  (logior (mv-nth 1 (rb 1 lin-addr r-w-x x86))
                          (ash (mv-nth 1 (rb (1- n) (1+ lin-addr) r-w-x x86)) 8))))
  :hints (("Goal" :in-theory (e/d (rb) (acl2::mv-nth-cons-meta force (force))))))

(local
 (defthmd rb-rb-subset-helper-1
   (implies (and (posp j)
                 (x86p x86))
            (equal (loghead (ash j 3) (xr :mem index x86))
                   (xr :mem index x86)))
   :hints (("Goal"
            :use ((:instance n08p-xr-mem (i index)))
            :in-theory (e/d* ()
                             (unsigned-byte-p
                              elem-p-of-xr-mem
                              n08p-xr-mem))))))

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-3/top" :dir :system))

   (defthmd rb-rb-subset-helper-2
     (implies (natp j)
              (equal (ash (loghead (ash j 3) x) 8)
                     (loghead (ash (1+ j) 3) (ash x 8))))
     :hints (("Goal" :in-theory (e/d* (loghead ash) ()))))))

(local
 (defthmd rb-rb-same-start-address-different-op-sizes-non-marking-view-helper
   (implies (and (equal (mv-nth 1 (rb i addr r-w-x x86)) val)
                 (canonical-address-p (+ -1 i addr))
                 (not (mv-nth 0 (las-to-pas i addr r-w-x x86)))
                 ;; The following should be inferrable from the above...
                 (not (mv-nth 0 (las-to-pas j addr r-w-x x86)))
                 (posp j)
                 (<= j i)
                 (not (app-view x86))
                 (not (marking-view x86))
                 (x86p x86))
            (equal (mv-nth 1 (rb j addr r-w-x x86))
                   (loghead (ash j 3) val)))
   :hints (("Goal"
            :in-theory (e/d* (rb-rb-subset-helper-1
                              rb-rb-subset-helper-2)
                             (unsigned-byte-p))))))

(defthmd rb-rb-same-start-address-different-op-sizes-non-marking-view
  (implies (and (equal (mv-nth 1 (rb i addr r-w-x x86)) val)
                (not (mv-nth 0 (las-to-pas i addr r-w-x x86)))
                (posp j)
                (<= j i)
                (canonical-address-p (+ -1 i addr))
                (integerp addr)
                (not (app-view x86))
                (not (marking-view x86))
                (x86p x86))
           (equal (mv-nth 1 (rb j addr r-w-x x86))
                  (loghead (ash j 3) val)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-rb-same-start-address-different-op-sizes-non-marking-view-helper)
                 (:instance mv-nth-0-las-to-pas-subset-p-in-non-marking-view
                            (n-1 i)
                            (addr-1 addr)
                            (n-2 j)
                            (addr-2 addr)))
           :in-theory (e/d* ()
                            (unsigned-byte-p
                             signed-byte-p)))))

(defun-nx rb-rb-induction-scheme (n-1 a-1 n-2 a-2 val x86)
;                    a-2
;   ------------------------------------------------------------------------
; ...   |   |   |   | w | w | w | w |   |   |   |   |   |   |   |   |   |  ...
;   ------------------------------------------------------------------------
;   0                    a-1                                               max
  (cond ((or (zp n-1) (zp n-2) (< n-2 n-1) (< a-1 a-2))
         (mv n-1 a-1 n-2 a-2 val x86))
        ((equal a-1 a-2)
         (mv n-1 a-1 n-2 a-2 val x86))
        ((< a-2 a-1)
         ;; Byte that won't be read by the most recent rb.
         (b* ((n-2 (1- n-2))
              (a-2 (1+ a-2))
              (val (logtail 8 val)))
           (rb-rb-induction-scheme n-1 a-1 n-2 a-2 val x86)))))

(defthmd rb-rb-subset-in-non-marking-view
  ;; [Shilpi]: Expensive rule. Keep this disabled.
  (implies (and (equal (mv-nth 1 (rb i addr-i r-w-x x86)) val)
                (not (mv-nth 0 (las-to-pas i addr-i r-w-x x86)))
                ;; <j,addr-j> is a subset (not strict) of <i,addr-i>.
                ;; This non-strictness is nice because it lets me have
                ;; a better hyp in one-read-with-rb-from-program-at-in-non-marking-view ---
                ;; (< lin-addr (+ (len bytes) prog-addr))
                ;; instead of
                ;; (< (+ 1 lin-addr) (+ (len bytes) prog-addr))
                (<= (+ j addr-j) (+ i addr-i))
                (<= addr-i addr-j)
                (canonical-address-p addr-i)
                (canonical-address-p (+ -1 i addr-i))
                (canonical-address-p addr-j)
                (posp i) (posp j)
                (not (app-view x86))
                (not (marking-view x86))
                (x86p x86))
           (equal (mv-nth 1 (rb j addr-j r-w-x x86))
                  (part-select val :low (ash (- addr-j addr-i) 3) :width (ash j 3))))
  :hints (("Goal"
           :induct (list (rb-rb-induction-scheme j addr-j i addr-i val x86)
                         (las-to-pas i addr-i r-w-x x86)
                         (las-to-pas j addr-j r-w-x x86))
           :in-theory (e/d* (signed-byte-p
                             ifix
                             nfix
                             rb-1-opener-theorem)
                            (unsigned-byte-p)))
          (if (equal (car id) '(0 1))
              '(:expand ((las-to-pas i addr-i r-w-x x86))
                        :use ((:instance rb-rb-same-start-address-different-op-sizes-non-marking-view
                                         (addr addr-i)))
                        :in-theory (e/d* (rb-rb-subset-helper-1
                                          rb-rb-subset-helper-2
                                          signed-byte-p
                                          ifix
                                          nfix
                                          rb-1-opener-theorem)
                                         (unsigned-byte-p
                                          signed-byte-p)))
            nil)))

(defthm many-reads-with-rb-from-program-at-in-non-marking-view
  (implies
   (and (bind-free (find-program-at-info 'prog-addr 'bytes mfc state)
                   (prog-addr bytes))
        (syntaxp (quotep n))
        (program-at prog-addr bytes x86)
        (<= prog-addr lin-addr)
        (< (+ n lin-addr) (+ (len bytes) prog-addr))
        (posp n)
        (canonical-address-p lin-addr)
        (byte-listp bytes)
        (not (app-view x86))
        (not (marking-view x86))
        (x86p x86))
   (equal (mv-nth 1 (rb n lin-addr :x x86))
          ;; During symbolic simulation of a program, we'd know the
          ;; concrete value of "bytes".  Moreover, note that using
          ;; combine-bytes instead of combine-n-bytes would have been
          ;; expensive because the former would combine all program
          ;; bytes whereas the latter only combines n of them.
          (combine-n-bytes (- lin-addr prog-addr) n bytes)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-rb-subset-in-non-marking-view
                            (addr-i prog-addr) (i (len bytes))
                            (addr-j lin-addr)  (j n)
                            (r-w-x :x)
                            (val (combine-bytes bytes)))
                 (:instance program-at-implies-canonical-addresses))
           :in-theory (e/d (program-at
                            relating-nth-and-combine-bytes
                            relating-combine-bytes-and-part-select)
                           (rb
                            canonical-address-p
                            acl2::mv-nth-cons-meta)))))

(defthm one-read-with-rb-from-program-at-in-non-marking-view
  ;; Even though we have
  ;; many-reads-with-rb-from-program-at-in-non-marking-view, I like having
  ;; this lemma around because it has a weaker hyp of
  ;; (< lin-addr (+ (len bytes) prog-addr))
  ;; instead of
  ;; (< (+ 1 lin-addr) (+ (len bytes) prog-addr)).
  (implies
   (and (bind-free (find-program-at-info 'prog-addr 'bytes mfc state)
                   (prog-addr bytes))
        (program-at prog-addr bytes x86)
        (<= prog-addr lin-addr)
        (< lin-addr (+ (len bytes) prog-addr))
        (canonical-address-p lin-addr)
        (byte-listp bytes)
        (not (marking-view x86))
        (not (app-view x86))
        (x86p x86))
   (equal (mv-nth 1 (rb 1 lin-addr :x x86))
          (nth (- lin-addr prog-addr) bytes)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (program-at
                            relating-nth-and-combine-bytes)
                           (rb
                            nth
                            signed-byte-p
                            not acl2::mv-nth-cons-meta))
           :use ((:instance rb-rb-subset-in-non-marking-view
                            (addr-i prog-addr) (i (len bytes))
                            (addr-j lin-addr)  (j 1)
                            (r-w-x :x)
                            (val (combine-bytes bytes)))
                 (:instance program-at-implies-canonical-addresses)))))

;; ======================================================================

(local
 (define r-x-irrelevant-ind-scheme (n lin-addr r-x-1 r-x-2 x86)
   :verify-guards nil
   :non-executable t
   :enabled t
   (if (zp n)
       (mv nil nil x86)
     (b* (((unless (canonical-address-p lin-addr))
           (mv t nil x86))
          ((mv flg-1 p-addr-1 x86-1)
           (ia32e-la-to-pa lin-addr r-x-1 x86))
          ((mv flg-2 p-addr-2 x86-2)
           (ia32e-la-to-pa lin-addr r-x-2 x86))
          ((unless (and (equal flg-1 flg-2)
                        (equal p-addr-1 p-addr-2)
                        (equal x86-1 x86-2)))
           (mv t nil x86-1))
          ((when flg-1) (mv flg-1 nil x86-1))
          ((mv flgs p-addrs x86)
           (r-x-irrelevant-ind-scheme
            (1- n) (1+ lin-addr) r-x-1 r-x-2 x86)))
       (mv flgs (if flgs nil (cons p-addr-1 p-addrs))
           x86)))))

(defthm r-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors-in-non-marking-view
  (implies (and
            (bind-free (find-almost-matching-las-to-pas 'r-x-1 n lin-addr mfc state)
                       (r-x-1))
            (syntaxp (and (not (eq r-x-2 r-x-1))
                          ;; r-x-2 must be "smaller" than r-x-1.
                          (term-order r-x-2 r-x-1)))
            (not (mv-nth 0 (las-to-pas n lin-addr r-x-1 x86)))
            (not (mv-nth 0 (las-to-pas n lin-addr r-x-2 x86)))
            (not (marking-view x86)))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-x-2 x86))
                  (mv-nth 1 (las-to-pas n lin-addr r-x-1 x86))))
  :hints (("Goal"
           :induct (r-x-irrelevant-ind-scheme n lin-addr r-x-1 r-x-2 x86))))

(defthm xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-p-in-non-marking-view
  (implies (and (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
                (disjoint-p (xlation-governing-entries-paddrs lin-addr x86)
                            (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (app-view x86))
                (not (marking-view x86))
                (x86p x86))
           (equal (xlation-governing-entries-paddrs lin-addr (mv-nth 1 (wb n-w write-addr w value x86)))
                  (xlation-governing-entries-paddrs lin-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p wb) ()))))

(defthm all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-in-non-marking-view
  (implies (and
            (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
            (disjoint-p (all-xlation-governing-entries-paddrs n lin-addr x86)
                        (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
            (not (app-view x86))
            (not (marking-view x86))
            (x86p x86))
           (equal (all-xlation-governing-entries-paddrs n lin-addr (mv-nth 1 (wb n-w write-addr w value x86)))
                  (all-xlation-governing-entries-paddrs n lin-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (all-xlation-governing-entries-paddrs)
                            (xlation-governing-entries-paddrs wb))
           :induct (all-xlation-governing-entries-paddrs n lin-addr x86))))

;; ======================================================================

(globally-disable '(rb wb canonical-address-p program-at
                       unsigned-byte-p signed-byte-p
                       las-to-pas all-xlation-governing-entries-paddrs))

(in-theory (e/d*
            ;; We enable all these functions so that reasoning about
            ;; memory can be done in terms of rb and wb.
            (riml-size
             rml-size
             wiml-size
             wml-size
             rml08 riml08 wml08 wiml08
             rml16 riml16 wml16 wiml16
             rml32 riml32 wml32 wiml32
             rml64 riml64 wml64 wiml64
             ea-to-la
             rme08 rime08 wme08 wime08)
            ()))

;; ======================================================================
