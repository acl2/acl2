;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "common-system-level-utils")
(include-book "paging/common-paging-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection non-marking-mode-proof-utilities
  :parents (proof-utilities debugging-code-proofs)

  :short "General-purpose code-proof libraries to include in the
  system-level non-marking mode (with A/D flag updates off)"

  :long "<p>When reasoning about an supervisor-mode program in the
  system-level <i>non-marking</i> mode of operation of the x86 ISA
  model, include the book
  @('x86isa/proofs/utilities/system-level-mode/non-marking-mode-top')
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
  these rules in @(see unwind-x86-interpreter-in-non-marking-mode).</p>

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
    @('get-prefixes-opener-lemma-no-prefix-byte'). <br/>
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
    Monitor @('rb-one-byte-of-program-in-non-marking-mode').
    </li>

   <li>When monitoring other rules above indicates that ACL2 can't
    resolve that the program remained unchanged (@(see
    program-at)) after a write operation @(see wb) occurred: <br/>
    Monitor @('program-at-wb-disjoint-in-non-marking-mode'). <br/>
    <br/>
    An instance of where monitoring this rule might be helpful is when
    the @('program-at') hypothesis of
    @('rb-one-byte-of-program-in-non-marking-mode') is not
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
    @('rb-one-byte-of-program-in-non-marking-mode') is not
    being relieved.
   </li>

   <li>When reasoning about disjointness/overlap of memory regions: <br/>
   @('rb-wb-disjoint-in-non-marking-mode') <br/>
   @('rb-wb-equal-in-non-marking-mode') <br/>
   @('la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode') <br/>
   @('all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-in-non-marking-mode')
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

(defsection unwind-x86-interpreter-in-non-marking-mode
  :parents (non-marking-mode-proof-utilities)

  ;; A benefit of defining this topic (apart from letting the user
  ;; view the definitions of the rules) is that if the rule names
  ;; mentioned in the parent topic are changed, the manual build
  ;; process will complain about broken links, and we'll know to
  ;; modify these two doc topics.

  :short "Definitions of rules to monitor in the system-level
  non-marking mode"

  :long "

 <h3>Rules about @('x86-run') and @('x86-fetch-decode-execute')</h3>

 @(def x86-run-opener-not-ms-not-zp-n)

 @(def x86-fetch-decode-execute-opener)

 <h3>Rules about @('get-prefixes')</h3>

 @(def get-prefixes-opener-lemma-no-prefix-byte)

 @(def get-prefixes-opener-lemma-group-1-prefix)

 @(def get-prefixes-opener-lemma-group-2-prefix)

 @(def get-prefixes-opener-lemma-group-3-prefix)

 @(def get-prefixes-opener-lemma-group-4-prefix)

 <h3>Rules related to instruction fetches and program location</h3>

 @(def rb-one-byte-of-program-in-non-marking-mode)

 @(def program-at-wb-disjoint-in-non-marking-mode)

 <h3>Rules related to canonical linear addresses</h3>

 @(def member-p-canonical-address-listp)

 <h3>Rules related to disjointness/overlap of memory regions</h3>

  @(def rb-wb-disjoint-in-non-marking-mode)
  @(def rb-wb-equal-in-non-marking-mode)
  @(def la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode)
  @(def all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-in-non-marking-mode)
")

(local (xdoc::set-default-parents non-marking-mode-proof-utilities))

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why ia32e-la-to-pa-values-and-mv-nth-1-wb)
;; (acl2::why rb-one-byte-of-program-in-non-marking-mode)
;; (acl2::why combine-bytes-rb-in-terms-of-rb-subset-p-in-non-marking-mode)
;; (acl2::why program-at-wb-disjoint-in-non-marking-mode)
;; (acl2::why rb-wb-disjoint-in-non-marking-mode)
;; (acl2::why disjointness-of-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode)

;; ======================================================================

;; Lemmas about memory reads:

(defthm read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa-in-non-marking-mode
  (implies (not (page-structure-marking-mode x86))
           (equal (read-from-physical-memory
                   p-addrs (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(defun find-prog-at-info (addr-var bytes-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((call (acl2::find-call-lst 'prog-at (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; prog-at term not encountered.
        nil))
    `((,addr-var . ,(nth 1 call))
      (,bytes-var . ,(nth 2 call)))))

(defthm rb-one-byte-of-program-in-non-marking-mode
  (implies (and (bind-free
                 (find-prog-at-info 'prog-addr 'bytes mfc state)
                 (prog-addr bytes))
                (prog-at prog-addr bytes x86)
                (<= prog-addr lin-addr)
                (< lin-addr (+ (len bytes) prog-addr))
                (canonical-address-p lin-addr)
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (rb 1 lin-addr :x x86))
                  (nth (- lin-addr prog-addr) bytes)))
  :hints (("Goal" :in-theory (e/d (prog-at rm08)
                                  (not acl2::mv-nth-cons-meta)))))

(defthmd rb-unwinding-thm-in-non-marking-mode
  (implies (and (not (mv-nth 0 (rb n lin-addr r-w-x x86)))
                (posp n)
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (rb n lin-addr r-w-x x86))
                  (logior (mv-nth 1 (rb 1 lin-addr r-w-x x86))
                          (ash (mv-nth 1 (rb (1- n) (1+ lin-addr) r-w-x x86)) 8))))
  :hints (("Goal" :in-theory (e/d (rb) (acl2::mv-nth-cons-meta force (force))))))

(defthm rb-in-terms-of-rb-subset-p-in-non-marking-mode
  (implies
   (and (bind-free
         (find-prog-at-info 'prog-addr 'bytes mfc state)
         (prog-addr bytes))
        (syntaxp (quotep n))
        (prog-at prog-addr bytes x86)
        (<= prog-addr lin-addr)
        (< (+ n lin-addr) (+ (len bytes) prog-addr))
        (not (mv-nth 0 (las-to-pas n lin-addr :x x86)))
        (posp n)
        (not (programmer-level-mode x86))
        (not (page-structure-marking-mode x86)))
   (equal (mv-nth 1 (rb n lin-addr :x x86))
          (logior (nth (- lin-addr prog-addr) bytes)
                  (ash (mv-nth 1 (rb (1- n) (1+ lin-addr) :x x86)) 8))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d ()
                           (rb
                            canonical-address-p
                            acl2::mv-nth-cons-meta
                            rb-one-byte-of-program-in-non-marking-mode))
           :use ((:instance rb-one-byte-of-program-in-non-marking-mode)
                 (:instance rb-unwinding-thm-in-non-marking-mode
                            (r-w-x :x))))))

;; ======================================================================

;; Lemmas about memory writes:

(defthm xr-mem-wb-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n lin-addr :w x86)))
                (disjoint-p (list index)
                            (mv-nth 1 (las-to-pas n lin-addr :w x86)))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86)))
           (equal (xr :mem index (mv-nth 1 (wb n lin-addr w value x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (wb write-to-physical-memory disjoint-p member-p)
                                   ((:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

(defthm mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode
  (implies (and (bind-free (find-l-addrs-from-las-to-pas '(n addr) r-w-x mfc state)
                           (n addr))
                ;; <1,a> is a subset of <n,addr>.
                (<= addr a)
                (< a (+ n addr))
                (not (mv-nth 0 (las-to-pas n addr r-w-x x86)))
                (not (page-structure-marking-mode x86))
                (posp n) (integerp a))
           (equal (mv-nth 0 (ia32e-la-to-pa a r-w-x x86)) nil)))

(defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode
  (implies (and
            ;; <1,a> is a subset of <n,addr>.
            (<= addr a)
            (< a (+ n addr))
            (not (mv-nth 0 (las-to-pas n addr r-w-x x86)))
            (not (page-structure-marking-mode x86))
            (posp n) (integerp a))
           (member-p (mv-nth 1 (ia32e-la-to-pa a r-w-x x86))
                     (mv-nth 1 (las-to-pas n addr r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm las-to-pas-values-and-xw-mem-not-member-in-non-marking-mode
  (implies (and (not (member-p index (all-xlation-governing-entries-paddrs n lin-addr x86)))
                (not (page-structure-marking-mode x86)))
           (and (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x (xw :mem index byte x86)))
                       (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x (xw :mem index byte x86)))
                       (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))))
  :hints (("Goal"
           :in-theory (e/d* (disjoint-p member-p)
                            (xlation-governing-entries-paddrs)))))

;; ======================================================================

;; Lemmas about interaction of writes and paging walkers:

(defthm rm-low-32-wb-in-non-marking-mode-disjoint
  (implies (and (not (mv-nth 0 (las-to-pas n addr :w x86)))
                (disjoint-p (addr-range 4 index)
                            (mv-nth 1 (las-to-pas n addr :w x86)))
                (not (page-structure-marking-mode x86)))
           (equal (rm-low-32 index (mv-nth 1 (wb n addr w value x86)))
                  (rm-low-32 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32 disjoint-p member-p)
                                   (write-to-physical-memory
                                    (:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

(defthm rm-low-64-wb-in-non-marking-mode-disjoint
  (implies (and (not (mv-nth 0 (las-to-pas n addr :w x86)))
                (disjoint-p (addr-range 8 index)
                            (mv-nth 1 (las-to-pas n addr :w x86)))
                (not (page-structure-marking-mode x86))
                (integerp index))
           (equal (rm-low-64 index (mv-nth 1 (wb n addr w value x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                            (wb (:meta acl2::mv-nth-cons-meta)
                                force (force))))))

(defthm las-to-pas-values-in-non-marking-mode-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p (all-xlation-governing-entries-paddrs n lin-addr x86) p-addrs)
                (physical-address-listp p-addrs)
                (not (page-structure-marking-mode x86)))
           (and (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))))
  :hints (("Goal" :induct (las-to-pas n lin-addr r-w-x x86)
           :in-theory (e/d* (disjoint-p disjoint-p-commutative) (xlation-governing-entries-paddrs)))))

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (page-structure-marking-mode x86))
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

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (page-structure-marking-mode x86))
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

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (page-structure-marking-mode x86))
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

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p
                 (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (page-structure-marking-mode x86))
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

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n write-addr :w x86)))
                (disjoint-p (xlation-governing-entries-paddrs lin-addr x86)
                            (mv-nth 1 (las-to-pas n write-addr :w x86)))
                (not (page-structure-marking-mode x86))
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

(defthm la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
                (disjoint-p (all-xlation-governing-entries-paddrs n lin-addr x86)
                            (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (page-structure-marking-mode x86)))
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

(defthm rb-wb-disjoint-in-non-marking-mode
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas n-r  read-addr  r-x x86))
                 (mv-nth 1 (las-to-pas n-w write-addr   :w x86)))
                (disjoint-p
                 (all-xlation-governing-entries-paddrs n-r read-addr x86)
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
           (and
            (equal (mv-nth 0 (rb n-r read-addr r-x (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (rb n-r read-addr r-x x86)))
            (equal (mv-nth 1 (rb n-r read-addr r-x (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (rb n-r read-addr r-x x86)))))
  :hints (("Goal" :do-not-induct t)))

(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint-in-non-marking-mode
  ;; Similar to rb-wb-disjoint-in-non-marking-mode
  (implies (and (disjoint-p p-addrs
                            (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86)))
           (equal (read-from-physical-memory p-addrs (mv-nth 1 (wb n-w write-addr w value x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthmd rb-wb-equal-in-non-marking-mode
  (implies (and (equal
                 (mv-nth 1 (las-to-pas n-r read-addr r-x x86))
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (disjoint-p
                 (all-xlation-governing-entries-paddrs n-r read-addr x86)
                 (mv-nth 1 (las-to-pas n-r read-addr r-x x86)))
                (no-duplicates-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (not (mv-nth 0 (las-to-pas n-r read-addr r-x x86)))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
           (equal (mv-nth 1 (rb n-r read-addr r-x (mv-nth 1 (wb n-w write-addr w value x86))))
                  (loghead (ash (nfix n-w) 3) value)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* () (force (force))))))

;; ======================================================================

(local
 (defthmd mv-nth-0-las-to-pas-subset-p-in-non-marking-mode-helper-0
   (implies (and (equal addr-2 addr-1)
                 ;; <n-2,addr-2> is a subset of <n-1,addr-1>.
                 (< (+ n-2 addr-2) (+ n-1 addr-2))
                 (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
                 (posp n-1))
            (equal (mv-nth 0 (las-to-pas n-2 addr-2 r-w-x x86))
                   nil))))

(local
 (defthmd mv-nth-0-las-to-pas-subset-p-in-non-marking-mode-helper-1
   (implies (and (signed-byte-p 48 addr-1)
                 (< (+ addr-1 n-2) (+ addr-1 n-1))
                 (not (mv-nth 0 (ia32e-la-to-pa addr-1 r-w-x x86)))
                 (not (mv-nth 0 (las-to-pas (+ -1 n-1) (+ 1 addr-1) r-w-x x86)))
                 (not (xr :page-structure-marking-mode 0 x86))
                 (integerp n-1)
                 (< 0 n-2))
            (not (mv-nth 0 (las-to-pas n-2 addr-1 r-w-x x86))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance mv-nth-0-las-to-pas-subset-p-in-non-marking-mode-helper-0
                             (addr-2 addr-1)))))))

(defthmd mv-nth-0-las-to-pas-subset-p-in-non-marking-mode
  (implies (and (bind-free (find-l-addrs-from-las-to-pas '(n-1 addr-1) r-w-x mfc state)
                           (n-1 addr-1))
                (syntaxp (and (not (eq n-1 n-2)) (not (eq addr-1 addr-2))))
                (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
                ;; <n-2,addr-2> is a subset of <n-1,addr-1>.
                (<= addr-1 addr-2)
                (< (+ n-2 addr-2) (+ n-1 addr-1))
                (not (page-structure-marking-mode x86))
                (posp n-1) (posp n-2) (integerp addr-2))
           (equal (mv-nth 0 (las-to-pas n-2 addr-2 r-w-x x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p-in-non-marking-mode-helper-1)
                                   ()))))

(defthm no-errors-when-translating-program-bytes-in-non-marking-mode
  ;; This rule will help in fetching instructions.
  (implies (and ;; (bind-free
            ;;  (find-prog-at-info 'prog-addr 'bytes mfc state)
            ;;  (prog-addr bytes))
            (not (mv-nth 0 (las-to-pas n-bytes prog-addr :x x86)))
            (syntaxp (and (not (eq n-bytes n)) (not (eq prog-addr addr))))
            ;; <n,addr> is a subset of <n-bytes,prog-addr>.
            (<= prog-addr addr)
            (< (+ n addr) (+ n-bytes prog-addr))
            (posp n-bytes) (integerp addr)
            (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas n addr :x x86)) nil)))

;; ======================================================================

;; Lemmas about prog-at:

(defthm prog-at-nil-when-translation-error
  (implies (and (mv-nth 0 (las-to-pas (len bytes) prog-addr :x x86))
                (not (programmer-level-mode x86)))
           (equal (prog-at prog-addr bytes x86) nil))
  :hints (("Goal" :in-theory (e/d* (prog-at) (force (force))))))

;; (defthm prog-at-in-terms-of-rb-in-non-marking-mode
;;   (implies (and (not (mv-nth 0 (rb (len bytes) prog-addr :x x86)))
;;                 (not (programmer-level-mode x86))
;;                 (not (page-structure-marking-mode x86)))
;;            (equal (prog-at prog-addr bytes x86)
;;                   (equal (mv-nth 1 (rb (len bytes) prog-addr :x x86))
;;                          (combine-bytes (acl2::rev bytes)))))
;;   :hints (("Goal" :in-theory (e/d* (prog-at)
;;                                    (rb)))))

;; (defthm mv-nth-1-ia32e-la-to-pa-not-member-of-mv-nth-1-las-to-pas
;;   (implies (and (bind-free (find-l-addrs-from-las-to-pas '(n-1 addr-1) r-w-x-1 mfc state)
;;                            (n-1 addr-1))
;;                 (disjoint-p (mv-nth 1 (las-to-pas n-1 addr-1 r-w-x-1 x86))
;;                             (mv-nth 1 (las-to-pas n-2 addr-2 r-w-x-2 x86)))
;;                 ;; <1,a> is a subset of <n-1,addr-1>.
;;                 (<= addr-1 a) (< a (+ n-1 addr-1))
;;                 (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x-1 x86)))
;;                 (not (page-structure-marking-mode x86))
;;                 (posp n-1) (integerp a))
;;            (equal (member-p (mv-nth 1 (ia32e-la-to-pa a r-w-x-1 x86))
;;                             (mv-nth 1 (las-to-pas n-2 addr-2 r-w-x-2 x86)))
;;                   nil))
;;   :hints
;;   (("Goal"
;;     :do-not-induct t
;;     :in-theory
;;     (e/d* (disjoint-p member-p)
;;           (mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode))
;;     :use ((:instance mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode
;;                      (n n-1) (addr addr-1) (r-w-x r-w-x-1) (a a))))))

;; (defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode-new
;;   (implies (and
;;             ;; <1,a> is a subset of <n,addr>.
;;             (<= addr a)
;;             (< a (+ n addr))
;;             (not (mv-nth 0 (las-to-pas n addr r-w-x-1 x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa a r-w-x-2 x86)))
;;             (not (page-structure-marking-mode x86))
;;             (posp n) (integerp a))
;;            (member-p (mv-nth 1 (ia32e-la-to-pa a r-w-x-2 x86))
;;                      (mv-nth 1 (las-to-pas n addr r-w-x-1 x86))))
;;   :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(local
 (defthm prog-at-wb-disjoint-in-non-marking-mode-helper-0
   (implies
    (and (signed-byte-p 48 prog-addr)
         (not (mv-nth 0 (ia32e-la-to-pa prog-addr :x x86)))
         (disjoint-p (cons (mv-nth 1 (ia32e-la-to-pa prog-addr :x x86))
                           (mv-nth 1
                                   (las-to-pas (len (cdr bytes))
                                               (+ 1 prog-addr)
                                               :x x86)))
                     (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
         (disjoint-p (xlation-governing-entries-paddrs prog-addr x86)
                     (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
         (not (xr :programmer-level-mode 0 x86))
         (not (xr :page-structure-marking-mode 0 x86))
         (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
    (equal (mv-nth 1 (rb 1 prog-addr :x (mv-nth 1 (wb n-w write-addr w value x86))))
           (mv-nth 1 (rb 1 prog-addr :x x86))))
   :hints (("goal" :do-not-induct t
            :in-theory (e/d (disjoint-p prog-at) (rb wb))))))

(local
 (defthm non-zero-len-of-consp
   ;; Ugh, why do I need this?
   (implies (consp x)
            (equal (equal (len x) 0) nil))))

(local
 (defthm prog-at-wb-disjoint-in-non-marking-mode-helper-1
   (implies
    (and (consp bytes)
         (signed-byte-p 48 prog-addr)
         (disjoint-p
          (all-xlation-governing-entries-paddrs (len bytes) prog-addr x86)
          (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
         (not (xr :page-structure-marking-mode 0 x86))
         (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
    (equal (mv-nth 0 (ia32e-la-to-pa prog-addr :x (mv-nth 1 (wb n-w write-addr w value x86))))
           (mv-nth 0 (ia32e-la-to-pa prog-addr :x x86))))
   :hints (("goal" :do-not-induct t
            :expand ((all-xlation-governing-entries-paddrs (len bytes) prog-addr x86))
            :in-theory (e/d (disjoint-p prog-at) (rb wb))))))

(local
 (defthm prog-at-wb-disjoint-in-non-marking-mode-helper-2
   (implies (and (consp bytes)
                 (signed-byte-p 48 prog-addr)
                 (not (mv-nth 0 (ia32e-la-to-pa prog-addr :x x86)))
                 (not (equal (car bytes)
                             (mv-nth 1 (rb 1 prog-addr :x (mv-nth 1 (wb n-w write-addr w value x86))))))
                 (disjoint-p
                  (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
                  (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                 (disjoint-p
                  (all-xlation-governing-entries-paddrs (len bytes) prog-addr x86)
                  (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                 (not (xr :programmer-level-mode 0 x86))
                 (not (xr :page-structure-marking-mode 0 x86))
                 (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
            (not (prog-at prog-addr bytes x86)))
   :hints (("Goal"
            :use ((:instance prog-at-wb-disjoint-in-non-marking-mode-helper-0))
            :expand ((las-to-pas (len bytes) prog-addr :x x86)
                     (all-xlation-governing-entries-paddrs (len bytes) prog-addr x86))
            :in-theory (e/d* ()
                             (prog-at-wb-disjoint-in-non-marking-mode-helper-0 prog-at rb wb))
            :do-not-induct t))))

(defthm prog-at-wb-disjoint-in-non-marking-mode
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
             (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
            (disjoint-p
             (all-xlation-governing-entries-paddrs (len bytes) prog-addr x86)
             (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (not (mv-nth 0 (las-to-pas n-w write-addr :w x86))))
           (equal (prog-at prog-addr bytes (mv-nth 1 (wb n-w write-addr w value x86)))
                  (prog-at prog-addr bytes x86)))
  :hints (("Goal"
           :induct (prog-at prog-addr bytes (mv-nth 1 (wb n-w write-addr w value x86)))
           :in-theory (e/d (prog-at) (rb wb)))))

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

(defthm r-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors-in-non-marking-mode
  (implies (and
            (bind-free (find-almost-matching-las-to-pas 'r-x-1 n lin-addr mfc state)
                       (r-x-1))
            (syntaxp (and (not (eq r-x-2 r-x-1))
                          ;; r-x-2 must be "smaller" than r-x-1.
                          (term-order r-x-2 r-x-1)))
            (not (mv-nth 0 (las-to-pas n lin-addr r-x-1 x86)))
            (not (mv-nth 0 (las-to-pas n lin-addr r-x-2 x86)))
            (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-x-2 x86))
                  (mv-nth 1 (las-to-pas n lin-addr r-x-1 x86))))
  :hints (("Goal"
           :induct (r-x-irrelevant-ind-scheme n lin-addr r-x-1 r-x-2 x86))))

(defthm xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-p-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
                (disjoint-p (xlation-governing-entries-paddrs lin-addr x86)
                            (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (xlation-governing-entries-paddrs lin-addr (mv-nth 1 (wb n-w write-addr w value x86)))
                  (xlation-governing-entries-paddrs lin-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p wb) ()))))

(defthm all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-in-non-marking-mode
  (implies (and
            (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
            (disjoint-p (all-xlation-governing-entries-paddrs n lin-addr x86)
                        (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (x86p x86))
           (equal (all-xlation-governing-entries-paddrs n lin-addr (mv-nth 1 (wb n-w write-addr w value x86)))
                  (all-xlation-governing-entries-paddrs n lin-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (all-xlation-governing-entries-paddrs)
                            (xlation-governing-entries-paddrs wb))
           :induct (all-xlation-governing-entries-paddrs n lin-addr x86))))

;; ======================================================================

(globally-disable '(rb wb canonical-address-p prog-at
                       unsigned-byte-p signed-byte-p
                       las-to-pas all-xlation-governing-entries-paddrs))

(in-theory (e/d*
            ;; We enable all these functions so that reasoning about
            ;; memory can be done in terms of rb and wb.
            (rim-size
             rm-size
             wim-size
             wm-size
             rm08 rim08 wm08 wim08
             rm16 rim16 wm16 wim16
             rm32 rim32 wm32 wim32
             rm64 rim64 wm64 wim64)
            ()))

;; ======================================================================
