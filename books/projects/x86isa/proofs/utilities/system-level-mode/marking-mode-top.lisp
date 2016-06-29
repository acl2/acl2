;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "marking-mode-utils")

(local (include-book "gl-lemmas"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection marking-mode-top
  :parents (proof-utilities)

  :short "Reasoning in the system-level marking mode"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents marking-mode-top))

;; ======================================================================

(defthm gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-disjoint
  (implies
   (and (disjoint-p p-addrs
                    (open-qword-paddr-list
                     (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (physical-address-listp p-addrs))
   (equal
    (gather-all-paging-structure-qword-addresses (write-to-physical-memory p-addrs bytes x86))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (write-to-physical-memory
                                    byte-listp
                                    n08p
                                    len
                                    disjoint-p
                                    gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)
                                   ()))))

(defthm gather-all-paging-structure-qword-addresses-and-wb-disjoint
  (implies
   (and
    ;; We need disjoint-p$ here instead of disjoint-p because this
    ;; first hyp should be present in the top-level hyps of the
    ;; effects theorems of programs.
    (disjoint-p$ (mv-nth 1 (las-to-pas
                            (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
                 (open-qword-paddr-list
                  (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (not (programmer-level-mode x86))
    (addr-byte-alistp addr-lst))
   (equal
    (gather-all-paging-structure-qword-addresses (mv-nth 1 (wb addr-lst x86)))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (wb disjoint-p$) (force (force) (:meta acl2::mv-nth-cons-meta))))))

;; ======================================================================

;; Lemmas about direct-map-p:

(defun-nx direct-map-p (count addr r-w-x cpl x86)
  (equal
   (mv-nth 1 (las-to-pas (create-canonical-address-list count addr) r-w-x cpl x86))
   (addr-range count addr)))

(defthm xlate-equiv-memory-and-direct-map-p
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (direct-map-p count addr r-w-x cpl x86-1)
                  (direct-map-p count addr r-w-x cpl x86-2)))
  :rule-classes :congruence)

(defthm direct-map-p-and-wb-disjoint-from-xlation-governing-addrs
  (implies
   (and (equal cpl (cpl x86))
        (disjoint-p
         (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl (double-rewrite x86)))
         (all-translation-governing-addresses (create-canonical-address-list count addr) (double-rewrite x86))))
   (equal (direct-map-p count addr r-w-x cpl (mv-nth 1 (wb addr-lst x86)))
          (direct-map-p count addr r-w-x cpl (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(in-theory (e/d* () (direct-map-p)))

;; ======================================================================

(defsection get-prefixes-alt
  :parents (marking-mode-top)

  :short "Rewriting @('get-prefixes') to @('get-prefixes-alt')"

  :long "<p>The following is not a theorem, which is why we can not
  define congruence rules about @('get-prefixes') and
  @('xlate-equiv-memory') directly.</p>

 <code>
 (implies
  (xlate-equiv-memory x86-1 x86-2)
  (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-1))
         (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-2))))
 </code>

 <p>The above would be a theorem if the following pre-conditions held
 about both @('x86-1') and @('x86-2'):</p>

 <code>
 (and (page-structure-marking-mode x86)
      (not (programmer-level-mode x86))
      (canonical-address-p start-rip)
      (disjoint-p
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) x86))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses x86)))
      (not (mv-nth 0 (las-to-pas
                      (create-canonical-address-list cnt start-rip)
                      :x (cpl x86) x86))))
 </code>

 <p>Since 'conditional' congruence rules can't be defined, we define
 an alternative version of @('get-prefixes'), called
 @('get-prefixes-alt'), which is equal to @('get-prefixes') if these
 pre-conditions hold, and if not, it returns benign values.  We prove
 a rewrite rule that rewrites @('get-prefixes') to
 @('get-prefixes-alt') when applicable, and then we can prove
 congruence rules about @('get-prefixes-alt') and
 @('xlate-equiv-memory').  Note that this approach will be most
 successful if we expect these pre-conditions to hold all the
 time.</p>

 <p>The biggest drawback of this approach to have 'conditional'
 congruence-based rules is that all the theorems I have about
 @('get-prefixes') now have to be re-proved in terms of
 @('get-prefixes-alt').</p>"


  (define get-prefixes-alt
    ((start-rip :type (signed-byte   #.*max-linear-address-size*))
     (prefixes  :type (unsigned-byte 43))
     (cnt       :type (integer 0 5))
     x86)
    :non-executable t
    :guard (canonical-address-p (+ cnt start-rip))
    (if (and (page-structure-marking-mode x86)
             (not (programmer-level-mode x86))
             (canonical-address-p start-rip)
             (disjoint-p
              (mv-nth 1 (las-to-pas
                         (create-canonical-address-list cnt start-rip)
                         :x (cpl x86) x86))
              (open-qword-paddr-list
               (gather-all-paging-structure-qword-addresses x86)))
             (not (mv-nth 0 (las-to-pas
                             (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) x86))))

        (get-prefixes start-rip prefixes cnt x86)

      (mv nil prefixes x86))

    ///

    (defthm natp-get-prefixes-alt
      (implies (forced-and (natp prefixes)
                           (canonical-address-p start-rip)
                           (x86p x86))
               (natp (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86))))
      :hints (("Goal"
               :cases ((and (page-structure-marking-mode x86)
                            (not (programmer-level-mode x86))
                            (not (mv-nth 0 (las-to-pas nil r-w-x (cpl x86) x86)))))
               :in-theory (e/d (las-to-pas)
                               ())))
      :rule-classes :type-prescription)

    (defthm-usb n43p-get-prefixes-alt
      :hyp (and (n43p prefixes)
                (canonical-address-p start-rip)
                (x86p x86))
      :bound 43
      :concl (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86))
      :hints (("Goal"
               :use ((:instance n43p-get-prefixes))
               :in-theory (e/d () (n43p-get-prefixes))))
      :gen-linear t)

    (defthm x86p-get-prefixes-alt
      (implies (force (x86p x86))
               (x86p (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))))

    (make-event
     (generate-xr-over-write-thms
      (remove-elements-from-list
       '(:mem :fault)
       *x86-field-names-as-keywords*)
      'get-prefixes-alt
      (acl2::formals 'get-prefixes-alt (w state))
      :output-index 2))

    (defthm xr-fault-and-get-prefixes-alt
      (equal (xr :fault index (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
             (xr :fault index x86))
      :hints (("Goal" :in-theory (e/d* (get-prefixes-alt)
                                       (not force (force))))))

    (make-event
     (generate-read-fn-over-xw-thms
      (remove-elements-from-list
       '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
       *x86-field-names-as-keywords*)
      'get-prefixes-alt
      (acl2::formals 'get-prefixes-alt (w state))
      :output-index 0
      ;; :hyps '(not (programmer-level-mode x86))
      :double-rewrite? t))

    (make-event
     (generate-read-fn-over-xw-thms
      (remove-elements-from-list
       '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
       *x86-field-names-as-keywords*)
      'get-prefixes-alt
      (acl2::formals 'get-prefixes-alt (w state))
      :output-index 1
      ;; :hyps '(not (programmer-level-mode x86))
      :double-rewrite? t))

    (make-event
     (generate-write-fn-over-xw-thms
      (remove-elements-from-list
       '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
       *x86-field-names-as-keywords*)
      'get-prefixes-alt
      (acl2::formals 'get-prefixes-alt (w state))
      :output-index 2
      ;; :hyps '(not (programmer-level-mode x86))
      ))

    (defthm get-prefixes-alt-values-and-!flgi-in-system-level-mode
      (implies (and (not (equal index *ac*))
                    (x86p x86))
               (and (equal (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt
                                                       (!flgi index value x86)))
                           (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (double-rewrite x86))))
                    (equal (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt
                                                       (!flgi index value x86)))
                           (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (double-rewrite x86))))))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d* ()
                                (force (force))))))

    (defthm get-prefixes-alt-and-!flgi-state-in-system-level-mode
      (implies (and (not (equal index *ac*))
                    (not (programmer-level-mode x86))
                    (x86p x86))
               (equal (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt (!flgi index value x86)))
                      (!flgi index value (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d* ()
                                (force (force))))))

    (defthm flgi-and-mv-nth-2-get-prefixes-alt
      (equal (flgi index (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
             (flgi index x86))
      :hints (("Goal" :in-theory (e/d* (flgi) ()))))

    (defthm alignment-checking-enabled-p-and-mv-nth-2-get-prefixes-alt
      (equal (alignment-checking-enabled-p (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
             (alignment-checking-enabled-p x86))
      :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p flgi) ())))))

  (defthm rewrite-get-prefixes-to-get-prefixes-alt
    (implies (forced-and
              (disjoint-p
               (mv-nth 1 (las-to-pas
                          (create-canonical-address-list cnt start-rip)
                          :x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (not (mv-nth 0 (las-to-pas
                              (create-canonical-address-list cnt start-rip)
                              :x (cpl x86) (double-rewrite x86))))
              (page-structure-marking-mode x86)
              (not (programmer-level-mode x86))
              (canonical-address-p start-rip))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes-alt start-rip prefixes cnt (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (get-prefixes-alt) ()))))

  ;; Opener lemmas:

  (defthm get-prefixes-alt-opener-lemma-zero-cnt
    (implies (and (zp cnt)
                  (disjoint-p
                   (mv-nth 1 (las-to-pas
                              (create-canonical-address-list cnt start-rip)
                              :x (cpl x86) (double-rewrite x86)))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
                  (not
                   (mv-nth
                    0
                    (las-to-pas (create-canonical-address-list cnt start-rip)
                                :x (cpl x86)
                                (double-rewrite x86))))
                  (page-structure-marking-mode x86)
                  (not (programmer-level-mode x86))
                  (canonical-address-p start-rip))
             (equal (get-prefixes-alt start-rip prefixes cnt x86)
                    (mv nil prefixes x86)))
    :hints (("Goal"
             :use ((:instance get-prefixes-opener-lemma-zero-cnt))
             :in-theory (e/d () (get-prefixes-opener-lemma-zero-cnt
                                 force (force))))))

  (defthm get-prefixes-alt-opener-lemma-no-prefix-byte
    (implies (and (let*
                      ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                       (prefix-byte-group-code
                        (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
                    (and (not flg)
                         (zp prefix-byte-group-code)))
                  (not (zp cnt))
                  (page-structure-marking-mode x86)
                  (not (programmer-level-mode x86))
                  (canonical-address-p start-rip)
                  (not
                   (mv-nth
                    0
                    (las-to-pas (create-canonical-address-list cnt start-rip)
                                :x (cpl x86)
                                (double-rewrite x86))))
                  (disjoint-p
                   (mv-nth 1 (las-to-pas
                              (create-canonical-address-list cnt start-rip)
                              :x (cpl x86) (double-rewrite x86)))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
             (and
              (equal (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86))
                     nil)
              (equal (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86))
                     (let ((prefixes
                            (!prefixes-slice :next-byte
                                             (mv-nth 1 (rm08 start-rip :x x86))
                                             prefixes)))
                       (!prefixes-slice :num-prefixes (- 5 cnt) prefixes)))))
    :hints (("Goal"
             :use ((:instance get-prefixes-opener-lemma-no-prefix-byte))
             :in-theory (e/d* () (get-prefixes-opener-lemma-no-prefix-byte)))))

  (defthm get-prefixes-alt-opener-lemma-group-1-prefix-in-marking-mode
    (implies
     (and
      (canonical-address-p (1+ start-rip))
      (not (zp cnt))
      (equal (prefixes-slice :group-1-prefix prefixes) 0)
      (let*
          ((flg (mv-nth 0 (rm08 start-rip :x x86)))
           (prefix-byte-group-code
            (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
        (and (not flg)
             (equal prefix-byte-group-code 1)))
      (page-structure-marking-mode x86)
      (not (programmer-level-mode x86))
      (canonical-address-p start-rip)
      (disjoint-p
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses x86)))
      (not
       (mv-nth
        0
        (las-to-pas (create-canonical-address-list cnt start-rip)
                    :x (cpl x86)
                    x86))))
     (equal (get-prefixes-alt start-rip prefixes cnt x86)
            (get-prefixes-alt (+ 1 start-rip)
                              (!prefixes-slice :group-1-prefix
                                               (mv-nth 1 (rm08 start-rip :x x86))
                                               prefixes)
                              (+ -1 cnt)
                              (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance get-prefixes-opener-lemma-group-1-prefix-in-marking-mode)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes (!prefixes-slice :group-1-prefix
                                                         (mv-nth 1 (rm08 start-rip :x x86))
                                                         prefixes))
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rm08 start-rip :x x86)))))
             :in-theory (e/d* (las-to-pas)
                              (get-prefixes-opener-lemma-group-1-prefix-in-marking-mode
                               rewrite-get-prefixes-to-get-prefixes-alt
                               acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-alt-opener-lemma-group-2-prefix-in-marking-mode
    (implies
     (and
      (canonical-address-p (1+ start-rip))
      (not (zp cnt))
      (equal (prefixes-slice :group-2-prefix prefixes) 0)
      (let*
          ((flg (mv-nth 0 (rm08 start-rip :x x86)))
           (prefix-byte-group-code
            (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
        (and (not flg)
             (equal prefix-byte-group-code 2)))
      (page-structure-marking-mode x86)
      (not (programmer-level-mode x86))
      (canonical-address-p start-rip)
      (disjoint-p
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses x86)))
      (not
       (mv-nth
        0
        (las-to-pas (create-canonical-address-list cnt start-rip)
                    :x (cpl x86)
                    x86))))
     (equal (get-prefixes-alt start-rip prefixes cnt x86)
            (get-prefixes-alt (+ 1 start-rip)
                              (!prefixes-slice :group-2-prefix
                                               (mv-nth 1 (rm08 start-rip :x x86))
                                               prefixes)
                              (+ -1 cnt)
                              (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance get-prefixes-opener-lemma-group-2-prefix-in-marking-mode)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes (!prefixes-slice :group-2-prefix
                                                         (mv-nth 1 (rm08 start-rip :x x86))
                                                         prefixes))
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rm08 start-rip :x x86)))))
             :in-theory (e/d* (las-to-pas)
                              (get-prefixes-opener-lemma-group-2-prefix-in-marking-mode
                               rewrite-get-prefixes-to-get-prefixes-alt
                               acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-alt-opener-lemma-group-3-prefix-in-marking-mode
    (implies
     (and
      (canonical-address-p (1+ start-rip))
      (not (zp cnt))
      (equal (prefixes-slice :group-3-prefix prefixes) 0)
      (let*
          ((flg (mv-nth 0 (rm08 start-rip :x x86)))
           (prefix-byte-group-code
            (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
        (and (not flg)
             (equal prefix-byte-group-code 3)))
      (page-structure-marking-mode x86)
      (not (programmer-level-mode x86))
      (canonical-address-p start-rip)
      (disjoint-p
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses x86)))
      (not
       (mv-nth
        0
        (las-to-pas (create-canonical-address-list cnt start-rip)
                    :x (cpl x86)
                    x86))))
     (equal (get-prefixes-alt start-rip prefixes cnt x86)
            (get-prefixes-alt (+ 1 start-rip)
                              (!prefixes-slice :group-3-prefix
                                               (mv-nth 1 (rm08 start-rip :x x86))
                                               prefixes)
                              (+ -1 cnt)
                              (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance get-prefixes-opener-lemma-group-3-prefix-in-marking-mode)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes (!prefixes-slice :group-3-prefix
                                                         (mv-nth 1 (rm08 start-rip :x x86))
                                                         prefixes))
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rm08 start-rip :x x86)))))
             :in-theory (e/d* (las-to-pas)
                              (get-prefixes-opener-lemma-group-3-prefix-in-marking-mode
                               rewrite-get-prefixes-to-get-prefixes-alt
                               acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-alt-opener-lemma-group-4-prefix-in-marking-mode
    (implies
     (and
      (canonical-address-p (1+ start-rip))
      (not (zp cnt))
      (equal (prefixes-slice :group-4-prefix prefixes) 0)
      (let*
          ((flg (mv-nth 0 (rm08 start-rip :x x86)))
           (prefix-byte-group-code
            (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
        (and (not flg)
             (equal prefix-byte-group-code 4)))
      (page-structure-marking-mode x86)
      (not (programmer-level-mode x86))
      (canonical-address-p start-rip)
      (disjoint-p
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses x86)))
      (not
       (mv-nth
        0
        (las-to-pas (create-canonical-address-list cnt start-rip)
                    :x (cpl x86)
                    x86))))
     (equal (get-prefixes-alt start-rip prefixes cnt x86)
            (get-prefixes-alt (+ 1 start-rip)
                              (!prefixes-slice :group-4-prefix
                                               (mv-nth 1 (rm08 start-rip :x x86))
                                               prefixes)
                              (+ -1 cnt)
                              (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance get-prefixes-opener-lemma-group-4-prefix-in-marking-mode)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes (!prefixes-slice :group-4-prefix
                                                         (mv-nth 1 (rm08 start-rip :x x86))
                                                         prefixes))
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rm08 start-rip :x x86)))))
             :in-theory (e/d* (las-to-pas)
                              (get-prefixes-opener-lemma-group-4-prefix-in-marking-mode
                               rewrite-get-prefixes-to-get-prefixes-alt
                               acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm xlate-equiv-memory-and-two-mv-nth-0-get-prefixes-alt-cong
    (implies
     (xlate-equiv-memory x86-1 x86-2)
     (equal (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86-1))
            (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-two-get-prefixes-values))
             :in-theory (e/d* (get-prefixes-alt las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-two-mv-nth-1-get-prefixes-alt-cong
    (implies
     (xlate-equiv-memory x86-1 x86-2)
     (equal (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86-1))
            (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-two-get-prefixes-values))
             :in-theory (e/d* (get-prefixes-alt las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-two-mv-nth-2-get-prefixes-alt-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-memory (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86-1))
                                 (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-two-mv-nth-2-get-prefixes))
             :in-theory (e/d* (get-prefixes-alt)
                              (xlate-equiv-memory-and-mv-nth-2-get-prefixes
                               rewrite-get-prefixes-to-get-prefixes-alt))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-mv-nth-2-get-prefixes-alt
    ;; Why do I need both the versions?
    (and
     ;; Matt thinks that this one here acts as a rewrite rule which
     ;; hangs on iff and whose RHS is T.
     (xlate-equiv-memory x86 (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
     ;; Matt thinks that this one acts as a driver rule whose RHS is
     ;; (double-rewrite x86).
     (xlate-equiv-memory (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))
                         (double-rewrite x86)))
    :hints (("Goal"
             :in-theory (e/d* (get-prefixes-alt)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (defthm member-p-start-rip-of-create-canonical-address-list
    ;; This is useful during proofs involving unwinding of
    ;; get-prefixes-alt.
    (implies (and (not (zp cnt))
                  (canonical-address-p start-rip))
             (member-p start-rip (create-canonical-address-list cnt start-rip)))
    :hints (("Goal" :in-theory (e/d* (canonical-address-p member-p) ()))))


  (defthm mv-nth-2-get-prefixes-alt-no-prefix-byte
    ;; Rewrite (mv-nth 2 (get-prefixes-alt ...)) to (mv-nth 2
    ;; (las-to-pas ...)) when no prefix bytes are present and no
    ;; errors are encountered.
    (implies
     (and (let*
              ((flg (mv-nth 0 (rm08 start-rip :x x86)))
               (prefix-byte-group-code
                (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
            (and (not flg)
                 (zp prefix-byte-group-code)))
          (not (zp cnt))
          (not (mv-nth 0
                       (las-to-pas
                        (create-canonical-address-list cnt start-rip)
                        :x (cpl x86) (double-rewrite x86))))
          (disjoint-p
           (mv-nth 1
                   (las-to-pas (create-canonical-address-list cnt start-rip)
                               :x (cpl x86) (double-rewrite x86)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
     (equal (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))
            (mv-nth 2 (las-to-pas (list start-rip) :x (cpl x86) x86))))
    :hints
    (("Goal" :in-theory (e/d* (get-prefixes-alt get-prefixes rm08 las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt)))))

  ;; Interaction between get-prefixes-alt and wb: Proof of
  ;; get-prefixes-alt-and-wb-in-system-level-marking-mode-disjoint-from-paging-structures
  ;; and get-prefixes-alt-and-wb-to-paging-structures follows.

  (encapsulate
    ()

    (local (in-theory (e/d (mv-nth-0-las-to-pas-subset-p)
                           (xlate-equiv-memory-and-mv-nth-1-rm08))))

    (defthm mv-nth-0-rb-and-xw-mem-in-system-level-mode
      (implies (and (disjoint-p
                     (list index)
                     (all-translation-governing-addresses l-addrs (double-rewrite x86)))
                    (canonical-address-listp l-addrs)
                    (physical-address-p index))
               (equal (mv-nth 0 (rb l-addrs r-w-x (xw :mem index value x86)))
                      (mv-nth 0 (rb l-addrs r-w-x x86))))
      :hints (("Goal" :in-theory (e/d* (rb
                                        disjoint-p
                                        las-to-pas)
                                       (force (force))))))

    (defthm read-from-physical-memory-xw-mem
      (implies (disjoint-p (list index) p-addrs)
               (equal (read-from-physical-memory p-addrs (xw :mem index value x86))
                      (read-from-physical-memory p-addrs x86)))
      :hints (("Goal" :in-theory (e/d* (read-from-physical-memory
                                        disjoint-p)
                                       ()))))

    (defthm mv-nth-1-rb-and-xw-mem-in-system-level-mode
      (implies (and
                (disjoint-p
                 (list index)
                 (all-translation-governing-addresses l-addrs (double-rewrite x86)))
                (disjoint-p
                 (list index)
                 (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
                (disjoint-p
                 (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
                 (all-translation-governing-addresses l-addrs (double-rewrite x86)))
                (canonical-address-listp l-addrs)
                (physical-address-p index)
                (not (programmer-level-mode x86)))
               (equal (mv-nth 1 (rb l-addrs r-w-x (xw :mem index value x86)))
                      (mv-nth 1 (rb l-addrs r-w-x x86))))
      :hints (("Goal" :in-theory (e/d* (rb
                                        disjoint-p
                                        las-to-pas)
                                       (xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                        force (force))))))

    (local
     (defthm get-prefixes-xw-mem-values-in-system-level-mode-helper-1
       (implies (and (not (zp cnt))
                     (canonical-address-p start-rip)
                     (canonical-address-p (+ cnt start-rip)))
                (canonical-address-p (+ 1 start-rip)))
       :hints (("Goal" :in-theory (e/d* (canonical-address-p
                                         signed-byte-p)
                                        ())))))
    (local
     (defthmd disjoint-p-all-translation-governing-addresses-and-las-to-pas-subset-p
       ;; Very similar to
       ;; MV-NTH-1-LAS-TO-PAS-SUBSET-P-DISJOINT-FROM-OTHER-P-ADDRS,
       ;; DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P.

       ;; This rule is tailored to rewrite terms of the form

       ;; (disjoint-p (all-translation-governing-addresses l-addrs-subset x86)
       ;;             (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

       ;; where l-addrs-subset is a subset of l-addrs, and l-addrs is of
       ;; the form (create-canonical-address-list ...).

       (implies
        (and
         (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                     'all-translation-governing-addresses 'l-addrs mfc state)
                    (l-addrs))
         ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs))) ; ;
         (disjoint-p
          (all-translation-governing-addresses l-addrs (double-rewrite x86))
          (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))
         (subset-p l-addrs-subset l-addrs)
         (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))))
        (disjoint-p (all-translation-governing-addresses l-addrs-subset x86)
                    (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))))
       :hints
       (("Goal"
         :use ((:instance disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                          (l-addrs l-addrs)
                          (l-addrs-subset l-addrs-subset)
                          (other-p-addrs (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                          (other-p-addrs-subset (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))))))))

    (local
     ;; (show-accumulated-persistence :useless :list)
     (in-theory (e/d* ()
                      ((:rewrite unsigned-byte-p-of-combine-bytes)
                       (:rewrite acl2::ash-0)
                       (:rewrite acl2::zip-open)
                       (:rewrite len-of-rb-in-system-level-mode)
                       (:linear ash-monotone-2)
                       (:rewrite subset-p-cdr-y)
                       (:rewrite default-<-2)
                       (:rewrite negative-logand-to-positive-logand-with-integerp-x)
                       (:meta acl2::cancel_plus-lessp-correct)
                       (:rewrite member-p-canonical-address-listp)
                       (:rewrite bitops::logtail-of-logior)
                       (:definition member-equal)
                       (:type-prescription bitops::logior-natp-type)
                       (:rewrite loghead-of-non-integerp)
                       (:rewrite unsigned-byte-p-of-logior)
                       (:rewrite default-+-2)
                       (:rewrite default-<-1)
                       (:rewrite default-+-1)
                       (:rewrite acl2::ifix-when-not-integerp)
                       (:rewrite bitops::logtail-of-ash)
                       (:linear member-p-pos-value)
                       (:linear member-p-pos-1-value)
                       (:definition byte-listp)
                       (:rewrite default-cdr)
                       (:rewrite bitops::loghead-of-logior)
                       (:rewrite member-p-cdr)
                       (:rewrite unsigned-byte-p-of-logtail)
                       (:rewrite consp-mv-nth-1-las-to-pas)
                       (:rewrite car-mv-nth-1-las-to-pas)
                       (:rewrite default-car)
                       (:rewrite unsigned-byte-p-of-logand-2)
                       (:definition len)
                       (:rewrite bitops::logtail-of-logand)
                       (:type-prescription acl2::|x < y  =>  0 < -x+y|)
                       (:rewrite get-prefixes-opener-lemma-no-prefix-byte)
                       (:rewrite acl2::logtail-identity)
                       (:rewrite acl2::zp-when-gt-0)
                       (:rewrite bitops::logand-with-bitmask)
                       (:linear mv-nth-1-idiv-spec)
                       (:linear mv-nth-1-div-spec)
                       (:type-prescription bitops::logand-natp-type-2)
                       (:rewrite bitops::logsquash-cancel)
                       (:meta acl2::cancel_times-equal-correct)
                       (:meta acl2::cancel_plus-equal-correct)
                       (:rewrite member-p-of-subset-is-member-p-of-superset)
                       (:type-prescription bitops::logtail-natp)
                       (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081)
                       (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090)
                       (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089)
                       (:definition n08p$inline)
                       (:rewrite unsigned-byte-p-of-logand-1)
                       (:rewrite rb-returns-no-error-programmer-level-mode)
                       (:rewrite bitops::loghead-of-logand)
                       (:type-prescription consp-mv-nth-1-las-to-pas)
                       (:type-prescription bitops::logand-natp-type-1)
                       (:rewrite canonical-address-p-limits-thm-2)
                       (:rewrite canonical-address-p-limits-thm-0)
                       (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081)
                       (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093)
                       (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089)
                       (:linear
                        ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones)
                       (:rewrite len-of-rb-in-programmer-level-mode)
                       (:rewrite cdr-mv-nth-1-las-to-pas)
                       (:rewrite rb-returns-byte-listp)
                       (:rewrite bitops::logior-equal-0)
                       (:rewrite ia32e-la-to-pa-in-programmer-level-mode)
                       (:rewrite subset-p-of-nil)
                       (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
                       (:linear acl2::expt->-1)
                       (:type-prescription acl2::logtail-type)
                       (:rewrite canonical-address-p-limits-thm-1)
                       (:type-prescription zip)
                       (:rewrite bitops::loghead-of-logsquash-commute)
                       (:rewrite bitops::associativity-of-logand)
                       (:type-prescription xw)
                       (:rewrite canonical-address-p-limits-thm-3)
                       (:type-prescription true-listp-mv-nth-1-las-to-pas)
                       (:rewrite unsigned-byte-p-of-logsquash)
                       (:linear n52p-mv-nth-1-ia32e-la-to-pa)
                       (:rewrite member-p-of-nil)
                       (:linear bitops::logior-<-0-linear-2)
                       (:rewrite bitops::logsquash-of-0-i)
                       (:linear bitops::logior-<-0-linear-1)
                       (:rewrite mv-nth-1-ia32e-la-to-pa-when-error)
                       (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
                       (:rewrite logand-redundant)
                       (:type-prescription logtail-*2^x-byte-pseudo-page*-of-physical-address)
                       (:rewrite subset-p-cdr-x)
                       (:type-prescription n52p-mv-nth-1-ia32e-la-to-pa)
                       (:linear <=-logior)
                       (:linear n43p-get-prefixes)
                       (:rewrite get-prefixes-opener-lemma-group-4-prefix)
                       (:rewrite get-prefixes-opener-lemma-group-3-prefix)
                       (:rewrite get-prefixes-opener-lemma-group-2-prefix)
                       (:rewrite get-prefixes-opener-lemma-group-1-prefix)
                       (:rewrite unsigned-byte-p-of-ash)
                       (:linear bitops::logior->=-0-linear)
                       (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
                       (:definition n43p$inline)
                       (:rewrite bitops::logtail-of-logtail)
                       (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-mode)
                       (:rewrite mv-nth-1-las-to-pas-when-error)
                       (:rewrite loghead-unequal)
                       (:rewrite bitops::logand-fold-consts)
                       (:rewrite rb-returns-x86-programmer-level-mode)
                       (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
                       (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors)
                       (:rewrite rb-in-terms-of-nth-and-pos-in-system-level-mode)
                       (:rewrite unsigned-byte-p-of-loghead)
                       (:rewrite bitops::signed-byte-p-of-logtail)
                       (:rewrite acl2::distributivity-of-minus-over-+)
                       (:rewrite member-p-and-mult-8-qword-paddr-listp)
                       (:rewrite acl2::natp-posp)
                       (:rewrite bitops::logior-fold-consts)
                       (:rewrite bitops::basic-unsigned-byte-p-of-+)
                       (:rewrite rm-low-64-logand-logior-helper-1)
                       (:rewrite acl2::posp-rw)
                       (:type-prescription member-p-physical-address-p-physical-address-listp)
                       (:type-prescription member-p-physical-address-p)
                       (:definition n64p$inline)
                       (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
                       (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller)
                       (:rewrite bitops::signed-byte-p-monotonicity)
                       (:rewrite default-unary-minus)
                       (:rewrite loghead-ash-0)
                       (:rewrite acl2::expt-with-violated-guards)
                       (:type-prescription bitops::lognot-negp)
                       (:type-prescription all-translation-governing-addresses)
                       (:rewrite acl2::unsigned-byte-p-loghead)
                       (:rewrite bitops::loghead-of-ash-same)
                       (:type-prescription n43p$inline)
                       (:type-prescription ash)
                       (:rewrite bitops::loghead-of-0-i)
                       (:rewrite acl2::equal-constant-+)
                       (:linear acl2::expt-is-increasing-for-base>1)
                       (:linear bitops::upper-bound-of-logior-for-naturals)
                       (:rewrite bitops::logsquash-of-logsquash-2)
                       (:rewrite bitops::logsquash-of-logsquash-1)
                       (:linear n08p-mv-nth-1-rm08)
                       (:type-prescription n64p$inline)
                       (:rewrite bitops::logand-of-logand-self-1)
                       (:type-prescription bitops::lognot-natp)
                       (:type-prescription lognot)
                       (:type-prescription acl2::expt-type-prescription-rationalp)
                       (:linear bitops::expt-2-lower-bound-by-logbitp)
                       (:rewrite acl2::natp-when-gte-0)
                       (:rewrite acl2::natp-when-integerp)
                       (:rewrite acl2::natp-rw)
                       (:type-prescription bitops::part-install-width-low$inline)
                       (:type-prescription bitops::natp-part-install-width-low)))))

    (defthm get-prefixes-xw-mem-in-system-level-mode
      (implies
       (and
        (disjoint-p
         (mv-nth 1 (las-to-pas
                    (create-canonical-address-list cnt start-rip)
                    :x (cpl x86) (double-rewrite x86)))
         (all-translation-governing-addresses
          (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
        (disjoint-p
         (list index)
         (mv-nth 1 (las-to-pas (create-canonical-address-list cnt start-rip)
                               :x (cpl x86) (double-rewrite x86))))
        (disjoint-p
         (list index)
         (all-translation-governing-addresses
          (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
        (not (mv-nth 0 (las-to-pas
                        (create-canonical-address-list cnt start-rip)
                        :x (cpl x86) x86)))
        (posp cnt)
        (canonical-address-p start-rip)
        (canonical-address-p (+ cnt start-rip))
        (physical-address-p index)
        (unsigned-byte-p 8 value)
        (not (programmer-level-mode x86))
        (page-structure-marking-mode x86)
        (x86p x86))
       (and
        (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (xw :mem index value x86)))
               (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
        (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (xw :mem index value x86)))
               (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))
        (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (xw :mem index value x86)))
               (xw :mem index value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))))))
      :hints
      (("Goal"

        :induct (get-prefixes-two-x86-induct-hint
                 start-rip prefixes cnt x86 (xw :mem index value x86))
        :expand ((get-prefixes start-rip prefixes cnt (xw :mem index value x86))
                 (get-prefixes start-rip prefixes cnt x86))
        :in-theory (e/d* (get-prefixes
                          disjoint-p$
                          disjoint-p-all-translation-governing-addresses-and-las-to-pas-subset-p
                          subset-p)
                         (disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                          get-prefixes-alt-opener-lemma-zero-cnt
                          member-p-strip-cars-of-remove-duplicate-keys
                          open-qword-paddr-list-and-member-p
                          unsigned-byte-p
                          xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                          mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                          mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                          infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses
                          r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
                          mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                          xlate-equiv-memory-with-mv-nth-2-las-to-pas
                          las-to-pas-values-and-xw-mem-not-member
                          all-translation-governing-addresses-and-xw-mem-not-member
                          r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
                          xr-programmer-level-mode-mv-nth-2-las-to-pas
                          all-translation-governing-addresses-and-xw-not-mem
                          xr-seg-visible-mv-nth-2-las-to-pas
                          xr-page-structure-marking-mode-mv-nth-2-las-to-pas
                          disjoint-p
                          member-p
                          disjoint-p-cons-1
                          rewrite-get-prefixes-to-get-prefixes-alt
                          create-canonical-address-list
                          xlate-equiv-memory-and-two-get-prefixes-values
                          xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                          rb-xw-values-in-programmer-level-mode
                          bitops::commutativity-2-of-logand
                          mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                          get-prefixes-does-not-modify-x86-state-in-system-level-non-marking-mode
                          get-prefixes-does-not-modify-x86-state-in-programmer-level-mode
                          acl2::zp-open
                          not)))))

    (defthm get-prefixes-and-write-to-physical-memory
      (implies
       (and
        (disjoint-p
         (mv-nth 1
                 (las-to-pas (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) (double-rewrite x86)))
         (all-translation-governing-addresses
          (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
        (disjoint-p
         p-addrs
         (mv-nth
          1
          (las-to-pas (create-canonical-address-list cnt start-rip)
                      :x (cpl x86) (double-rewrite x86))))
        (disjoint-p
         p-addrs
         (all-translation-governing-addresses
          (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
        (not (mv-nth 0 (las-to-pas (create-canonical-address-list cnt start-rip)
                                   :x (cpl x86) x86)))
        (posp cnt)
        (canonical-address-p start-rip)
        (canonical-address-p (+ cnt start-rip))
        (physical-address-listp p-addrs)
        (byte-listp bytes)
        (equal (len p-addrs) (len bytes))
        (not (programmer-level-mode x86))
        (page-structure-marking-mode x86)
        (x86p x86))
       (and
        (equal
         (mv-nth 0 (get-prefixes start-rip prefixes cnt
                                 (write-to-physical-memory p-addrs bytes x86)))
         (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
        (equal
         (mv-nth 1 (get-prefixes start-rip prefixes cnt
                                 (write-to-physical-memory p-addrs bytes x86)))
         (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))
        (equal
         (mv-nth 2 (get-prefixes start-rip prefixes cnt
                                 (write-to-physical-memory p-addrs bytes x86)))
         (write-to-physical-memory p-addrs bytes
                                   (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))))))
      :hints (("Goal"
               :induct (cons (write-to-physical-memory p-addrs bytes x86)
                             (byte-listp bytes))
               :in-theory (e/d* (las-to-pas-values-and-xw-mem-not-member
                                 gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
                                 disjoint-p
                                 byte-listp
                                 n08p
                                 len)
                                (rewrite-get-prefixes-to-get-prefixes-alt
                                 rm08-to-rb
                                 las-to-pas-values-and-write-to-physical-memory-disjoint
                                 get-prefixes-xw-mem-values-in-system-level-mode-helper-1
                                 xlate-equiv-memory-and-two-get-prefixes-values)))))

    (defthm get-prefixes-alt-and-write-to-physical-memory-disjoint-from-paging-structures
      (implies
       (and
        (disjoint-p
         p-addrs
         (mv-nth 1
                 (las-to-pas (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) (double-rewrite x86))))
        (disjoint-p$
         p-addrs
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (posp cnt)
        (canonical-address-p (+ cnt start-rip))
        (physical-address-listp p-addrs)
        (byte-listp bytes)
        (equal (len p-addrs) (len bytes))
        (x86p x86))
       (and
        (equal
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
        (equal
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))
        (equal
         (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
         (write-to-physical-memory p-addrs bytes
                                   (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))))))
      :hints
      (("Goal"
        :do-not-induct t
        :use ((:instance get-prefixes-and-write-to-physical-memory)
              (:instance all-translation-governing-addresses-subset-of-paging-structures
                         (l-addrs (create-canonical-address-list cnt start-rip))))
        :in-theory
        (e/d*
         (get-prefixes-alt
          subset-p
          disjoint-p$
          disjoint-p-commutative
          disjoint-p-subset-p)
         (rewrite-get-prefixes-to-get-prefixes-alt
          get-prefixes-and-write-to-physical-memory
          xlate-equiv-memory-and-two-get-prefixes-values
          mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
          all-translation-governing-addresses-subset-of-paging-structures
          force (force))))))

    (defthm get-prefixes-alt-and-wb-in-system-level-marking-mode-disjoint-from-paging-structures
      (implies
       (and
        (disjoint-p$
         (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
         (mv-nth 1 (las-to-pas
                    (create-canonical-address-list cnt start-rip)
                    :x (cpl x86) (double-rewrite x86))))
        (posp cnt)
        (canonical-address-p (+ cnt start-rip))
        (addr-byte-alistp addr-lst)
        (not (programmer-level-mode x86))
        (x86p x86))
       (and
        (equal
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (mv-nth 1 (wb addr-lst x86))))
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
        (equal
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (mv-nth 1 (wb addr-lst x86))))
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d* (las-to-pas
                                 disjoint-p$
                                 wb
                                 disjoint-p-commutative
                                 infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses
                                 xlate-equiv-memory-with-mv-nth-2-las-to-pas)
                                (rewrite-get-prefixes-to-get-prefixes-alt
                                 xlate-equiv-memory-and-two-get-prefixes-values
                                 xlate-equiv-memory-and-xr-mem-from-rest-of-memory)))))

    (local
     (defthm subset-p-and-open-qword-paddr-list
       (implies (subset-p x y)
                (subset-p (open-qword-paddr-list x) (open-qword-paddr-list y)))
       :hints (("Goal" :in-theory (e/d* (subset-p open-qword-paddr-list) ())))))

    (defthmd disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
      (implies (and
                (equal p-addrs (addr-range 8 index))
                (disjoint-p
                 (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))
                 (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
                (equal (page-size (combine-bytes bytes)) 1)
                (physical-address-p index)
                (equal (loghead 3 index) 0)
                (byte-listp bytes)
                (equal (len bytes) 8)
                (not (programmer-level-mode x86)))
               (disjoint-p
                (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))
                (open-qword-paddr-list
                 (gather-all-paging-structure-qword-addresses
                  (write-to-physical-memory p-addrs bytes x86)))))
      :hints (("Goal"
               :use ((:instance gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p)
                     (:instance disjoint-p-subset-p
                                (x (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                                (y (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
                                (a (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                                (b (open-qword-paddr-list
                                    (gather-all-paging-structure-qword-addresses (write-to-physical-memory p-addrs bytes x86))))))
               :in-theory (e/d* (subset-p
                                 subset-p-reflexive)
                                (disjoint-p-subset-p
                                 gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p)))))

    (defthm get-prefixes-alt-and-write-to-physical-memory-paging-structures
      (implies
       (and
        (equal p-addrs (addr-range 8 index))
        (disjoint-p
         (mv-nth 1
                 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (disjoint-p
         p-addrs
         (mv-nth 1
                 (las-to-pas (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) (double-rewrite x86))))
        (disjoint-p$
         p-addrs
         (all-translation-governing-addresses
          (create-canonical-address-list cnt start-rip)
          (double-rewrite x86)))
        (equal (page-size (combine-bytes bytes)) 1)
        (posp cnt)
        (canonical-address-p (+ cnt start-rip))
        (physical-address-listp p-addrs)
        (byte-listp bytes)
        (equal (len bytes) 8)
        (physical-address-p index)
        (equal (loghead 3 index) 0)
        (x86p x86))
       (and
        (equal
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
        (equal
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))
        (equal
         (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
         (write-to-physical-memory p-addrs bytes
                                   (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))))))
      :hints
      (("Goal"
        :do-not-induct t
        :use ((:instance get-prefixes-and-write-to-physical-memory)
              (:instance all-translation-governing-addresses-subset-of-paging-structures
                         (l-addrs (create-canonical-address-list cnt start-rip)))
              (:instance disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
                         (index index)
                         (cpl (cpl x86))
                         (p-addrs (addr-range 8 index))
                         (l-addrs (create-canonical-address-list cnt start-rip))
                         (r-w-x :x)))
        :in-theory
        (e/d*
         (get-prefixes-alt
          subset-p
          disjoint-p$
          disjoint-p-subset-p)
         (disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
          rewrite-get-prefixes-to-get-prefixes-alt
          get-prefixes-and-write-to-physical-memory
          xlate-equiv-memory-and-two-get-prefixes-values
          mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
          all-translation-governing-addresses-subset-of-paging-structures
          force (force))))))

    (defthm get-prefixes-alt-and-wb-to-paging-structures
      (implies
       (and
        (equal (page-size value) 1)
        (direct-map-p 8 lin-addr :w (cpl x86) (double-rewrite x86))
        (disjoint-p
         (mv-nth 1
                 (las-to-pas (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                               :w (cpl x86) (double-rewrite x86)))
         (all-translation-governing-addresses
          (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
        (disjoint-p
         (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                               :w (cpl x86) (double-rewrite x86)))
         (mv-nth 1 (las-to-pas
                    (create-canonical-address-list cnt start-rip)
                    :x (cpl x86) (double-rewrite x86))))
        (posp cnt)
        (canonical-address-p (+ cnt start-rip))
        (physical-address-p lin-addr)
        (equal (loghead 3 lin-addr) 0)
        (canonical-address-p lin-addr)
        (unsigned-byte-p 64 value)
        (not (programmer-level-mode x86))
        (x86p x86))
       (and
        (equal
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt
                                     (mv-nth 1 (wb
                                                (create-addr-bytes-alist
                                                 (create-canonical-address-list 8 lin-addr)
                                                 (byte-ify 8 value))
                                                x86))))
         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
        (equal
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt
                                     (mv-nth 1 (wb
                                                (create-addr-bytes-alist
                                                 (create-canonical-address-list 8 lin-addr)
                                                 (byte-ify 8 value))
                                                x86))))
         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance get-prefixes-alt-and-write-to-physical-memory-paging-structures
                                (index lin-addr)
                                (p-addrs (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                               :w (cpl x86) x86)))
                                (bytes (byte-ify 8 value))
                                (x86 (mv-nth 2 (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                           :w (cpl x86) x86)))))
               :in-theory (e/d* (direct-map-p
                                 get-prefixes-alt-and-write-to-physical-memory-paging-structures
                                 las-to-pas
                                 acl2::loghead-identity
                                 acl2::fold-consts-in-+
                                 disjoint-p$
                                 wb
                                 infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses
                                 xlate-equiv-memory-with-mv-nth-2-las-to-pas)
                                (rewrite-get-prefixes-to-get-prefixes-alt
                                 mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt
                                 subset-p
                                 mv-nth-0-las-to-pas-subset-p
                                 mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                                 xlate-equiv-memory-and-two-get-prefixes-values
                                 xlate-equiv-memory-and-xr-mem-from-rest-of-memory)))))))

;; ======================================================================

(defsection program-at-alt
  :parents (marking-mode-top)

  ;; Note that unlike rb-alt and get-prefixes-alt, we need to use
  ;; disjoint-p$ for program-at-alt instead of disjoint-p.
  (local (in-theory (e/d (disjoint-p$) ())))

  (define program-at-alt ((l-addrs canonical-address-listp)
                          (bytes byte-listp)
                          (x86))
    :non-executable t
    (if (and (page-structure-marking-mode x86)
             (not (programmer-level-mode x86))
             (canonical-address-listp l-addrs)
             (not (mv-nth 0 (las-to-pas l-addrs :x (cpl x86) x86)))
             (disjoint-p$ (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) x86))
                          (open-qword-paddr-list
                           (gather-all-paging-structure-qword-addresses x86))))

        (program-at l-addrs bytes x86)

      nil))

  (defthm rewrite-program-at-to-program-at-alt
    (implies (forced-and
              (disjoint-p$
               (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (not (mv-nth 0 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86))))
              (canonical-address-listp l-addrs)
              (page-structure-marking-mode x86)
              (not (programmer-level-mode x86)))
             (equal (program-at l-addrs bytes x86)
                    (program-at-alt l-addrs bytes (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (program-at-alt) ()))))

  (defthm program-at-alt-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (program-at-alt l-addrs bytes x86-1)
                    (program-at-alt l-addrs bytes x86-2)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                              (r-w-x :x)))
             :in-theory (e/d* (program-at-alt
                               program-at)
                              (rewrite-program-at-to-program-at-alt
                               mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                               force (force)))))
    :rule-classes :congruence)

  (defthm program-at-alt-wb-disjoint-in-system-level-mode
    (implies
     (and
      (disjoint-p$
       (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
       (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86))))
      (disjoint-p$
       (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (addr-byte-alistp addr-lst)
      (x86p x86))
     (equal (program-at-alt l-addrs bytes (mv-nth 1 (wb addr-lst x86)))
            (program-at-alt l-addrs bytes (double-rewrite x86))))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance program-at-wb-disjoint-in-system-level-mode))
      :in-theory
      (e/d
       (program-at-alt
        disjoint-p-commutative)
       (rewrite-program-at-to-program-at-alt
        program-at-wb-disjoint-in-system-level-mode
        rb-wb-disjoint-in-system-level-mode
        disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
        mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
        rb wb)))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault
            :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'program-at-alt
    (acl2::formals 'program-at (w state))
    ;; :hyps '(not (programmer-level-mode x86))
    :prepwork '((local (in-theory (e/d (program-at-alt)
                                       (rewrite-program-at-to-program-at-alt)))))
    :double-rewrite? t))

  (defthm program-at-alt-!flgi
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (program-at-alt l-addrs bytes (!flgi index value x86))
                    (program-at-alt l-addrs bytes (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (program-at-alt)
                                     (rewrite-program-at-to-program-at-alt)))))

  (defthm program-at-alt-after-mv-nth-2-rb
    (implies
     (and
      (not (programmer-level-mode x86))
      (not (mv-nth 0 (las-to-pas l-addrs-2 r-w-x-2 (cpl x86) (double-rewrite x86)))))
     (equal (program-at-alt l-addrs-1 bytes-1
                            (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86)))
            (program-at-alt l-addrs-1 bytes-1 (double-rewrite x86))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (program-at-alt
                               program-at)
                              (rewrite-program-at-to-program-at-alt
                               force (force)))))))

;; ======================================================================

(defsection rb-alt
  :parents (marking-mode-top)

  :long "<p>rb-alt is defined basically to read the program bytes from
 the memory. I don't intend to use it to read paging data
 structures.</p>"

  (define rb-alt ((l-addrs canonical-address-listp)
                  (r-w-x :type (member :r :w :x))
                  (x86))
    :non-executable t
    (if (and (page-structure-marking-mode x86)
             (not (programmer-level-mode x86))
             (canonical-address-listp l-addrs)
             (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
             ;; (disjoint-p (all-translation-governing-addresses l-addrs x86)
             ;;             (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
             (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) x86))
                         (open-qword-paddr-list
                          (gather-all-paging-structure-qword-addresses x86))))

        (rb l-addrs r-w-x x86)

      (mv nil nil x86))

    ///

    (defthm rb-alt-returns-byte-listp
      (implies (x86p x86)
               (byte-listp (mv-nth 1 (rb-alt addresses r-w-x x86))))
      :rule-classes (:rewrite :type-prescription))

    (defthm rb-alt-returns-x86p
      (implies (force (x86p x86))
               (x86p (mv-nth 2 (rb-alt l-addrs r-w-x x86)))))

    (defthm rb-alt-nil-lemma
      (equal (mv-nth 1 (rb-alt nil r-w-x x86))
             nil)
      :hints (("Goal"
               :cases ((and (page-structure-marking-mode x86)
                            (not (programmer-level-mode x86))
                            (not (mv-nth 0 (las-to-pas nil r-w-x (cpl x86) x86)))))
               :in-theory (e/d* () (force (force))))))


    (make-event
     (generate-xr-over-write-thms
      (remove-elements-from-list
       '(:mem :fault)
       *x86-field-names-as-keywords*)
      'rb-alt
      (acl2::formals 'rb-alt (w state))
      :output-index 2
      :prepwork '((local (in-theory (e/d () (force (force))))))))

    (defthm xr-fault-rb-alt-state-in-system-level-mode
      (equal (xr :fault index (mv-nth 2 (rb-alt l-addrs r-w-x x86)))
             (xr :fault index x86))
      :hints (("Goal" :in-theory (e/d* (rb-alt
                                        las-to-pas)
                                       (force (force))))))

    (defthm mv-nth-0-rb-alt-is-nil
      (equal (mv-nth 0 (rb-alt l-addrs r-w-x x86)) nil)
      :hints (("Goal"
               :use ((:instance mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode))
               :in-theory (e/d* ()
                                (mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode
                                 force (force))))))

    (make-event
     (generate-read-fn-over-xw-thms
      (remove-elements-from-list
       '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
       *x86-field-names-as-keywords*)
      'rb-alt
      (acl2::formals 'rb-alt (w state))
      :output-index 0
      :double-rewrite? t))

    (make-event
     (generate-read-fn-over-xw-thms
      (remove-elements-from-list
       '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
       *x86-field-names-as-keywords*)
      'rb-alt
      (acl2::formals 'rb-alt (w state))
      :output-index 1
      :double-rewrite? t))

    (defthm rb-alt-xw-rflags-not-ac-values-in-system-level-mode
      (implies (equal (rflags-slice :ac value)
                      (rflags-slice :ac (rflags x86)))
               (and (equal (mv-nth 0 (rb-alt addr r-w-x (xw :rflags 0 value x86)))
                           (mv-nth 0 (rb-alt addr r-w-x x86)))
                    (equal (mv-nth 1 (rb-alt addr r-w-x (xw :rflags 0 value x86)))
                           (mv-nth 1 (rb-alt addr r-w-x x86)))))
      :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (make-event
     (generate-write-fn-over-xw-thms
      (remove-elements-from-list
       '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
       *x86-field-names-as-keywords*)
      'rb-alt
      (acl2::formals 'rb-alt (w state))
      :output-index 2
      :prepwork '((local (in-theory (e/d* () (force (force))))))))

    (defthm rb-alt-xw-rflags-not-ac-state-in-system-level-mode
      (implies (equal (rflags-slice :ac value)
                      (rflags-slice :ac (rflags x86)))
               (equal (mv-nth 2 (rb-alt addr r-w-x (xw :rflags 0 value x86)))
                      (xw :rflags 0 value (mv-nth 2 (rb-alt addr r-w-x x86)))))
      :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm rb-alt-values-and-!flgi-in-system-level-mode
      (implies (and (not (equal index *ac*))
                    (x86p x86))
               (and (equal (mv-nth 0 (rb-alt l-addrs r-w-x (!flgi index value x86)))
                           (mv-nth 0 (rb-alt l-addrs r-w-x (double-rewrite x86))))
                    (equal (mv-nth 1 (rb-alt l-addrs r-w-x (!flgi index value x86)))
                           (mv-nth 1 (rb-alt l-addrs r-w-x (double-rewrite x86))))))
      :hints (("Goal" :do-not-induct t
               :in-theory (e/d* () (force (force))))))

    (defthm rb-alt-and-!flgi-state-in-system-level-mode
      (implies (and (not (equal index *ac*))
                    (x86p x86))
               (equal (mv-nth 2 (rb-alt lin-addr r-w-x (!flgi index value x86)))
                      (!flgi index value (mv-nth 2 (rb-alt lin-addr r-w-x x86)))))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d* ()
                                (force (force))))))

    (defthm flgi-and-mv-nth-2-rb-alt
      (equal (flgi index (mv-nth 2 (rb-alt l-addrs r-w-x x86)))
             (flgi index x86))
      :hints (("Goal" :in-theory (e/d* (flgi) ()))))

    (defthm alignment-checking-enabled-p-and-mv-nth-2-rb-alt
      (equal (alignment-checking-enabled-p (mv-nth 2 (rb-alt l-addrs r-w-x x86)))
             (alignment-checking-enabled-p x86))
      :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p flgi) ()))))

    (defthm mv-nth-2-rb-alt-in-system-level-marking-mode
      (implies
       (and (not (programmer-level-mode x86))
            (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
            (canonical-address-listp l-addrs)
            (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
                        (open-qword-paddr-list
                         (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
       (equal (mv-nth 2 (rb-alt l-addrs r-w-x x86))
              (mv-nth 2 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))))
      :hints (("Goal" :do-not-induct t
               :in-theory (e/d* () (force (force)))))))

  ;; Note that in the lemmas below, we use program-at-alt instead of
  ;; program-at.

  ;; Rewrite rb to rb-alt:

  (defthm rewrite-rb-to-rb-alt
    ;; Note that the hyps here aren't forced --- this is because we
    ;; don't always want rb to rewrite to rb-alt. E.g., when we're
    ;; reading from the paging data structures, we want to reason
    ;; about rb.
    (implies (and
              (disjoint-p
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
              (canonical-address-listp l-addrs)
              (page-structure-marking-mode x86)
              (not (programmer-level-mode x86)))
             (equal (rb l-addrs r-w-x x86)
                    (rb-alt l-addrs r-w-x (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) ()))))

  ;; rb-alt and xlate-equiv-memory:

  (defthm mv-nth-0-rb-alt-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rb-alt l-addrs r-w-x x86-1))
                    (mv-nth 0 (rb-alt l-addrs r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force)))))
    :rule-classes :congruence)

  (defthm mv-nth-1-rb-alt-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 1 (rb-alt l-addrs r-w-x x86-1))
                    (mv-nth 1 (rb-alt l-addrs r-w-x x86-2))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures))
             :in-theory (e/d* (rb-alt)
                              (mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                               rewrite-rb-to-rb-alt
                               force (force)))))
    :rule-classes :congruence)

  (defthm mv-nth-2-rb-alt-and-xlate-equiv-memory
    (and (xlate-equiv-memory (mv-nth 2 (rb-alt l-addrs r-w-x x86)) (double-rewrite x86))
         (xlate-equiv-memory x86 (mv-nth 2 (rb-alt l-addrs r-w-x x86))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force))))))

  (defthm xlate-equiv-memory-and-two-mv-nth-2-rb-alt-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-memory (mv-nth 2 (rb-alt l-addrs r-w-x x86-1))
                                 (mv-nth 2 (rb-alt l-addrs r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt))
             :use ((:instance xlate-equiv-memory-and-two-mv-nth-2-rb))))
    :rule-classes :congruence)

  (defthm rb-alt-in-terms-of-nth-and-pos-in-system-level-mode
    (implies (and (bind-free (find-info-from-program-at-term
                              'rb-alt-in-terms-of-nth-and-pos-in-system-level-mode
                              mfc state)
                             (n prog-addr bytes))
                  (program-at-alt
                   (create-canonical-address-list n prog-addr)
                   bytes x86)
                  (syntaxp (quotep n))
                  (member-p lin-addr (create-canonical-address-list n prog-addr))
                  (not (mv-nth 0
                               (las-to-pas (create-canonical-address-list n prog-addr)
                                           :x (cpl x86)
                                           (double-rewrite x86))))
                  (disjoint-p$
                   (mv-nth 1
                           (las-to-pas (create-canonical-address-list n prog-addr)
                                       :x (cpl x86)
                                       (double-rewrite x86)))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
                  (page-structure-marking-mode x86)
                  (not (xr :programmer-level-mode 0 x86))
                  (x86p x86))
             (equal (car (mv-nth 1 (rb-alt (list lin-addr) :x x86)))
                    (nth (pos lin-addr (create-canonical-address-list n prog-addr)) bytes)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (las-to-pas
                              subset-p
                              disjoint-p
                              disjoint-p$
                              disjoint-p-commutative)
                             (acl2::mv-nth-cons-meta
                              rb-in-terms-of-nth-and-pos-in-system-level-mode
                              rewrite-rb-to-rb-alt
                              disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p))
             :use ((:instance rewrite-rb-to-rb-alt
                              (l-addrs (list lin-addr))
                              (r-w-x :x))
                   (:instance rb-in-terms-of-nth-and-pos-in-system-level-mode)))))

  (defthm rb-alt-in-terms-of-rb-alt-subset-p-in-system-level-mode
    (implies
     (and
      (bind-free (find-info-from-program-at-term
                  'rb-alt-in-terms-of-rb-alt-subset-p-in-system-level-mode
                  mfc state)
                 (n prog-addr bytes))
      (program-at-alt (create-canonical-address-list n prog-addr) bytes x86)
      (subset-p l-addrs (create-canonical-address-list n prog-addr))
      (syntaxp (quotep n))
      (consp l-addrs)
      (not (mv-nth 0
                   (las-to-pas (create-canonical-address-list n prog-addr)
                               :x (cpl x86) (double-rewrite x86))))
      (disjoint-p$
       (mv-nth 1
               (las-to-pas (create-canonical-address-list n prog-addr)
                           :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (page-structure-marking-mode x86)
      (not (programmer-level-mode x86))
      (x86p x86))
     (equal (mv-nth 1 (rb-alt l-addrs :x x86))
            (append (list (nth (pos
                                (car l-addrs)
                                (create-canonical-address-list n prog-addr))
                               bytes))
                    (mv-nth 1 (rb-alt (cdr l-addrs) :x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (las-to-pas
                              subset-p
                              disjoint-p
                              disjoint-p$
                              disjoint-p-commutative)
                             (rb-in-terms-of-rb-subset-p-in-system-level-mode
                              rewrite-rb-to-rb-alt
                              acl2::mv-nth-cons-meta
                              disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p))
             :use ((:instance rb-in-terms-of-rb-subset-p-in-system-level-mode)
                   (:instance rewrite-rb-to-rb-alt
                              (r-w-x :x))
                   (:instance rewrite-rb-to-rb-alt
                              (l-addrs (cdr l-addrs))
                              (r-w-x :x))))))

  (defthmd rb-alt-wb-equal-in-system-level-mode
    (implies (and (equal
                   ;; The physical addresses pertaining to the read
                   ;; operation are equal to those pertaining to the
                   ;; write operation.
                   (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
                   (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
                  ;; The following should be directly present as a
                  ;; hypothesis of the effects theorem for programs.
                  ;; That's why it's in terms of disjoint-p$ instead
                  ;; of disjoint-p.
                  (disjoint-p$
                   ;; The physical addresses pertaining to the write are
                   ;; disjoint from the translation-governing-addresses
                   ;; pertaining to the read.
                   (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
                   (open-qword-paddr-list (gather-all-paging-structure-qword-addresses
                                           (double-rewrite x86))))
                  (no-duplicates-p
                   (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
                  (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
                  (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
                  (canonical-address-listp l-addrs)
                  (addr-byte-alistp addr-lst)
                  (page-structure-marking-mode x86)
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (mv-nth 1 (rb-alt l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                    (strip-cdrs addr-lst)))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d* (las-to-pas
                               disjoint-p$
                               disjoint-p-commutative)
                              (rewrite-rb-to-rb-alt
                               disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                               force (force)))
             :use ((:instance rewrite-rb-to-rb-alt
                              (x86 (mv-nth 1 (wb addr-lst x86))))
                   (:instance rb-wb-equal-in-system-level-mode)))))

  (defthm rb-alt-wb-disjoint-in-system-level-mode
    (implies (and
              (disjoint-p
               ;; The physical addresses pertaining to the write
               ;; operation are disjoint from those pertaining to the
               ;; read operation.
               (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
              ;; We use disjoint-p for reads and disjoint-p$ for
              ;; writes, because l-addrs can be a subset of program
              ;; addresses and hence, unlike (strip-cars addr-lst),
              ;; the following hyp won't be directly present as a hyp
              ;; of a program's effects theorem.  It'll instead be in
              ;; terms of the superset of l-addrs.
              (disjoint-p
               ;; The physical addresses pertaining to the read are
               ;; disjoint from the physical addresses of the paging
               ;; structures.
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list (gather-all-paging-structure-qword-addresses
                                       (double-rewrite x86))))
              (disjoint-p$
               ;; The physical addresses pertaining to the write are
               ;; disjoint from the physical addresses of the paging
               ;; structures.
               (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
              (canonical-address-listp l-addrs)
              (addr-byte-alistp addr-lst)
              (page-structure-marking-mode x86)
              (not (programmer-level-mode x86))
              (x86p x86))
             (and
              (equal (mv-nth 0 (rb-alt l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                     (mv-nth 0 (rb-alt l-addrs r-w-x (double-rewrite x86))))
              (equal (mv-nth 1 (rb-alt l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                     (mv-nth 1 (rb-alt l-addrs r-w-x (double-rewrite x86))))))
    :hints (("Goal" :do-not-induct t
             :use ((:instance rewrite-rb-to-rb-alt
                              (x86 (mv-nth 1 (wb addr-lst x86))))
                   (:instance rewrite-rb-to-rb-alt)
                   (:instance rb-wb-disjoint-in-system-level-mode))
             :in-theory (e/d* (disjoint-p-commutative
                               disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               rb-wb-disjoint-in-system-level-mode
                               disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)))))

  (defthm disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures
    ;; Note that r-w-x = :x here -- this rule applies during
    ;; instruction fetches.
    (implies (and
              (bind-free
               (find-l-addrs-from-program-at-or-program-at-alt-term
                'infer-disjointness 'l-addrs mfc state)
               (l-addrs))
              ;; The equality of
              ;; gather-all-paging-structure-qword-addresses and
              ;; las-to-pas with x86-1 and x86-2 are better than the
              ;; xlate-equiv-memory hyp because x86-2 may contain wb
              ;; terms, which don't preserve xlate-equiv-memory relation
              ;; on the x86 states.
              ;; (xlate-equiv-memory (double-rewrite x86-1) (double-rewrite x86-2))
              (equal
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
              (equal (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86-1)))
                     (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86-2))))
              (equal (page-size value) 1)
              (direct-map-p 8 lin-addr :w (cpl x86-2) (double-rewrite x86-2))
              (disjoint-p$
               (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86-1)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
              (subset-p l-addrs-subset l-addrs)
              (not (mv-nth 0 (las-to-pas l-addrs :x cpl (double-rewrite x86-1))))
              (physical-address-p lin-addr)
              (equal (loghead 3 lin-addr) 0)
              (canonical-address-p lin-addr)
              (unsigned-byte-p 64 value)
              (not (programmer-level-mode x86-2)))
             (disjoint-p
              (mv-nth 1 (las-to-pas l-addrs-subset :x cpl x86-1))
              (open-qword-paddr-list
               (gather-all-paging-structure-qword-addresses
                (mv-nth 1 (wb (create-addr-bytes-alist
                               (create-canonical-address-list 8 lin-addr)
                               (byte-ify 8 value))
                              x86-2))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
                              (p-addrs (addr-range 8 lin-addr))
                              (r-w-x :x)
                              (index lin-addr)
                              (bytes (byte-ify 8 value))
                              (x86 (mv-nth 2
                                           (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                       :w (cpl x86-2) x86-2))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1)))
                              (a (mv-nth 1 (las-to-pas l-addrs-subset :x cpl x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 lin-addr)
                                    (byte-ify 8 value)
                                    (mv-nth 2
                                            (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                        :w (cpl x86-2)
                                                        x86-2))))))
                              (a (mv-nth 1 (las-to-pas l-addrs-subset :x cpl x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 lin-addr)
                                    (byte-ify 8 value)
                                    (mv-nth 2
                                            (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                        :w (cpl x86-2)
                                                        x86-2))))))))
             :in-theory (e/d* (disjoint-p$
                               subset-p
                               subset-p-reflexive
                               wb
                               direct-map-p)
                              (disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures)))))

  (defthmd disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures-general
    (implies (and
              ;; The equality of
              ;; gather-all-paging-structure-qword-addresses and
              ;; las-to-pas with x86-1 and x86-2 are better than the
              ;; xlate-equiv-memory hyp because x86-2 may contain wb
              ;; terms, which don't preserve xlate-equiv-memory relation
              ;; on the x86 states.
              ;; (xlate-equiv-memory (double-rewrite x86-1) (double-rewrite x86-2))
              (equal
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
              (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1)))
                     (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-2))))
              (equal (page-size value) 1)
              (direct-map-p 8 lin-addr :w (cpl x86-2) (double-rewrite x86-2))
              (disjoint-p$
               (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
              (subset-p l-addrs-subset l-addrs)
              (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1))))
              (physical-address-p lin-addr)
              (equal (loghead 3 lin-addr) 0)
              (canonical-address-p lin-addr)
              (unsigned-byte-p 64 value)
              (not (programmer-level-mode x86-2)))
             (disjoint-p
              (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86-1))
              (open-qword-paddr-list
               (gather-all-paging-structure-qword-addresses
                (mv-nth 1 (wb (create-addr-bytes-alist
                               (create-canonical-address-list 8 lin-addr)
                               (byte-ify 8 value))
                              x86-2))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
                              (p-addrs (addr-range 8 lin-addr))
                              (r-w-x r-w-x)
                              (index lin-addr)
                              (bytes (byte-ify 8 value))
                              (x86 (mv-nth 2
                                           (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                       :w (cpl x86-2) x86-2))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1)))
                              (a (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 lin-addr)
                                    (byte-ify 8 value)
                                    (mv-nth 2
                                            (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                        :w (cpl x86-2)
                                                        x86-2))))))
                              (a (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 lin-addr)
                                    (byte-ify 8 value)
                                    (mv-nth 2
                                            (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                        :w (cpl x86-2)
                                                        x86-2))))))))
             :in-theory (e/d* (disjoint-p$
                               subset-p
                               subset-p-reflexive
                               wb
                               direct-map-p)
                              (disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures)))))

  (defthm rb-alt-and-wb-to-paging-structures-disjoint
    (implies (and
              (equal (page-size value) 1)
              (direct-map-p 8 lin-addr :w (cpl x86) (double-rewrite x86))
              (disjoint-p
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (disjoint-p
               (mv-nth 1 (las-to-pas
                          (create-canonical-address-list 8 lin-addr)
                          :w (cpl x86) (double-rewrite x86)))
               (all-translation-governing-addresses l-addrs (double-rewrite x86)))
              (disjoint-p
               (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                                     :w (cpl x86) (double-rewrite x86)))
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
              (physical-address-p lin-addr)
              (equal (loghead 3 lin-addr) 0)
              (canonical-address-p lin-addr)
              (unsigned-byte-p 64 value)
              (x86p x86))
             (and
              (equal (mv-nth 0 (rb-alt l-addrs r-w-x
                                       (mv-nth 1 (wb
                                                  (create-addr-bytes-alist
                                                   (create-canonical-address-list 8 lin-addr)
                                                   (byte-ify 8 value)) x86))))
                     (mv-nth 0 (rb-alt l-addrs r-w-x (double-rewrite x86))))
              (equal (mv-nth 1 (rb-alt l-addrs r-w-x
                                       (mv-nth 1 (wb
                                                  (create-addr-bytes-alist
                                                   (create-canonical-address-list 8 lin-addr)
                                                   (byte-ify 8 value)) x86))))
                     (mv-nth 1 (rb-alt l-addrs r-w-x (double-rewrite x86))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures-general
                              (l-addrs-subset l-addrs)
                              (cpl (cpl x86))
                              (x86-1 x86)
                              (x86-2 x86)))
             :in-theory (e/d* (disjoint-p$
                               subset-p
                               subset-p-reflexive
                               rb-alt)
                              (rewrite-rb-to-rb-alt))))))

;; ======================================================================

;; Step function opener lemma:

(defthm x86-fetch-decode-execute-opener-in-marking-mode
  ;; Note that we use get-prefixes-alt here instead of get-prefixes.
  (implies (and
            ;; Start: binding hypotheses.
            (equal start-rip (rip x86))
            ;; get-prefixes-alt:
            (equal three-vals-of-get-prefixes (get-prefixes-alt start-rip 0 5 x86))
            (equal flg-get-prefixes (mv-nth 0 three-vals-of-get-prefixes))
            (equal prefixes (mv-nth 1 three-vals-of-get-prefixes))
            (equal x86-1 (mv-nth 2 three-vals-of-get-prefixes))

            (equal opcode/rex/escape-byte (prefixes-slice :next-byte prefixes))
            (equal prefix-length (prefixes-slice :num-prefixes prefixes))
            (equal temp-rip0 (if (equal prefix-length 0)
                                 (+ 1 start-rip)
                               (+ prefix-length start-rip 1)))
            (equal rex-byte (if (equal (ash opcode/rex/escape-byte -4) 4)
                                opcode/rex/escape-byte
                              0))

            ;; opcode/escape-byte:
            (equal three-vals-of-opcode/escape-byte
                   (if (equal rex-byte 0)
                       (mv nil opcode/rex/escape-byte x86-1)
                     (rm08 temp-rip0 :x x86-1)))
            (equal flg-opcode/escape-byte (mv-nth 0 three-vals-of-opcode/escape-byte))
            (equal opcode/escape-byte (mv-nth 1 three-vals-of-opcode/escape-byte))
            (equal x86-2 (mv-nth 2 three-vals-of-opcode/escape-byte))

            (equal temp-rip1 (if (equal rex-byte 0) temp-rip0 (1+ temp-rip0)))
            (equal modr/m? (x86-one-byte-opcode-modr/m-p opcode/escape-byte))

            ;; modr/m byte:
            (equal three-vals-of-modr/m
                   (if modr/m? (rm08 temp-rip1 :x x86-2) (mv nil 0 x86-2)))
            (equal flg-modr/m (mv-nth 0 three-vals-of-modr/m))
            (equal modr/m (mv-nth 1 three-vals-of-modr/m))
            (equal x86-3 (mv-nth 2 three-vals-of-modr/m))

            (equal temp-rip2 (if modr/m? (1+ temp-rip1) temp-rip1))
            (equal sib? (and modr/m? (x86-decode-sib-p modr/m)))

            ;; sib byte:
            (equal three-vals-of-sib
                   (if sib? (rm08 temp-rip2 :x x86-3) (mv nil 0 x86-3)))
            (equal flg-sib (mv-nth 0 three-vals-of-sib))
            (equal sib (mv-nth 1 three-vals-of-sib))
            (equal x86-4 (mv-nth 2 three-vals-of-sib))

            (equal temp-rip3 (if sib? (1+ temp-rip2) temp-rip2))
            ;; End: binding hypotheses.

            (page-structure-marking-mode x86)
            (not (programmer-level-mode x86))
            (not (ms x86))
            (not (fault x86))
            (x86p x86)
            (double-rewrite (not flg-get-prefixes))
            ;; !!! Add double-rewrite after monitoring this theorem...
            (double-rewrite (canonical-address-p temp-rip0))
            (double-rewrite
             (if (and (equal prefix-length 0)
                      (equal rex-byte 0)
                      (not modr/m?))
                 ;; One byte instruction --- all we need to know is that
                 ;; the new RIP is canonical, not that there's no error
                 ;; in reading a value from that address.
                 t
               (not flg-opcode/escape-byte)))
            ;; !!! Add double-rewrite after monitoring this theorem...
            (double-rewrite
             (if (equal rex-byte 0)
                 t
               (canonical-address-p temp-rip1)))
            (double-rewrite
             (if  modr/m?
                 (and (canonical-address-p temp-rip2)
                      (not flg-modr/m))
               t))
            (double-rewrite
             (if sib?
                 (and (canonical-address-p temp-rip3)
                      (not flg-sib))
               t))

            ;; For get-prefixes-alt (we wouldn't need these hyps if we
            ;; used get-prefixes):

            (disjoint-p
             (mv-nth
              1
              (las-to-pas
               (create-canonical-address-list 5 (xr :rip 0 x86))
               :x (cpl x86) (double-rewrite x86)))
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
            (not
             (mv-nth
              0
              (las-to-pas
               (create-canonical-address-list 5 (xr :rip 0 x86))
               :x (cpl x86) (double-rewrite x86)))))
           (equal (x86-fetch-decode-execute x86)
                  (top-level-opcode-execute
                   start-rip temp-rip3 prefixes rex-byte opcode/escape-byte modr/m sib x86-4)))
  :hints (("Goal"
           :do-not '(preprocess)
           :in-theory (e/d (x86-fetch-decode-execute
                            get-prefixes-alt)
                           (rewrite-get-prefixes-to-get-prefixes-alt
                            top-level-opcode-execute
                            xlate-equiv-memory-and-mv-nth-0-rm08-cong
                            xlate-equiv-memory-and-two-mv-nth-2-rm08-cong
                            xlate-equiv-memory-and-mv-nth-2-rm08
                            signed-byte-p
                            not
                            member-equal
                            mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                            remove-duplicates-equal
                            combine-bytes
                            byte-listp
                            acl2::ash-0
                            open-qword-paddr-list
                            cdr-mv-nth-1-las-to-pas
                            unsigned-byte-p-of-combine-bytes
                            get-prefixes-opener-lemma-no-prefix-byte
                            get-prefixes-opener-lemma-group-1-prefix-in-marking-mode
                            get-prefixes-opener-lemma-group-2-prefix-in-marking-mode
                            get-prefixes-opener-lemma-group-3-prefix-in-marking-mode
                            get-prefixes-opener-lemma-group-4-prefix-in-marking-mode
                            mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode
                            mv-nth-2-rb-in-system-level-marking-mode
                            (force) force)))))

;; ======================================================================
