;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; This is the top-level book to include when reasoning about code in
;; the system-level mode.

(include-book "physical-memory-utils" :ttags :all)
(include-book "paging-lib/paging-top" :ttags :all)
(include-book "normalize-memory-accesses" :ttags :all)

;; TO-DO: Uncomment the following once the alternative versions of
;; get-prefixes, x86-fetch-decode-execute, and x86-run are defined.
;; (include-book "x86-alt" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

;; Get-prefixes lemmas in the system-level mode:

(define get-prefixes-and-xlate-equiv-x86s-ind-hint
  ((start-rip :type (signed-byte   #.*max-linear-address-size*))
   (prefixes  :type (unsigned-byte 43))
   (cnt       :type (integer 0 5))
   x86-1 x86-2)
  :verify-guards nil
  :measure (nfix cnt)
  :non-executable t
  :enabled t

  (if (zp cnt)

      (mv nil prefixes x86-1 x86-2)

    (b* (((mv flg-1 byte-1 x86-1)
          (rm08 start-rip :x x86-1))
         ((mv flg-2 byte-2 x86-2)
          (rm08 start-rip :x x86-2))
         ((when (or (not (equal flg-1 flg-2))
                    (not (equal byte-1 byte-2))))
          (mv nil prefixes x86-1 x86-2))

         (byte byte-1)

         (prefix-byte-group-code
          (get-one-byte-prefix-array-code byte)))

      (if (zp prefix-byte-group-code)

          (let ((prefixes
                 (!prefixes-slice :next-byte byte prefixes)))
            (mv nil
                (!prefixes-slice :num-prefixes (- 5 cnt) prefixes)
                x86-1
                x86-2))

        (case prefix-byte-group-code
          (1 (let ((prefix-1?
                    (prefixes-slice :group-1-prefix prefixes)))
               (if (or (eql 0 (the (unsigned-byte 8) prefix-1?))
                       ;; Redundant Prefix Okay
                       (eql byte prefix-1?))
                   (let ((next-rip (1+ start-rip)))
                     (if (canonical-address-p next-rip)
                         ;; Storing the group 1 prefix and going on...
                         (get-prefixes-and-xlate-equiv-x86s-ind-hint
                          next-rip
                          (!prefixes-slice :group-1-prefix byte prefixes)
                          (1- cnt) x86-1 x86-2)
                       (mv (cons 'non-canonical-address next-rip) prefixes x86-1 x86-2)))
                 ;; We do not tolerate more than one prefix from a prefix group.
                 (mv t prefixes x86-1 x86-2))))

          (2 (let ((prefix-2?
                    (prefixes-slice :group-2-prefix prefixes)))
               (if (or (eql 0 (the (unsigned-byte 8) prefix-2?))
                       ;; Redundant Prefixes Okay
                       (eql byte (the (unsigned-byte 8) prefix-2?)))
                   (let ((next-rip (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     (1+ start-rip))))
                     (if (mbe :logic (canonical-address-p next-rip)
                              :exec
                              (< (the (signed-byte
                                       #.*max-linear-address-size+1*)
                                   next-rip)
                                 #.*2^47*))
                         ;; Storing the group 2 prefix and going on...
                         (get-prefixes-and-xlate-equiv-x86s-ind-hint
                          next-rip
                          (!prefixes-slice :group-2-prefix byte prefixes)
                          (1- cnt)
                          x86-1 x86-2)
                       (mv (cons 'non-canonical-address next-rip)
                           prefixes
                           x86-1 x86-2)))
                 ;; We do not tolerate more than one prefix from a prefix group.
                 (mv t prefixes x86-1 x86-2))))

          (3 (let ((prefix-3?
                    (prefixes-slice :group-3-prefix prefixes)))
               (if (or (eql 0 (the (unsigned-byte 8) prefix-3?))
                       ;; Redundant Prefix Okay
                       (eql byte (the (unsigned-byte 8) prefix-3?)))

                   (let ((next-rip (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     (1+ start-rip))))
                     (if (mbe :logic (canonical-address-p next-rip)
                              :exec
                              (< (the (signed-byte
                                       #.*max-linear-address-size+1*)
                                   next-rip)
                                 #.*2^47*))
                         ;; Storing the group 3 prefix and going on...
                         (get-prefixes-and-xlate-equiv-x86s-ind-hint
                          next-rip
                          (!prefixes-slice :group-3-prefix byte prefixes)
                          (1- cnt)
                          x86-1 x86-2)
                       (mv (cons 'non-canonical-address next-rip)
                           prefixes x86-1 x86-2)))
                 ;; We do not tolerate more than one prefix from a prefix group.
                 (mv t prefixes x86-1 x86-2))))

          (4 (let ((prefix-4?
                    (prefixes-slice :group-4-prefix prefixes)))
               (if (or (eql 0 (the (unsigned-byte 8) prefix-4?))
                       ;; Redundant Prefix Okay
                       (eql byte (the (unsigned-byte 8) prefix-4?)))
                   (let ((next-rip (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     (1+ start-rip))))
                     (if (mbe :logic (canonical-address-p next-rip)
                              :exec
                              (< (the (signed-byte
                                       #.*max-linear-address-size+1*)
                                   next-rip)
                                 #.*2^47*))
                         ;; Storing the group 4 prefix and going on...
                         (get-prefixes-and-xlate-equiv-x86s-ind-hint
                          next-rip
                          (!prefixes-slice :group-4-prefix byte prefixes)
                          (1- cnt)
                          x86-1 x86-2)
                       (mv (cons 'non-canonical-address next-rip)
                           prefixes x86-1 x86-2)))
                 ;; We do not tolerate more than one prefix from a prefix group.
                 (mv t prefixes x86-1 x86-2))))

          (otherwise
           (mv t prefixes x86-1 x86-2)))))))

(local
 (defthmd get-prefixes-and-xlate-equiv-x86s-aux
   (implies (and
             (bind-free
              (find-an-xlate-equiv-x86
               'get-prefixes-and-xlate-equiv-x86s
               x86-1 'x86-2 mfc state)
              (x86-2))
             ;; To prevent loops...
             (syntaxp (not (eq x86-1 x86-2)))
             ;;
             (equal (xr :seg-visible 1 x86-1)
                    (xr :seg-visible 1 x86-2))
             ;;
             (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86-1)))
             (canonical-address-p start-rip)
             (canonical-address-p (+ cnt start-rip))
             (all-paging-entries-found-p
              (create-canonical-address-list cnt start-rip)
              (double-rewrite x86-1))
             (no-page-faults-during-translation-p
              (create-canonical-address-list cnt start-rip)
              :x cpl x86-1)
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
              (create-canonical-address-list cnt start-rip)
              :x cpl x86-1)
             (xlate-equiv-x86s x86-1 x86-2))
            (and
             (equal
              (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-1))
              (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-2)))
             (equal
              (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-1))
              (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-2)))
             (xlate-equiv-x86s
              (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-1))
              (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-2)))))
   :hints (("Goal"
            :induct (cons
                     ;; For opening up both the calls of get-prefixes
                     ;; in sync...
                     (get-prefixes-and-xlate-equiv-x86s-ind-hint
                      start-rip prefixes cnt x86-1 x86-2)
                     ;; For opening up calls of
                     ;; all-paging-entries-found-p and
                     ;; mapped-lin-addrs-disjoint-from-paging-structure-addrs-p...
                     (create-canonical-address-list cnt start-rip))
            :expand ((get-prefixes start-rip prefixes cnt x86-1)
                     (get-prefixes start-rip prefixes cnt x86-2))
            :in-theory (e/d* (get-prefixes
                              all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p)
                             (all-seg-visibles-equal-open
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logior-equal-0
                              acl2::zp-open
                              not
                              (tau-system)
                              (:rewrite negative-logand-to-positive-logand-with-integerp-x)
                              (:type-prescription bitops::logior-natp-type)
                              (:rewrite unsigned-byte-p-of-logior)
                              (:rewrite acl2::ifix-when-not-integerp)
                              (:rewrite acl2::ash-0)
                              (:rewrite acl2::loghead-identity)
                              (:rewrite acl2::zip-open)
                              (:rewrite bitops::logtail-of-logior)
                              (:rewrite bitops::unsigned-byte-p-when-unsigned-byte-p-less)
                              (:rewrite bitops::loghead-of-logior)
                              (:rewrite unsigned-byte-p-of-logtail)
                              (:rewrite unsigned-byte-p-of-logand-2)
                              (:rewrite bitops::logtail-of-logand)
                              (:rewrite loghead-of-non-integerp)
                              (:rewrite bitops::logand-with-bitmask)
                              (:rewrite bitops::logsquash-cancel)
                              (:rewrite member-list-p-and-pairwise-disjoint-p-aux)
                              (:rewrite acl2::zp-when-gt-0)
                              (:rewrite bitops::logtail-of-ash)
                              (:rewrite unsigned-byte-p-of-logand-1)
                              (:definition open-qword-paddr-list-list)
                              (:definition open-qword-paddr-list)
                              (:rewrite signed-byte-p-limits-thm)
                              (:rewrite default-+-2)
                              (:rewrite default-+-1)
                              (:definition pairwise-disjoint-p-aux)
                              (:definition binary-append)
                              (:rewrite default-<-2)
                              (:rewrite default-<-1)
                              (:rewrite programmer-level-mode-rm08-no-error)
                              (:rewrite acl2::append-when-not-consp)
                              (:rewrite acl2::logtail-identity)
                              (:rewrite canonical-address-p-limits-thm-3)
                              (:rewrite get-prefixes-opener-lemma-6)
                              (:rewrite canonical-address-p-limits-thm-2)
                              (:rewrite canonical-address-p-limits-thm-1)
                              (:rewrite canonical-address-p-limits-thm-0)
                              (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
                              (:rewrite logand-redundant)
                              (:rewrite get-prefixes-opener-lemma-5)
                              (:rewrite get-prefixes-opener-lemma-4)
                              (:rewrite get-prefixes-opener-lemma-3)
                              (:rewrite default-cdr)
                              (:type-prescription true-listp-addr-range)
                              (:type-prescription consp-addr-range)
                              (:definition addr-range)
                              (:rewrite rm08-does-not-affect-state-in-programmer-level-mode)
                              (:rewrite bitops::associativity-of-logand)
                              (:rewrite member-p-cdr)
                              (:rewrite pairwise-disjoint-p-aux-and-append)
                              (:rewrite default-car)
                              (:type-prescription open-qword-paddr-list-list)
                              (:rewrite acl2::distributivity-of-minus-over-+)
                              (:type-prescription gather-all-paging-structure-qword-addresses)
                              (:rewrite car-addr-range)
                              (:type-prescription disjoint-p)
                              (:rewrite bitops::logand-fold-consts)
                              (:rewrite all-seg-visibles-equal-aux-open)
                              (:rewrite member-p-and-mult-8-qword-paddr-listp)
                              (:rewrite member-list-p-and-mult-8-qword-paddr-list-listp)
                              (:rewrite bitops::logior-fold-consts)
                              (:linear n43p-get-prefixes)
                              (:rewrite cdr-create-canonical-address-list)
                              (:rewrite car-create-canonical-address-list)
                              (:rewrite consp-of-create-canonical-address-list)
                              (:rewrite disjoint-p-subset-p)
                              (:rewrite disjoint-p-members-of-true-list-list-disjoint-p)
                              (:rewrite disjoint-p-members-of-pairwise-disjoint-p-aux)
                              (:rewrite disjoint-p-members-of-pairwise-disjoint-p)
                              (:rewrite cdr-addr-range)
                              (:rewrite loghead-unequal)
                              (:type-prescription bitops::logand-natp-type-2)
                              (:rewrite default-unary-minus)
                              (:definition n43p$inline)
                              (:rewrite get-prefixes-opener-lemma-7)
                              (:type-prescription rm-low-64-logand-logior-helper-1)
                              (:rewrite acl2::posp-redefinition)
                              (:type-prescription bitops::logand-natp-type-1)
                              (:type-prescription n43p$inline)
                              (:rewrite bitops::logsquash-of-logsquash-2)
                              (:rewrite bitops::logsquash-of-logsquash-1)
                              (:rewrite bitops::logand-of-logand-self-1)
                              (:rewrite get-prefixes-opener-lemma-2)
                              (:rewrite xr-rm08-state-in-programmer-level-mode)
                              (:type-prescription bitops::ash-natp-type)
                              (:rewrite mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-member-p)
                              (:type-prescription rationalp-expt-type-prescription)
                              (:type-prescription posp)
                              (:type-prescription n64p$inline)
                              (:rewrite x86p-rm08)
                              (:type-prescription expt-type-prescription-non-zero-base)
                              (:type-prescription bitops::part-install-width-low$inline)
                              (:type-prescription bitops::natp-part-install-width-low)
                              (:rewrite rationalp-implies-acl2-numberp)))))))

(encapsulate
  ()

  (defun find-binding-from-all-entries-found-p-aux
    (var calls)
    (if
        (endp calls)
        nil
      (b*
          ((call (car calls))
           (var-val (if (equal var 'l-addrs)
                        (second call)
                      (if (equal var 'x86)
                          (third call)
                        nil))))
        (append
         (cons (cons var var-val) 'nil)
         (find-binding-from-all-entries-found-p-aux var (cdr calls))))))

  (defun find-binding-from-all-entries-found-p
    (var mfc state)
    (declare (xargs :stobjs (state) :mode :program)
             (ignorable state))
    (b* ((calls (acl2::find-calls-of-fns-lst
                 '(all-paging-entries-found-p)
                 (acl2::mfc-clause mfc))))
      (find-binding-from-all-entries-found-p-aux var calls)))

  (defthm all-paging-entries-found-p-and-good-paging-structures-x86p
    (implies (and
              (bind-free
               (find-binding-from-all-entries-found-p
                'l-addrs mfc state)
               (l-addrs))
              (all-paging-entries-found-p l-addrs x86)
              (consp l-addrs))
             (good-paging-structures-x86p x86))
    :hints (("Goal"
             :use ((:instance entry-found-p-and-good-paging-structures-x86p
                              (lin-addr (car l-addrs))))
             :in-theory (e/d* (all-paging-entries-found-p)
                              (entry-found-p-and-good-paging-structures-x86p))))))

(defthm get-prefixes-and-xlate-equiv-x86s
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'get-prefixes-and-xlate-equiv-x86s
              x86-1 'x86-2 mfc state)
             (x86-2))
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
            (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86-1)))
            (canonical-address-p start-rip)
            (canonical-address-p (+ cnt start-rip))
            (posp cnt)
            (all-paging-entries-found-p
             (create-canonical-address-list cnt start-rip)
             (double-rewrite x86-1))
            (no-page-faults-during-translation-p
             (create-canonical-address-list cnt start-rip)
             :x cpl (double-rewrite x86-1))
            (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
             (create-canonical-address-list cnt start-rip)
             :x cpl (double-rewrite x86-1))
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2))
           (and
            (equal
             (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-1))
             (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-2)))
            (equal
             (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-1))
             (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-2)))
            (xlate-equiv-x86s
             (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-1))
             (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-2)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance all-seg-visibles-equal-open
                            (j 1))
                 (:instance get-prefixes-and-xlate-equiv-x86s-aux))
           :in-theory (e/d* (all-paging-entries-found-p)
                            (all-seg-visibles-equal-open
                             get-prefixes-and-xlate-equiv-x86s-aux
                             unsigned-byte-p
                             signed-byte-p)))))

(defthm get-prefixes-opener-lemma-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (canonical-address-p start-rip)
                (canonical-address-p (+ cnt start-rip))
                (all-paging-entries-found-p
                 (create-canonical-address-list cnt start-rip)
                 (double-rewrite x86))
                (no-page-faults-during-translation-p
                 (create-canonical-address-list cnt start-rip)
                 :x cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 (create-canonical-address-list cnt start-rip)
                 :x cpl (double-rewrite x86))
                (not (zp cnt))
                (not (mv-nth 0 (rm08 start-rip :x x86))))
           (and
            (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt x86))
                   (cond
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       1)
                      (equal (prefixes-slice :group-1-prefix prefixes) 0))
                     (mv-nth 0
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-1-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       2)
                      (equal (prefixes-slice :group-2-prefix prefixes) 0))
                     (mv-nth 0
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-2-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       3)
                      (equal (prefixes-slice :group-3-prefix prefixes) 0))
                     (mv-nth 0
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-3-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       4)
                      (equal (prefixes-slice :group-4-prefix prefixes) 0))
                     (mv-nth 0
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-4-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    (t
                     (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))))
            (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt x86))
                   (cond
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       1)
                      (equal (prefixes-slice :group-1-prefix prefixes) 0))
                     (mv-nth 1
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-1-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       2)
                      (equal (prefixes-slice :group-2-prefix prefixes) 0))
                     (mv-nth 1
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-2-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       3)
                      (equal (prefixes-slice :group-3-prefix prefixes) 0))
                     (mv-nth 1
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-3-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    ((and
                      (equal
                       (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                       4)
                      (equal (prefixes-slice :group-4-prefix prefixes) 0))
                     (mv-nth 1
                             (get-prefixes (1+ start-rip)
                                           (!prefixes-slice
                                            :group-4-prefix
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)
                                           (1- cnt) x86)))
                    (t
                     (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((get-prefixes start-rip prefixes cnt x86))
           :in-theory (e/d* (get-prefixes
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (get-prefixes-and-xlate-equiv-x86s
                             (:definition unsigned-byte-p)
                             (:rewrite negative-logand-to-positive-logand-with-integerp-x)
                             (:linear <=-logior)
                             (:rewrite bitops::logsquash-cancel)
                             (:rewrite acl2::natp-when-integerp)
                             (:linear bitops::logand-<-0-linear)
                             (:rewrite acl2::ifix-negative-to-negp)
                             (:linear bitops::logand->=-0-linear-2)
                             (:type-prescription bitops::logand-natp-type-2)
                             (:linear bitops::upper-bound-of-logand . 2)
                             (:linear bitops::logior->=-0-linear)
                             (:linear bitops::logior-<-0-linear-2)
                             (:linear bitops::logior-<-0-linear-1)
                             (:rewrite default-<-1)
                             (:type-prescription bitops::logior-natp-type)
                             (:rewrite acl2::negp-when-less-than-0)
                             (:rewrite acl2::natp-when-gte-0)
                             (:rewrite unsigned-byte-p-of-logior)
                             (:type-prescription bitops::logand-natp-type-1)
                             (:type-prescription binary-logand)
                             (:linear ash-monotone-2)
                             (:rewrite acl2::ifix-when-not-integerp)
                             (:linear acl2::loghead-upper-bound)
                             (:rewrite acl2::loghead-identity)
                             (:rewrite default-<-2)
                             (:rewrite acl2::negp-when-integerp)
                             (:rewrite constant-upper-bound-of-logior-for-naturals)
                             (:type-prescription bitops::ash-natp-type)
                             (:rewrite unsigned-byte-p-of-logand-2)
                             (:rewrite bitops::ash-<-0)
                             (:type-prescription natp-of-get-one-byte-prefix-array-code)
                             (:type-prescription n08p-mv-nth-1-rm08)
                             (:type-prescription negp)
                             (:linear bitops::logand->=-0-linear-1)
                             (:rewrite acl2::ash-0)
                             (:rewrite acl2::zip-open)
                             (:rewrite bitops::logsquash-<-0)
                             (:rewrite loghead-of-non-integerp)
                             (:rewrite unsigned-byte-p-of-logtail)
                             (:linear bitops::upper-bound-of-logand . 1)
                             (:rewrite bitops::logior-equal-0)
                             (:rewrite bitops::logtail-of-logior)
                             (:rewrite bitops::unsigned-byte-p-when-unsigned-byte-p-less)
                             (:type-prescription bitops::logsquash$inline)
                             (:rewrite bitops::logtail-of-logand)
                             (:rewrite acl2::logtail-identity)
                             (:rewrite bitops::loghead-of-logior)
                             (:rewrite unsigned-byte-p-of-logsquash)
                             (:type-prescription bitops::logtail-natp)
                             (:rewrite bitops::logtail-of-ash)
                             (:rewrite get-prefixes-opener-lemma-1)
                             (:linear bitops::upper-bound-of-logior-for-naturals)
                             (:type-prescription acl2::logtail-type)
                             (:rewrite rm08-values-and-xlate-equiv-x86s-disjoint)
                             (:rewrite bitops::logand-with-bitmask)
                             (:linear n08p-mv-nth-1-rm08)
                             (:rewrite acl2::zp-when-gt-0)
                             (:rewrite bitops::loghead-of-logand)
                             (:rewrite unsigned-byte-p-of-logand-1)
                             (:type-prescription logtail-*2^x-byte-pseudo-page*-of-physical-address)
                             (:rewrite default-+-2)
                             (:rewrite default-+-1)
                             (:rewrite bitops::loghead-of-logsquash-commute)
                             (:rewrite member-list-p-and-pairwise-disjoint-p-aux)
                             (:definition n64p$inline)
                             (:type-prescription rationalp-expt-type-prescription)
                             (:linear rm-low-64-logand-logior-helper-1)
                             (:rewrite signed-byte-p-limits-thm)
                             (:type-prescription expt-type-prescription-non-zero-base)
                             (:rewrite n08p-mv-nth-1-rm08)
                             (:definition member-list-p)
                             (:definition programmer-level-mode$inline)
                             (:type-prescription rm-low-64-logand-logior-helper-1)
                             (:rewrite programmer-level-mode-rm08-no-error)
                             (:definition open-qword-paddr-list-list)
                             (:rewrite canonical-address-p-limits-thm-3)
                             (:rewrite acl2::simplify-logior)
                             (:rewrite get-prefixes-opener-lemma-6)
                             (:rewrite get-prefixes-opener-lemma-5)
                             (:rewrite get-prefixes-opener-lemma-4)
                             (:rewrite get-prefixes-opener-lemma-3)
                             (:definition open-qword-paddr-list)
                             (:rewrite bitops::logsquash-of-0-i)
                             (:definition pairwise-disjoint-p-aux)
                             (:rewrite canonical-address-p-limits-thm-2)
                             (:rewrite canonical-address-p-limits-thm-1)
                             (:rewrite canonical-address-p-limits-thm-0)
                             (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
                             (:rewrite logand-redundant)
                             (:type-prescription n64p$inline)
                             (:type-prescription zip)
                             (:rewrite unsigned-byte-p-of-ash)
                             (:rewrite open-qword-paddr-list-list-and-member-list-p)
                             (:meta acl2::mv-nth-cons-meta)
                             (:type-prescription integer-range-p)
                             (:type-prescription bitops::lognot-negp)
                             (:type-prescription seg-visiblei-is-n16p)
                             (:definition binary-append)
                             (:rewrite rm08-does-not-affect-state-in-programmer-level-mode)
                             (:type-prescription member-list-p)
                             (:rewrite member-p-cdr)
                             (:rewrite bitops::logtail-of-logtail)
                             (:rewrite good-paging-structures-x86p-implies-x86p)
                             (:type-prescription ash)
                             (:rewrite rm-low-64-logand-logior-helper-1)
                             (:rewrite default-cdr)
                             (:rewrite rm08-value-when-error)
                             (:linear seg-visiblei-is-n16p)
                             (:rewrite acl2::append-when-not-consp)
                             (:rewrite xr-rm08-state-in-system-level-mode)
                             (:rewrite unsigned-byte-p-of-loghead)
                             (:rewrite acl2::difference-unsigned-byte-p)
                             (:rewrite consp-of-create-canonical-address-list)
                             (:rewrite cdr-create-canonical-address-list)
                             (:rewrite car-create-canonical-address-list)
                             (:definition addr-range)
                             (:rewrite default-car)
                             (:rewrite get-prefixes-opener-lemma-2)
                             (:rewrite acl2::distributivity-of-minus-over-+)
                             (:type-prescription true-listp-addr-range)
                             (:type-prescription consp-addr-range)
                             (:rewrite subset-list-p-and-member-list-p)
                             (:rewrite x86p-rm08)
                             (:type-prescription bitops::lognot-natp)
                             (:type-prescription lognot)
                             (:type-prescription open-qword-paddr-list-list)
                             (:type-prescription gather-all-paging-structure-qword-addresses)
                             (:rewrite member-p-and-mult-8-qword-paddr-listp)
                             (:rewrite member-list-p-and-mult-8-qword-paddr-list-listp)
                             (:rewrite bitops::logior-fold-consts)
                             (:rewrite pairwise-disjoint-p-aux-and-append)
                             (:rewrite car-addr-range)
                             (:rewrite all-seg-visibles-equal-aux-open)
                             (:rewrite acl2::unsigned-byte-p-loghead)
                             (:rewrite default-unary-minus)
                             (:rewrite good-paging-structures-x86p-implies-system-level-mode)
                             (:rewrite subset-p-cons-member-p-lemma)
                             (:rewrite member-p-of-not-a-consp)
                             (:rewrite member-list-p-no-duplicates-list-p-and-member-p)
                             (:rewrite loghead-ash-0)
                             (:type-prescription bitops::natp-part-install-width-low)
                             (:rewrite bitops::loghead-of-ash-same)
                             (:rewrite bitops::loghead-of-0-i)
                             (:rewrite bitops::logsquash-of-logsquash-2)
                             (:rewrite bitops::logsquash-of-logsquash-1)
                             (:type-prescription mult-8-qword-paddr-list-listp)
                             (:type-prescription disjoint-p)
                             (:rewrite mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-member-p)
                             (:rewrite
                              good-paging-structures-x86p-implies-mult-8-qword-paddr-list-listp-paging-structure-addrs)
                             (:rewrite disjoint-p-subset-p)
                             (:rewrite disjoint-p-members-of-true-list-list-disjoint-p)
                             (:rewrite disjoint-p-members-of-pairwise-disjoint-p-aux)
                             (:rewrite disjoint-p-members-of-pairwise-disjoint-p)
                             (:rewrite cdr-addr-range)
                             (:type-prescription bitops::part-install-width-low$inline)
                             (:rewrite get-prefixes-opener-lemma-7)
                             (:rewrite xr-rm08-state-in-programmer-level-mode)))
           :use ((:instance get-prefixes-and-xlate-equiv-x86s
                            (cpl (loghead 2 (xr :seg-visible 1 x86)))
                            (start-rip (1+ start-rip))
                            (prefixes (cond
                                       ((and
                                         (equal
                                          (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                                          1)
                                         (equal (prefixes-slice :group-1-prefix prefixes) 0))
                                        (!prefixes-slice
                                         :group-1-prefix
                                         (mv-nth 1 (rm08 start-rip :x x86))
                                         prefixes))
                                       ((and
                                         (equal
                                          (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                                          2)
                                         (equal (prefixes-slice :group-2-prefix prefixes) 0))
                                        (!prefixes-slice
                                         :group-2-prefix
                                         (mv-nth 1 (rm08 start-rip :x x86))
                                         prefixes))
                                       ((and
                                         (equal
                                          (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                                          3)
                                         (equal (prefixes-slice :group-3-prefix prefixes) 0))
                                        (!prefixes-slice
                                         :group-3-prefix
                                         (mv-nth 1 (rm08 start-rip :x x86))
                                         prefixes))
                                       ((and
                                         (equal
                                          (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))
                                          4)
                                         (equal (prefixes-slice :group-4-prefix prefixes) 0))
                                        (!prefixes-slice
                                         :group-4-prefix
                                         (mv-nth 1 (rm08 start-rip :x x86))
                                         prefixes))
                                       (t
                                        prefixes)))
                            (cnt (+ -1 cnt))
                            (x86-1 (mv-nth 2 (rm08 start-rip :x x86)))
                            (x86-2 x86))))))

;; ======================================================================

;; x86-fetch-decode-execute lemmas in the system-level mode:

#||

(i-am-here)

(defthm x86-fetch-decode-execute-and-xlate-equiv-x86s
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'x86-fetch-decode-execute-and-xlate-equiv-x86s
              x86-1 'x86-2 mfc state)
             (x86-2))
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
            (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86-1)))

            (equal start-rip (rip x86-1))
            (equal prefixes (mv-nth 1 (get-prefixes start-rip 0 5 x86-1)))
            (equal opcode/rex/escape-byte
                   (prefixes-slice :next-byte prefixes))
            (equal prefix-length (prefixes-slice :num-prefixes prefixes))
            (equal temp-rip0 (if (equal prefix-length 0)
                                 (+ 1 start-rip)
                               (+ prefix-length start-rip 1)))
            (equal rex-byte (if (equal (ash opcode/rex/escape-byte -4)
                                       4)
                                opcode/rex/escape-byte 0))
            (equal opcode/escape-byte (if (equal rex-byte 0)
                                          opcode/rex/escape-byte
                                        (mv-nth 1 (rm08 temp-rip0 :x x86-1))))
            (equal temp-rip1 (if (equal rex-byte 0)
                                 temp-rip0 (1+ temp-rip0)))
            (equal modr/m? (x86-one-byte-opcode-modr/m-p opcode/escape-byte))
            (equal modr/m (if modr/m?
                              (mv-nth 1 (rm08 temp-rip1 :x x86-1))
                            0))
            (equal temp-rip2 (if modr/m? (1+ temp-rip1) temp-rip1))
            (equal sib? (and modr/m? (x86-decode-sib-p modr/m)))
            (equal sib (if sib? (mv-nth 1 (rm08 temp-rip2 :x x86-1)) 0))
            (equal temp-rip3 (if sib? (1+ temp-rip2) temp-rip2))
            (not (mv-nth 0 (get-prefixes (xr :rip 0 x86-1) 0 5 x86-1)))
            (not (mv-nth 0 (rm08 temp-rip0 :x x86-1)))

            (canonical-address-p start-rip)
            ;; An instruction can be up to 15 bytes long.
            (canonical-address-p (+ 15 start-rip))
            (all-paging-entries-found-p
             (create-canonical-address-list 15 start-rip)
             (double-rewrite x86-1))
            (no-page-faults-during-translation-p
             (create-canonical-address-list 15 start-rip)
             :x cpl x86-1)
            (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
             (create-canonical-address-list 15 start-rip)
             :x cpl x86-1)
            (canonical-address-p temp-rip0)
            (if (equal rex-byte 0)
                t
              (canonical-address-p temp-rip1))
            (if modr/m?
                (and (canonical-address-p temp-rip2)
                     (not (mv-nth 0 (rm08 temp-rip1 :x x86-1))))
              t)
            (if sib?
                (and (canonical-address-p temp-rip3)
                     (not (mv-nth 0 (rm08 temp-rip2 :x x86-1))))
              t)
            (xlate-equiv-x86s x86-1 x86-2)
            (not (xr :programmer-level-mode 0 x86-1)))
           (xlate-equiv-x86s
            (x86-fetch-decode-execute x86-1)
            (x86-fetch-decode-execute x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-xr-simple-fields
                            (fld :rip))
                 (:instance xlate-equiv-x86s-and-xr-simple-fields
                            (fld :ms))
                 (:instance xlate-equiv-x86s-and-xr-simple-fields
                            (fld :fault)))
           :in-theory (e/d* (xlate-equiv-x86s-and-xr-simple-fields
                             x86-fetch-decode-execute
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             x86-step-unimplemented)
                            (top-level-opcode-execute
                             unsigned-byte-p
                             signed-byte-p
                             bitops::logior-equal-0
                             acl2::zp-open
                             xlate-equiv-x86s-and-xr-simple-fields
                             all-seg-visibles-equal-open
                             acl2::member-of-cons)))))

;; Ugh, I need to prove
;; xlate-equiv-x86s-and-top-level-opcode-execute. Which means that I'd
;; have to do that for all the instruction specifications. That's
;; going to clutter everything up.

;; But how do I even prove xlate-equiv-x86s with any function defined
;; using def-inst if that function accesses/updates the memory? I'd
;; need lemmas that say that this memory access/update is disjoint
;; from the paging structures. And God, when we accumulate all such
;; lemmas together, the theorem
;; xlate-equiv-x86s-and-top-level-opcode-execute is going to have a
;; ton of hypotheses... Sigh. This is very bad.

;; Even if I do end up proving
;; xlate-equiv-x86s-and-top-level-opcode-execute and consequently
;; x86-fetch-decode-execute-opener-in-system-level-mode, how will the
;; latter driver rule work? I'd need xlate-equiv-x86s to be an
;; acceptable congruence relation in the context where
;; x86-fetch-decode-execute-opener-in-system-level-mode would help.

;; I guess the solution to this problem is similar to what I did with
;; paging-lib/x86-ia32e-paging-alt.lisp. See x86-alt.lisp.

(defthm xlate-equiv-x86s-and-top-level-opcode-execute
  (implies (and
            ;; Bind-free here
            (xlate-equiv-x86s x86-1 x86-2)
            ;; Loads of other hypotheses...
            )
           (xlate-equiv-x86s
            (top-level-opcode-execute
             start-rip temp-rip prefixes rex-byte
             opcode/escape-byte modr/m sib x86-1)
            (top-level-opcode-execute
             start-rip temp-rip prefixes rex-byte
             opcode/escape-byte modr/m sib x86-2)))
  :hints (("Goal" :in-theory (e/d* (top-level-opcode-execute)
                                   ()))))

(defthm x86-fetch-decode-execute-opener-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal start-rip (rip x86))
        (equal prefixes (mv-nth 1 (get-prefixes start-rip 0 5 x86)))
        (equal opcode/rex/escape-byte
               (prefixes-slice :next-byte prefixes))
        (equal prefix-length (prefixes-slice :num-prefixes prefixes))
        (equal temp-rip0 (if (equal prefix-length 0)
                             (+ 1 start-rip)
                           (+ prefix-length start-rip 1)))
        (equal rex-byte (if (equal (ash opcode/rex/escape-byte -4)
                                   4)
                            opcode/rex/escape-byte 0))
        (equal opcode/escape-byte (if (equal rex-byte 0)
                                      opcode/rex/escape-byte
                                    (mv-nth 1 (rm08 temp-rip0 :x x86))))
        (equal temp-rip1 (if (equal rex-byte 0)
                             temp-rip0 (1+ temp-rip0)))
        (equal modr/m? (x86-one-byte-opcode-modr/m-p opcode/escape-byte))
        (equal modr/m (if modr/m?
                          (mv-nth 1 (rm08 temp-rip1 :x x86))
                        0))
        (equal temp-rip2 (if modr/m? (1+ temp-rip1) temp-rip1))
        (equal sib? (and modr/m? (x86-decode-sib-p modr/m)))
        (equal sib (if sib? (mv-nth 1 (rm08 temp-rip2 :x x86)) 0))
        (equal temp-rip3 (if sib? (1+ temp-rip2) temp-rip2))

        (x86p x86)
        (not (ms x86))
        (not (fault x86))
        (canonical-address-p start-rip)
        (canonical-address-p temp-rip0)
        (all-paging-entries-found-p
         (create-canonical-address-list 15 start-rip)
         (double-rewrite x86))
        (no-page-faults-during-translation-p
         (create-canonical-address-list 15 start-rip)
         :x cpl (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
         (create-canonical-address-list 15 start-rip)
         :x cpl (double-rewrite x86))
        (not (mv-nth 0 (get-prefixes start-rip 0 5 x86)))

        (not (mv-nth 0 (rm08 temp-rip0 :x x86)))
        (if (equal rex-byte 0)
            t
          (canonical-address-p temp-rip1))
        (if modr/m?
            (and (canonical-address-p temp-rip2)
                 (not (mv-nth 0 (rm08 temp-rip1 :x x86))))
          t)
        (if sib?
            (and (canonical-address-p temp-rip3)
                 (not (mv-nth 0 (rm08 temp-rip2 :x x86))))
          t)
        (not (xr :programmer-level-mode 0 x86)))
   (xlate-equiv-x86s
    (x86-fetch-decode-execute x86)
    (top-level-opcode-execute
     start-rip temp-rip3 prefixes rex-byte opcode/escape-byte modr/m sib x86)))
  :hints (("Goal" :in-theory (e/d (x86-fetch-decode-execute)
                                  (signed-byte-p
                                   not
                                   acl2::member-of-cons
                                   top-level-opcode-execute)))))

||#

;; ======================================================================
