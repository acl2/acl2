;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "marking-mode-utils")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

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
   (and (disjoint-p (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))
                    (open-qword-paddr-list
                     (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (not (programmer-level-mode x86))
        (addr-byte-alistp addr-lst))
   (equal
    (gather-all-paging-structure-qword-addresses (mv-nth 1 (wb addr-lst x86)))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (wb) (force (force) (:meta acl2::mv-nth-cons-meta))))))

; ======================================================================

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
      (implies (forced-and (x86p x86)
                           (canonical-address-p start-rip))
               (x86p (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))))

    (defthm xr-not-mem-and-get-prefixes-alt
      (implies (and (not (equal fld :mem))
                    (not (equal fld :fault)))
               (equal (xr fld index (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
                      (xr fld index x86)))
      :hints (("Goal" :in-theory (e/d* () (not force (force)))))))

  (defthm rewrite-get-prefixes-to-get-prefixes-alt
    (implies (forced-and
              (disjoint-p
               (mv-nth 1 (las-to-pas
                          (create-canonical-address-list cnt start-rip)
                          :x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses x86)))
              (not (mv-nth 0 (las-to-pas
                              (create-canonical-address-list cnt start-rip)
                              :x (cpl x86) x86)))
              (page-structure-marking-mode x86)
              (not (programmer-level-mode x86))
              (canonical-address-p start-rip))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes-alt start-rip prefixes cnt x86)))
    :hints (("Goal" :in-theory (e/d* (get-prefixes-alt) ()))))

  ;; Opener lemmas:

  (defthm get-prefixes-alt-opener-lemma-zero-cnt
    (implies (and (zp cnt)
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
                                x86)))
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
                                x86)))
                  (disjoint-p
                   (mv-nth 1 (las-to-pas
                              (create-canonical-address-list cnt start-rip)
                              :x (cpl x86) (double-rewrite x86)))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses x86))))
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
    :hints (("Goal" :in-theory (e/d* (canonical-address-p member-p) ())))))

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
      (implies (x86p x86)
               (x86p (mv-nth 2 (rb-alt l-addrs r-w-x x86)))))

    (defthm rb-alt-nil-lemma
      (equal (mv-nth 1 (rb-alt nil r-w-x x86))
             nil)
      :hints (("Goal"
               :cases ((and (page-structure-marking-mode x86)
                            (not (programmer-level-mode x86))
                            (not (mv-nth 0 (las-to-pas nil r-w-x (cpl x86) x86)))))
               :in-theory (e/d* () (force (force))))))

    (defthm xr-rb-alt-state-in-system-level-mode
      (implies (and (not (equal fld :mem))
                    (not (equal fld :fault)))
               (equal (xr fld index (mv-nth 2 (rb-alt addr r-w-x x86)))
                      (xr fld index x86)))
      :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm mv-nth-0-rb-alt-is-nil
      (equal (mv-nth 0 (rb-alt l-addrs r-w-x x86)) nil)
      :hints (("Goal"
               :use ((:instance mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode))
               :in-theory (e/d* ()
                                (mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode
                                 force (force)))))))

  ;; Rewrite rb to rb-alt:

  (defthm rewrite-rb-to-rb-alt
    (implies (forced-and
              ;; (disjoint-p (all-translation-governing-addresses l-addrs x86)
              ;;             (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
              (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) x86))
                          (open-qword-paddr-list
                           (gather-all-paging-structure-qword-addresses x86)))
              (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
              (canonical-address-listp l-addrs)
              (page-structure-marking-mode x86)
              (not (programmer-level-mode x86)))
             (equal (rb l-addrs r-w-x x86)
                    (rb-alt l-addrs r-w-x x86)))
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
                  (program-at (create-canonical-address-list n prog-addr)
                              bytes x86)
                  (syntaxp (quotep n))
                  (member-p lin-addr (create-canonical-address-list n prog-addr))
                  (not (mv-nth 0
                               (las-to-pas (create-canonical-address-list n prog-addr)
                                           :x (cpl x86)
                                           (double-rewrite x86))))
                  (disjoint-p
                   (mv-nth 1
                           (las-to-pas (create-canonical-address-list n prog-addr)
                                       :x (cpl x86)
                                       (double-rewrite x86)))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
                  (page-structure-marking-mode x86)
                  (x86p x86))
             (equal (car (mv-nth 1 (rb-alt (list lin-addr) :x x86)))
                    (nth (pos lin-addr (create-canonical-address-list n prog-addr)) bytes)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (las-to-pas
                              subset-p
                              disjoint-p)
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
      (program-at (create-canonical-address-list n prog-addr) bytes x86)
      (subset-p l-addrs (create-canonical-address-list n prog-addr))
      (syntaxp (quotep n))
      (consp l-addrs)
      (not (mv-nth 0
                   (las-to-pas (create-canonical-address-list n prog-addr)
                               :x (cpl x86) (double-rewrite x86))))
      (disjoint-p
       (mv-nth 1
               (las-to-pas (create-canonical-address-list n prog-addr)
                           :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (page-structure-marking-mode x86)
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
                              disjoint-p)
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
                  (disjoint-p
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
              (disjoint-p
               ;; The physical addresses pertaining to the read are
               ;; disjoint from the physical addresses of the paging
               ;; structures.
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list (gather-all-paging-structure-qword-addresses
                                       (double-rewrite x86))))
              (disjoint-p
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
             :in-theory (e/d* (disjoint-p-commutative)
                              (rewrite-rb-to-rb-alt
                               rb-wb-disjoint-in-system-level-mode
                               disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs))))))

;; ======================================================================

(defsection program-at-alt
  :parents (marking-mode-top)

  (define program-at-alt ((l-addrs canonical-address-listp)
                          (bytes byte-listp)
                          (x86))
    :non-executable t
    (if (and (page-structure-marking-mode x86)
             (not (programmer-level-mode x86))
             (canonical-address-listp l-addrs)
             (not (mv-nth 0 (las-to-pas l-addrs :x (cpl x86) x86)))
             (disjoint-p (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) x86))
                         (open-qword-paddr-list
                          (gather-all-paging-structure-qword-addresses x86))))

        (program-at l-addrs bytes x86)

      nil))

  (defthm rewrite-program-at-to-program-at-alt
    (implies (forced-and
              (disjoint-p (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) x86))
                          (open-qword-paddr-list
                           (gather-all-paging-structure-qword-addresses x86)))
              (not (mv-nth 0 (las-to-pas l-addrs :x (cpl x86) x86)))
              (canonical-address-listp l-addrs)
              (page-structure-marking-mode x86)
              (not (programmer-level-mode x86)))
             (equal (program-at l-addrs bytes x86)
                    (program-at-alt l-addrs bytes x86)))
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
    :rule-classes :congruence))

;; ======================================================================

#||

;; Some misc. rules:

(defun get-subterms-if-match (n match-fn terms)
  (declare (xargs :guard (and (natp n)
                              (symbolp match-fn)
                              (pseudo-term-listp terms))))
  ;; (get-subterms-if-match
  ;;  1
  ;;  'create-canonical-address-list
  ;;  '((all-translation-governing-addresses
  ;;     (create-canonical-address-list cnt start-rip)
  ;;     p-addrs)
  ;;    (all-translation-governing-addresses
  ;;     (cons 'start-rip nil)
  ;;     p-addrs)))
  (if (atom terms)
      nil
    (let ((term (nth n (acl2::list-fix (car terms)))))
      (if (and (consp term)
               (eq (car term) match-fn))
          (cons term (get-subterms-if-match n match-fn (cdr terms)))
        (get-subterms-if-match n match-fn (cdr terms))))))

(defun find-l-addrs-like-create-canonical-address-list-from-fn
  (fn l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
       ((when (not calls)) nil)
       (l-addrs (get-subterms-if-match 1 'create-canonical-address-list calls))
       (alst-lst
        (make-bind-free-alist-lists l-addrs-var l-addrs)))
    alst-lst))

;; TODO: Maybe merge -1 and -2 rules by removing the first syntaxp?

(defthm disjoint-p-all-translation-governing-addresses-and-las-to-pas-subset-p-1
  ;; Follows from MV-NTH-1-LAS-TO-PAS-SUBSET-P-DISJOINT-FROM-OTHER-P-ADDRS.

  ;; This rule is tailored to rewrite terms of the form

  ;; (disjoint-p (all-translation-governing-addresses l-addrs-subset x86)
  ;;             (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

  ;; where l-addrs-subset is a subset of l-addrs, l-addrs is of the
  ;; form (create-canonical-address-list ...), and l-addrs-subset is
  ;; NOT of the form (create-canonical-address-list ...).

  ;; This comes in useful during instruction fetches, where given that
  ;; a top-level hypothesis states that the program's
  ;; translation-governing addresses are disjoint from the physical
  ;; addresses, we have to infer that the same is the case for a
  ;; single instruction. Note that this rule is sort of a special
  ;; instance of
  ;; DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P,
  ;; which is much more expensive/general rule.

  (implies
   (and
    (syntaxp (and (consp l-addrs-subset)
                  (not (eq (car l-addrs-subset) 'create-canonical-address-list))))
    (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                'all-translation-governing-addresses 'l-addrs mfc state)
               (l-addrs))
    ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
    (syntaxp (and (consp l-addrs)
                  (eq (car l-addrs) 'create-canonical-address-list)))
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
                     (other-p-addrs-subset (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))))
    :in-theory (e/d* (subset-p
                      member-p
                      disjoint-p-append-1
                      las-to-pas
                      all-translation-governing-addresses)
                     ()))))

(defthm disjoint-p-all-translation-governing-addresses-and-las-to-pas-subset-p-2
  ;; This rule is tailored to rewrite terms of the form

  ;; (disjoint-p (all-translation-governing-addresses l-addrs-subset x86)
  ;;             (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

  ;; where l-addrs-subset is a subset of l-addrs, and both l-addrs and
  ;; l-addrs-subset are of the form (create-canonical-address-list
  ;; ...).

  (implies
   (and
    (syntaxp (and (consp l-addrs-subset)
                  (eq (car l-addrs-subset) 'create-canonical-address-list)))
    (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                'all-translation-governing-addresses 'l-addrs mfc state)
               (l-addrs))
    ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
    (syntaxp (and (consp l-addrs)
                  (eq (car l-addrs) 'create-canonical-address-list)))
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
                     (other-p-addrs-subset (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))))
    :in-theory (e/d* (subset-p
                      member-p
                      disjoint-p-append-1
                      las-to-pas
                      all-translation-governing-addresses)
                     ()))))

(defthm not-member-p-of-all-translation-governing-addresses-1
  ;; This rule is tailored to rewrite terms of the form to nil

  ;; (member-p index (all-translation-governing-addresses l-addrs-subset x86))

  ;; where l-addrs-subset is a subset of l-addrs, l-addrs is of the
  ;; form (create-canonical-address-list ...), and l-addrs-subset is
  ;; NOT of the form (create-canonical-address-list ...).

  (implies (and (syntaxp (and (consp l-addrs-subset)
                              (not (eq (car l-addrs-subset) 'create-canonical-address-list))))
                (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                            'all-translation-governing-addresses 'l-addrs mfc state)
                           (l-addrs))
                ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
                (syntaxp (and (consp l-addrs)
                              (eq (car l-addrs) 'create-canonical-address-list)))
                (not (member-p index (all-translation-governing-addresses l-addrs x86)))
                (subset-p l-addrs-subset l-addrs))
           (equal (member-p index (all-translation-governing-addresses l-addrs-subset x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    member-p
                                    all-translation-governing-addresses)
                                   ()))))

(defthm not-member-p-of-all-translation-governing-addresses-2
  ;; This rule is tailored to rewrite terms of the form to nil

  ;; (member-p index (all-translation-governing-addresses l-addrs-subset x86))

  ;; where l-addrs-subset is a subset of l-addrs, and both l-addrs and
  ;; l-addrs-subset are of the form (create-canonical-address-list
  ;; ...).

  (implies (and (syntaxp (and (consp l-addrs-subset)
                              (eq (car l-addrs-subset) 'create-canonical-address-list)))
                (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                            'all-translation-governing-addresses 'l-addrs mfc state)
                           (l-addrs))
                ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
                (syntaxp (and (consp l-addrs)
                              (eq (car l-addrs) 'create-canonical-address-list)))
                (not (member-p index (all-translation-governing-addresses l-addrs x86)))
                (subset-p l-addrs-subset l-addrs))
           (equal (member-p index (all-translation-governing-addresses l-addrs-subset x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    member-p
                                    all-translation-governing-addresses)
                                   ()))))

(defthm not-member-p-of-mv-nth-1-las-to-pas-1
  ;; This rule is tailored to rewrite terms of the form to nil

  ;; (member-p index (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

  ;; where l-addrs-subset is a subset of l-addrs, l-addrs is of the
  ;; form (create-canonical-address-list ...), and l-addrs-subset is
  ;; NOT of the form (create-canonical-address-list ...).

  (implies (and (syntaxp (and (consp l-addrs-subset)
                              (not (eq (car l-addrs-subset) 'create-canonical-address-list))))
                (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                            'las-to-pas 'l-addrs mfc state)
                           (l-addrs))
                ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
                (syntaxp (and (consp l-addrs)
                              (eq (car l-addrs) 'create-canonical-address-list)))
                (not (member-p index (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))))
                (subset-p l-addrs-subset l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
           (equal (member-p index (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))
                  nil))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance mv-nth-1-las-to-pas-subset-p)
                 (:instance not-member-p-of-superset-is-not-member-p-of-subset
                            (e index)
                            (y (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                            (x (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))))
           :in-theory (e/d* () (mv-nth-1-las-to-pas-subset-p)))))

(defthm not-member-p-of-mv-nth-1-las-to-pas-2
  ;; This rule is tailored to rewrite terms of the form to nil

  ;; (member-p index (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

  ;; where l-addrs-subset is a subset of l-addrs, and both l-addrs and
  ;; l-addrs-subset are of the form (create-canonical-address-list
  ;; ...).

  (implies (and (syntaxp (and (consp l-addrs-subset)
                              (eq (car l-addrs-subset) 'create-canonical-address-list)))
                (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                            'las-to-pas 'l-addrs mfc state)
                           (l-addrs))
                ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
                (syntaxp (and (consp l-addrs)
                              (eq (car l-addrs) 'create-canonical-address-list)))
                (not (member-p index (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))))
                (subset-p l-addrs-subset l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
           (equal (member-p index (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))
                  nil))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance mv-nth-1-las-to-pas-subset-p)
                 (:instance not-member-p-of-superset-is-not-member-p-of-subset
                            (e index)
                            (y (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                            (x (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))))
           :in-theory (e/d* () (mv-nth-1-las-to-pas-subset-p)))))

(defun find-l-addrs-from-program-at-term (thm l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm state))
  (b* ((call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc)))
       (call (if (not call)
                 (acl2::find-call-lst 'program-at-alt (acl2::mfc-clause mfc))
               nil))
       ((when (not call)) nil)
       (addresses (cadr call))
       ((when (not (equal (car addresses) 'create-canonical-address-list)))
        nil))
    `((,l-addrs-var . ,addresses))))

||#

;; ======================================================================
