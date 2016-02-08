;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "system-level-memory-utils")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;; Relating top-level memory accessors and updaters with rb and wb in
;; system-level mode.

;; ======================================================================

(local (in-theory (e/d* (entry-found-p-and-good-paging-structures-x86p
                         entry-found-p-and-lin-addr
                         ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                        (signed-byte-p
                         unsigned-byte-p))))

(local (xdoc::set-default-parents system-level-memory-utils))

;; ======================================================================

(defthm dumb-len-and-car-for-true-listp-rule
  (implies (and (equal (len xs) 1)
                (true-listp xs))
           (equal (list (car xs)) xs)))

(defthmd combine-bytes-simplify-lists-of-combine-bytes-to-append-aux
  (implies (and (byte-listp z)
                (natp x)
                (equal xs (list x)))
           (equal (cons (combine-bytes xs) z)
                  (append xs z))))

(defthm combine-bytes-simplify-lists-of-combine-bytes-to-append
  (implies (and (byte-listp xs)
                (byte-listp z)
                (equal (len xs) 1))
           (equal (cons (combine-bytes xs) z)
                  (append xs z)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance combine-bytes-simplify-lists-of-combine-bytes-to-append-aux
                            (xs xs) (x (car xs)))))))

(defthm dumb-len-and-consp-rule
  (implies (consp x)
           (equal (equal (len x) 0) nil)))

;; (defthm consp-rb
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (consp l-addrs)
;;                 (all-paging-entries-found-p l-addrs (double-rewrite x86))
;;                 (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
;;            (consp (mv-nth 1 (rb l-addrs r-w-x x86))))
;;   :hints (("Goal"
;;            :use ((:instance len-of-rb-in-system-level-mode))
;;            :in-theory (e/d* () (len-of-rb-in-system-level-mode))))
;;   :rule-classes (:type-prescription :rewrite))

(local
 (defthmd dumb-rule-about-canonical-address-p-of-lin-addr-from-l-addrs
   (implies (and (equal l-addrs (create-canonical-address-list n lin-addr))
                 (equal (len l-addrs) n)
                 (posp n))
            (canonical-address-p lin-addr))))

(local
 (defthm rb-value-in-system-level-mode-after-rb
   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:CONGRUENCE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:REWRITE MV-NTH-1-RB-AND-XLATE-EQUIV-X86S-DISJOINT)
   ;; (:REWRITE MV-NTH-2-RB-AND-XLATE-EQUIV-X86S)
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  l-addrs-1 r-w-x-1 cpl (double-rewrite x86))
                 (no-page-faults-during-translation-p
                  l-addrs-2 r-w-x-2 cpl (double-rewrite x86))
                 (not (programmer-level-mode x86)))
            (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
                   (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
   :hints (("Goal"
            :in-theory (e/d* () (force (force)))))))

(local (in-theory (e/d () (all-seg-visibles-equal-open))))

;; ======================================================================

(defthmd rm08-to-rb-in-system-level-mode
  (implies (force (paging-entries-found-p lin-addr (double-rewrite x86)))
           (equal (rm08 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 1 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             rb)
                            (signed-byte-p
                             unsigned-byte-p)))))

;; ----------------------------------------------------------------------

(local
 (defthmd rm16-to-rm08-in-system-level-mode
   (implies
    (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
         (equal l-addrs (create-canonical-address-list 2 lin-addr))
         (equal (len l-addrs) 2)
         (all-paging-entries-found-p l-addrs (double-rewrite x86))
         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
         (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
    (equal (rm16 lin-addr r-w-x x86)
           (b* (((mv & byte0 x86)
                 (rm08 (car l-addrs) r-w-x x86))
                ((mv & byte1 x86)
                 (rm08 (cadr l-addrs) r-w-x x86))
                (result (combine-bytes (list byte0 byte1))))
             (mv nil result x86))))
   :hints (("Goal"
            :in-theory (e/d* (all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              rm16
                              rm08
                              rb)
                             (cons-equal
                              signed-byte-p
                              unsigned-byte-p
                              bitops::logior-equal-0
                              rm08-to-rb-in-system-level-mode
                              (:meta acl2::mv-nth-cons-meta)
                              ;; mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                              force (force)))))))


(defthmd rm16-to-rb-in-system-level-mode
  (implies
   (forced-and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
               (equal l-addrs (create-canonical-address-list 2 lin-addr))
               (equal (len l-addrs) 2)
               (all-paging-entries-found-p l-addrs (double-rewrite x86))
               (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
               (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
   (equal (rm16 lin-addr r-w-x x86)
          (b* (((mv flg bytes x86)
                (rb l-addrs r-w-x x86))
               (result (combine-bytes bytes)))
            (mv flg result x86))))
  :hints (("Goal"
           :use ((:instance dumb-rule-about-canonical-address-p-of-lin-addr-from-l-addrs
                            (n 2)))
           :in-theory (e/d* (rm16-to-rm08-in-system-level-mode
                             rm08-to-rb-in-system-level-mode
                             rb-rb-split-reads-in-system-level-mode-state
                             rb-rb-split-reads-in-system-level-mode
                             all-paging-entries-found-p
                             no-page-faults-during-translation-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (combine-bytes
                             cons-equal
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;;----------------------------------------------------------------------

(local
 (defthmd rm32-to-rm08-in-system-level-mode
   (implies
    (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
         (equal l-addrs (create-canonical-address-list 4 lin-addr))
         (equal (len l-addrs) 4)
         (all-paging-entries-found-p l-addrs (double-rewrite x86))
         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
         (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
    (equal (rm32 lin-addr r-w-x x86)
           (b* (((mv & byte0 x86)
                 (rm08 lin-addr r-w-x x86))
                ((mv & byte1 x86)
                 (rm08 (+ 1 lin-addr) r-w-x x86))
                ((mv & byte2 x86)
                 (rm08 (+ 2 lin-addr) r-w-x x86))
                ((mv & byte3 x86)
                 (rm08 (+ 3 lin-addr) r-w-x x86))
                (result (combine-bytes (list byte0 byte1 byte2 byte3))))
             (mv nil result x86))))
   :hints (("Goal"
            :induct (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
            :in-theory (e/d* (all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              rm32
                              rm08
                              rb)
                             (cons-equal
                              signed-byte-p
                              unsigned-byte-p
                              bitops::logior-equal-0
                              rm08-to-rb-in-system-level-mode
                              (:meta acl2::mv-nth-cons-meta)
                              ;; mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                              force (force)))))))

(defthmd rm32-to-rb-in-system-level-mode
  ;; Needs rb-value-in-system-level-mode-after-rb.
  (implies
   (forced-and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
               (equal l-addrs (create-canonical-address-list 4 lin-addr))
               (equal (len l-addrs) 4)
               (all-paging-entries-found-p l-addrs (double-rewrite x86))
               (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
               (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
   (equal (rm32 lin-addr r-w-x x86)
          (b* (((mv flg bytes x86)
                (rb l-addrs r-w-x x86))
               (result (combine-bytes bytes)))
            (mv flg result x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance dumb-rule-about-canonical-address-p-of-lin-addr-from-l-addrs
                            (n 4)))
           :in-theory (e/d* (rm32-to-rm08-in-system-level-mode
                             rm08-to-rb-in-system-level-mode
                             rb-rb-split-reads-in-system-level-mode-state
                             rb-rb-split-reads-in-system-level-mode
                             all-paging-entries-found-p
                             no-page-faults-during-translation-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (combine-bytes
                             rb
                             cons-equal
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             rm08-values-and-xlate-equiv-x86s-disjoint
                             mv-nth-1-rb-and-xlate-equiv-x86s-disjoint
                             force (force))))))

;;----------------------------------------------------------------------

(local
 (defthmd rm64-to-rm08-in-system-level-mode
   ;; TO-DO: Speed this up!
   (implies
    (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
         (equal l-addrs (create-canonical-address-list 8 lin-addr))
         (equal (len l-addrs) 8)
         (all-paging-entries-found-p l-addrs (double-rewrite x86))
         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
         (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
    (equal (rm64 lin-addr r-w-x x86)
           (b* (((mv & byte0 x86)
                 (rm08 lin-addr r-w-x x86))
                ((mv & byte1 x86)
                 (rm08 (+ 1 lin-addr) r-w-x x86))
                ((mv & byte2 x86)
                 (rm08 (+ 2 lin-addr) r-w-x x86))
                ((mv & byte3 x86)
                 (rm08 (+ 3 lin-addr) r-w-x x86))
                ((mv & byte4 x86)
                 (rm08 (+ 4 lin-addr) r-w-x x86))
                ((mv & byte5 x86)
                 (rm08 (+ 5 lin-addr) r-w-x x86))
                ((mv & byte6 x86)
                 (rm08 (+ 6 lin-addr) r-w-x x86))
                ((mv & byte7 x86)
                 (rm08 (+ 7 lin-addr) r-w-x x86))
                (result (combine-bytes (list byte0 byte1 byte2 byte3 byte4 byte5 byte6 byte7))))
             (mv nil result x86))))
   :hints (("Goal"
            :induct (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
            :in-theory (e/d* (all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              rm64
                              rm08
                              rb)
                             ((:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2)
                              (:LINEAR ASH-MONOTONE-2)
                              (:REWRITE BITOPS::ASH-<-0)
                              (:REWRITE ACL2::NATP-WHEN-INTEGERP)
                              (:REWRITE ACL2::ASH-0)
                              (:REWRITE ACL2::ZIP-OPEN)
                              (:TYPE-PRESCRIPTION BITOPS::LOGIOR-NATP-TYPE)
                              (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)
                              (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-ERROR)
                              (:REWRITE MEMBER-LIST-P-AND-PAIRWISE-DISJOINT-P-AUX)
                              (:LINEAR ACL2::LOGHEAD-UPPER-BOUND)
                              (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
                              (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-VALUE-OF-ADDRESS-WHEN-ERROR)
                              (:DEFINITION MEMBER-LIST-P)
                              (:REWRITE LOGHEAD-OF-NON-INTEGERP)
                              (:REWRITE ACL2::LOGHEAD-IDENTITY)
                              (:DEFINITION OPEN-QWORD-PADDR-LIST-LIST)
                              (:REWRITE DEFAULT-+-2)
                              (:REWRITE DEFAULT-+-1)
                              (:DEFINITION OPEN-QWORD-PADDR-LIST)
                              (:REWRITE ACL2::NATP-WHEN-GTE-0)
                              (:REWRITE LOGHEAD-ZERO-SMALLER)
                              (:REWRITE ACL2::IFIX-NEGATIVE-TO-NEGP)
                              (:LINEAR <=-LOGIOR)
                              (:REWRITE ALL-SEG-VISIBLES-EQUAL-AUX-OPEN)
                              (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
                              (:LINEAR BITOPS::LOGIOR->=-0-LINEAR)
                              (:REWRITE OPEN-QWORD-PADDR-LIST-LIST-AND-MEMBER-LIST-P)
                              (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1)
                              (:REWRITE DEFAULT-<-1)
                              (:DEFINITION BINARY-APPEND)
                              (:TYPE-PRESCRIPTION MEMBER-LIST-P)
                              (:REWRITE ACL2::NEGP-WHEN-LESS-THAN-0)
                              (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                              (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS)
                              (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
                              (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P)
                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-1)
                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-0)
                              (:REWRITE MEMBER-P-CDR)
                              (:DEFINITION ADDR-RANGE)
                              (:REWRITE ACL2::NEGP-WHEN-INTEGERP)
                              (:TYPE-PRESCRIPTION ASH)
                              (:REWRITE SUBSET-LIST-P-AND-MEMBER-LIST-P)
                              (:TYPE-PRESCRIPTION BINARY-LOGIOR)
                              (:TYPE-PRESCRIPTION TRUE-LISTP-ADDR-RANGE)
                              (:TYPE-PRESCRIPTION CONSP-ADDR-RANGE)
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
                              (:TYPE-PRESCRIPTION GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES)
                              (:DEFINITION BYTE-LISTP)
                              (:LINEAR MEMI-IS-N08P)
                              (:REWRITE PAIRWISE-DISJOINT-P-AUX-AND-APPEND)
                              (:REWRITE CAR-ADDR-RANGE)
                              (:LINEAR UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                              (:REWRITE DEFAULT-<-2)
                              (:REWRITE X86P-MV-NTH-2-IA32E-ENTRIES-FOUND-LA-TO-PA)
                              (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
                              (:REWRITE MEMBER-LIST-P-NO-DUPLICATES-LIST-P-AND-MEMBER-P)
                              (:TYPE-PRESCRIPTION NATP)
                              (:REWRITE LOGHEAD-UNEQUAL)
                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
                              (:LINEAR SIZE-OF-COMBINE-BYTES)
                              (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-MEMBER-P)
                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-MEMBER-P)
                              (:REWRITE DISJOINT-P-SUBSET-P)
                              (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
                              (:REWRITE CDR-ADDR-RANGE)
                              (:REWRITE ALL-MEM-EXCEPT-PAGING-STRUCTURES-EQUAL-AUX-OPEN)
                              (:TYPE-PRESCRIPTION MULT-8-QWORD-PADDR-LIST-LISTP)
                              (:REWRITE
                               GOOD-PAGING-STRUCTURES-X86P-IMPLIES-MULT-8-QWORD-PADDR-LIST-LISTP-PAGING-STRUCTURE-ADDRS)
                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-SUBSET-P)
                              (:REWRITE ALL-PAGING-ENTRIES-FOUND-P-SUBSET-P)
                              (:TYPE-PRESCRIPTION NEGP)
                              (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-SUBSET-P)
                              (:REWRITE CONSTANT-UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                              (:LINEAR BITOPS::UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                              (:LINEAR MEMBER-P-POS-VALUE)
                              (:LINEAR MEMBER-P-POS-1-VALUE)
                              (:TYPE-PRESCRIPTION BYTE-LISTP)
                              (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P-PHYSICAL-ADDRESS-LISTP)
                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P)
                              (:REWRITE MEMBER-P-AND-MULT-8-QWORD-PADDR-LISTP)
                              (:REWRITE MEMBER-LIST-P-AND-MULT-8-QWORD-PADDR-LIST-LISTP)
                              (:REWRITE RIGHT-SHIFT-TO-LOGTAIL)
                              (:DEFINITION RB-1)
                              (:TYPE-PRESCRIPTION ZIP)
                              (:REWRITE COMBINE-BYTES-SIMPLIFY-LISTS-OF-COMBINE-BYTES-TO-APPEND)
                              (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS)
                              (:REWRITE UNSIGNED-BYTE-P-OF-ASH)
                              (:REWRITE RB-1-RETURNS-BYTE-LISTP)
                              (:TYPE-PRESCRIPTION RB-1-RETURNS-BYTE-LISTP)
                              (:REWRITE RVM08-NO-ERROR)
                              (:REWRITE UNSIGNED-BYTE-P-OF-LOGIOR)
                              (:TYPE-PRESCRIPTION BOOLEANP)
                              (:REWRITE X86P-MV-NTH-2-RVM08-UNCHANGED)
                              (:REWRITE RB-1-ACCUMULATOR-THM)
                              (:REWRITE
                               CANONICAL-ADDRESS-LISTP-FIRST-INPUT-TO-ALL-PAGING-ENTRIES-FOUND-P)
                              cons-equal
                              signed-byte-p
                              unsigned-byte-p
                              bitops::logior-equal-0
                              rm08-to-rb-in-system-level-mode
                              (:meta acl2::mv-nth-cons-meta)
                              force (force)))))))

(defthmd rm64-to-rb-in-system-level-mode
  ;; TO-DO: Speed this up!
  ;; Needs rb-value-in-system-level-mode-after-rb.
  (implies
   (forced-and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
               (equal l-addrs (create-canonical-address-list 8 lin-addr))
               (equal (len l-addrs) 8)
               (all-paging-entries-found-p l-addrs (double-rewrite x86))
               (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
               (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
   (equal (rm64 lin-addr r-w-x x86)
          (b* (((mv flg bytes x86)
                (rb l-addrs r-w-x x86))
               (result (combine-bytes bytes)))
            (mv flg result x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance dumb-rule-about-canonical-address-p-of-lin-addr-from-l-addrs
                            (n 8)))
           :in-theory (e/d* (rm64-to-rm08-in-system-level-mode
                             rm08-to-rb-in-system-level-mode
                             rb-rb-split-reads-in-system-level-mode-state
                             rb-rb-split-reads-in-system-level-mode
                             all-paging-entries-found-p
                             no-page-faults-during-translation-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            ((:REWRITE MEMBER-LIST-P-AND-PAIRWISE-DISJOINT-P-AUX)
                             (:DEFINITION MEMBER-LIST-P)
                             (:DEFINITION BYTE-LISTP)
                             (:DEFINITION OPEN-QWORD-PADDR-LIST-LIST)
                             (:DEFINITION OPEN-QWORD-PADDR-LIST)
                             (:TYPE-PRESCRIPTION CONSP-RB)
                             (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                             (:REWRITE OPEN-QWORD-PADDR-LIST-LIST-AND-MEMBER-LIST-P)
                             (:TYPE-PRESCRIPTION MEMBER-LIST-P)
                             (:REWRITE ALL-PAGING-ENTRIES-FOUND-P-MEMBER-P)
                             (:REWRITE DEFAULT-+-2)
                             (:TYPE-PRESCRIPTION MEMBER-P)
                             (:REWRITE DEFAULT-+-1)
                             (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
                             (:REWRITE MEMBER-P-CANONICAL-ADDRESS-LISTP)
                             (:DEFINITION ADDR-RANGE)
                             (:REWRITE MEMBER-P-CDR)
                             (:REWRITE ALL-PAGING-ENTRIES-FOUND-P-SUBSET-P)
                             (:REWRITE SUBSET-LIST-P-AND-MEMBER-LIST-P)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
                             (:REWRITE ACL2::LOGHEAD-IDENTITY)
                             (:TYPE-PRESCRIPTION TRUE-LISTP-ADDR-RANGE)
                             (:TYPE-PRESCRIPTION GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES)
                             (:TYPE-PRESCRIPTION CONSP-ADDR-RANGE)
                             (:REWRITE LOGHEAD-OF-NON-INTEGERP)
                             (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
                             (:REWRITE ACL2::IFIX-WHEN-INTEGERP)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-1)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-0)
                             (:REWRITE PAIRWISE-DISJOINT-P-AUX-AND-APPEND)
                             (:TYPE-PRESCRIPTION SEG-VISIBLEI-IS-N16P)
                             (:REWRITE ALL-SEG-VISIBLES-EQUAL-AUX-OPEN)
                             (:TYPE-PRESCRIPTION ATOM-LISTP)
                             (:REWRITE CAR-ADDR-RANGE)
                             (:REWRITE LOGHEAD-ZERO-SMALLER)
                             (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-SUBSET-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
                             (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-SUBSET-P)
                             (:TYPE-PRESCRIPTION SUBSET-P)
                             (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P)
                             (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
                             (:REWRITE MEMBER-LIST-P-NO-DUPLICATES-LIST-P-AND-MEMBER-P)
                             (:REWRITE UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:DEFINITION N08P$INLINE)
                             (:REWRITE SUBSET-P-CDR-Y)
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                             (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-MEMBER-P)
                             (:REWRITE
                              GOOD-PAGING-STRUCTURES-X86P-IMPLIES-MULT-8-QWORD-PADDR-LIST-LISTP-PAGING-STRUCTURE-ADDRS)
                             (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
                             (:REWRITE RB-RETURNS-X86-PROGRAMMER-LEVEL-MODE)
                             (:TYPE-PRESCRIPTION MULT-8-QWORD-PADDR-LIST-LISTP)
                             (:TYPE-PRESCRIPTION IFIX)
                             (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-MEMBER-P)
                             (:REWRITE DISJOINT-P-SUBSET-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
                             (:REWRITE CDR-ADDR-RANGE)
                             (:REWRITE MV-NTH-2-RM08-AND-XLATE-EQUIV-X86S)
                             (:REWRITE PROGRAMMER-LEVEL-MODE-RM08-NO-ERROR)
                             (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION RB-RETURNS-BYTE-LISTP)
                             (:TYPE-PRESCRIPTION BOOLEANP)
                             (:TYPE-PRESCRIPTION BYTE-LISTP-APPEND)
                             (:REWRITE N08P-MV-NTH-1-RM08)
                             (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)
                             (:REWRITE XR-RM08-STATE-IN-SYSTEM-LEVEL-MODE)
                             (:REWRITE UNICITY-OF-0)
                             (:REWRITE XR-RM08-STATE-IN-PROGRAMMER-LEVEL-MODE)
                             (:DEFINITION FIX)
                             (:REWRITE CANONICAL-ADDRESS-LISTP-FIRST-INPUT-TO-ALL-PAGING-ENTRIES-FOUND-P)
                             (:TYPE-PRESCRIPTION X86P-RM08)
                             (:REWRITE
                              PAGE-TABLE-ENTRY-ADDR-FOUND-P-IMPLIES-PAGE-DIRECTORY-ENTRY-ADDR-FOUND-P)
                             (:REWRITE
                              PAGE-DIRECTORY-ENTRY-ADDR-FOUND-P-IMPLIES-PAGE-DIR-PTR-TABLE-ENTRY-ADDR-FOUND-P)
                             (:REWRITE
                              PAGE-DIR-PTR-TABLE-ENTRY-ADDR-FOUND-P-IMPLIES-PML4-TABLE-ENTRY-ADDR-FOUND-P)
                             (:LINEAR MEMBER-P-POS-VALUE)
                             (:LINEAR MEMBER-P-POS-1-VALUE)
                             combine-bytes
                             rb
                             cons-equal
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             rm08-values-and-xlate-equiv-x86s-disjoint
                             mv-nth-1-rb-and-xlate-equiv-x86s-disjoint
                             force (force))))))

;; ======================================================================

(defthmd wm08-to-wb-in-system-level-mode
  (implies (forced-and (paging-entries-found-p lin-addr (double-rewrite x86))
                       (unsigned-byte-p 8 byte))
           (equal (wm08 lin-addr byte x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 1 lin-addr)
                       (list byte))
                      x86)))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm08
                             wb)
                            (signed-byte-p
                             unsigned-byte-p)))))

;; ----------------------------------------------------------------------

(defthmd wm16-to-wm08-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 2 lin-addr))
        (equal (len l-addrs) 2)
        (all-paging-entries-found-p l-addrs (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
        (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
   (equal (wm16 lin-addr word x86)
          (b* (((mv & x86)
                (wm08 lin-addr (part-select word :low 0 :width 8) x86))
               ((mv & x86)
                (wm08 (1+ lin-addr) (part-select word :low 8 :width 8) x86)))
            (mv nil x86))))
  :hints (("Goal"
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             wm16
                             wm08
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wm08-to-wb-in-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

(defthmd wm16-to-wb-in-system-level-mode
  (implies
   (forced-and
    (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
    (equal l-addrs (create-canonical-address-list 2 lin-addr))
    (equal (len l-addrs) 2)
    (all-paging-entries-found-p l-addrs (double-rewrite x86))
    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
    (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
   (equal (wm16 lin-addr word x86)
          (b* (((mv & x86)
                (wb (create-addr-bytes-alist l-addrs (byte-ify 2 word)) x86)))
            (mv nil x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (wm16-to-wm08-in-system-level-mode
                             wm08-to-wb-in-system-level-mode
                             wb-wb-split-reads-in-system-level-mode
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ----------------------------------------------------------------------

(defthmd wm32-to-wm08-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 4 lin-addr))
        (equal (len l-addrs) 4)
        (all-paging-entries-found-p l-addrs (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
        (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
   (equal (wm32 lin-addr dword x86)
          (b* (((mv & x86)
                (wm08 lin-addr (part-select dword :low 0 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 1 lin-addr) (part-select dword :low 8 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 2 lin-addr) (part-select dword :low 16 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 3 lin-addr) (part-select dword :low 24 :width 8) x86)))
            (mv nil x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 4)
                            (end-addr (+ 3 lin-addr))))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             wm32
                             wm08
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wm08-to-wb-in-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

(defthmd wm32-to-wb-in-system-level-mode
  (implies
   (forced-and
    (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
    (equal l-addrs (create-canonical-address-list 4 lin-addr))
    (equal (len l-addrs) 4)
    (all-paging-entries-found-p l-addrs (double-rewrite x86))
    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
    (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
   (equal (wm32 lin-addr dword x86)
          (b* (((mv & x86)
                (wb (create-addr-bytes-alist l-addrs (byte-ify 4 dword)) x86)))
            (mv nil x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (wm32-to-wm08-in-system-level-mode
                             wm08-to-wb-in-system-level-mode
                             wb-wb-split-reads-in-system-level-mode
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ----------------------------------------------------------------------

(local
 (defthm open-create-canonical-address-list
   (implies (and (canonical-address-p lin-addr)
                 (posp n)
                 (canonical-address-p (+ -1 n lin-addr)))
            (equal (create-canonical-address-list n lin-addr)
                   (cons lin-addr
                         (create-canonical-address-list (+ -1 n) (+ 1 lin-addr)))))
   :hints (("Goal" :in-theory (e/d* () (signed-byte-p))))))

(defthmd wm64-to-wm08-in-system-level-mode
  ;; TO-DO: Speed this up!
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 8 lin-addr))
        (equal (len l-addrs) 8)
        (all-paging-entries-found-p l-addrs (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
        (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
   (equal (wm64 lin-addr qword x86)
          (b* (((mv & x86)
                (wm08 lin-addr (part-select qword :low 0 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 1 lin-addr) (part-select qword :low 8 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 2 lin-addr) (part-select qword :low 16 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 3 lin-addr) (part-select qword :low 24 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 4 lin-addr) (part-select qword :low 32 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 5 lin-addr) (part-select qword :low 40 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 6 lin-addr) (part-select qword :low 48 :width 8) x86))
               ((mv & x86)
                (wm08 (+ 7 lin-addr) (part-select qword :low 56 :width 8) x86)))
            (mv nil x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 8)
                            (end-addr (+ 7 lin-addr))))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             wm64
                             wm08
                             byte-ify)
                            (open-qword-paddr-list-list
                             open-qword-paddr-list
                             member-list-p-and-pairwise-disjoint-p-aux
                             member-list-p
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wm08-to-wb-in-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

(defthmd wm64-to-wb-in-system-level-mode
  (implies
   (forced-and
    (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
    (equal l-addrs (create-canonical-address-list 8 lin-addr))
    (equal (len l-addrs) 8)
    (all-paging-entries-found-p l-addrs (double-rewrite x86))
    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
    (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
   (equal (wm64 lin-addr qword x86)
          (b* (((mv & x86)
                (wb (create-addr-bytes-alist l-addrs (byte-ify 8 qword)) x86)))
            (mv nil x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (wm64-to-wm08-in-system-level-mode
                             wm08-to-wb-in-system-level-mode
                             wb-wb-split-reads-in-system-level-mode
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ----------------------------------------------------------------------

(defthmd write-canonical-address-to-memory-to-wb-in-system-level-mode
  (implies
   (forced-and
    (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
    (equal l-addrs (create-canonical-address-list 8 lin-addr))
    (equal (len l-addrs) 8)
    (all-paging-entries-found-p l-addrs (double-rewrite x86))
    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
    (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86))
    (not (xr :programmer-level-mode 0 x86)))
   (equal (write-canonical-address-to-memory lin-addr signed-canonical-address x86)
          (b* (((mv & x86)
                (wb (create-addr-bytes-alist l-addrs (byte-ify 8 signed-canonical-address)) x86)))
            (mv nil x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 8)
                            (end-addr (+ 7 lin-addr))))
           :in-theory (e/d* (write-canonical-address-to-memory
                             wm64-to-wb-in-system-level-mode
                             remove-loghead-from-byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================

(local (in-theory (e/d (
                        ;; Reads
                        rm08-to-rb-in-system-level-mode
                        rm16-to-rb-in-system-level-mode
                        rm32-to-rb-in-system-level-mode
                        rm64-to-rb-in-system-level-mode
                        ;; Writes
                        wm08-to-wb-in-system-level-mode
                        wm16-to-wb-in-system-level-mode
                        wm32-to-wb-in-system-level-mode
                        wm64-to-wb-in-system-level-mode
                        write-canonical-address-to-memory-to-wb-in-system-level-mode
                        )
                       ())))

;; ======================================================================
