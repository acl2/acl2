#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;; Keep this list of include-books in sync with the list in the .acl2 file:
;;
(include-book "gacc3")


;(local (include-book "rtl/rel4/arithmetic/floor" :dir :system))
;(local (include-book "rtl/rel4/arithmetic/numerator" :dir :system))

(in-theory (disable g* s* x*))
(in-theory (enable 
            (:induction s*)
            (:induction g*)
            (:induction x*)
            ))

(in-theory (disable
            DISJOINT-MESH-G*-FIX
            DISJOINT-G*-BLKS-G*-FIX-2
            DISJOINT-BLKS-G*-FIX
            DISJOINT-MESH-FROM-X*-INSTANCE
            DISJOINT-BLKS-FROM-X*-INSTANCE
            DISJOINT-BLK-SUBBAGP-RIGHT
;            bag::DISJOINT-CONS
;            DEFAULT-CDR
        ;    DEFAULT-CAR
            (:TYPE-PRESCRIPTION BINARY-APPEND)

; Modified by Matt K. after Jared D.'s check-in to acl2-books svn revision 633,
; which removed the following rule: I disabled the relatively new built-in rule
; instead.
;           (:TYPE-PRESCRIPTION acl2::APPEND-TRUE-LISTP-TYPE-PRESCRIPTION)
            (:type-prescription acl2::true-listp-append)
            ))

(in-theory (disable
            DISJOINT-BLK-SUBBAGP-LEFT
;            bag::DISJOINT-of-APPEND
            blk-disjoint-from-blk-1
            blk-disjoint-from-blk-2
;            DISJOINT
            bag::UNIQUE-of-APPEND ;remove?
;            bag::SUBBAGP-IMPLIES-SUBBAGP-APPEND-REC
        ;    bag::SUBBAGP-IMPLIES-SUBBAGP-APPEND-CAR
;            bag::REMOVE-bag-APPEND
;            bag::META-SUBBAGP
            ))



;trying with just the regular unicity-of-0
;; ;why??
;; (defthm integerp-unicity-of-0
;;   (implies
;;    (integerp x)
;;    (equal (+ 0 x) x)))
;;
;;(in-theory (disable UNICITY-OF-0))

;; Typically, there will be a uniqueness hyp. in your theorem.  By
;; starting out in a state in which this statement can be simplified
;; as much as possible without disturbing the rest of the terms, you
;; will probably save quite a bit of time in the long run.

(deftheory simplify-uniqueness
  (union-theories
   `(
     (BLKS)
     (MAX-OFFSET)
     (MESH)
     FLATTEN
     SYNTAX-ATOM
     SYNTAX-CONSP-OR-SYMBOL
     list::append-associative
;     bag::APPEND-NIL
;     INTEGERP-UNICITY-OF-0
     OPEN-BLKS
     OPEN-G*
     OPEN-MESH
     TRUE-LISTP-BLK
     TRUE-LISTP-MESH
     (:TYPE-PRESCRIPTION RX)
     (:TYPE-PRESCRIPTION UNIQUE))
   (theory 'ground-zero)))

(in-theory (disable
            ;;UNIQUE RULES
            ;; bag::UNIQUE-DESPITE-REMOVE-bag
            bag::*TRIGGER*-SYNTAX-EV-SYNTAX-SUBBAGP ;;bzo move this disable to bags/top?
            ;;bag::SUBBAGP-UNIQUENESS
            UNIQUE-BLKS-PTR-INDEPENDENT-OF-PTR
            UNIQUE-BLK
            UNIQUE-BLK-REC
            ;;bag::UNIQUE-of-APPEND
            ;;UNIQUE
            ;;DISJOINT RULES
            bag::*TRIGGER*-UNIQUE-SUBBAGPS-IMPLIES-DISJOINTNESS
            bag::*TRIGGER*-SUBBAGP-PAIR-DISJOINT
            ;;bag::SUBBAGP-DISJOINT-COMMUTE
            ;;    bag::SUBBAGP-DISJOINT
            DISJOINT-MESH-G*-FIX
            DISJOINT-G*-BLKS-G*-FIX-2
            DISJOINT-BLKS-G*-FIX
            DISJOINT-MESH-FROM-X*-INSTANCE
            DISJOINT-BLKS-FROM-X*-INSTANCE
            DISJOINT-BLK-PTR-BLKS-PTR-INDEPENDENT-OF-PTR-0-HYP
            DISJOINT-BLK-PTR-BLKS-PTR-INDEPENDENT-OF-PTR-0-CONCLUSION
            DISJOINT-BLK-PTR-BLKS-PTR-INDEPENDENT-OF-PTR
            DISJOINT-RELOCATION
            ;;DISJOINT-BLK-SUBBAGP-LEFT
            ;;DISJOINT-BLK-SUBBAGP-RIGHT
            disjoint-of-blk-recs-1
            disjoint-of-blk-recs-2
            DISJOINT-BLK-REC-SUBBAGP-LEFT
            DISJOINT-BLK-REC-SUBBAGP-RIGHT
            DISJOINT-BLK-REC-SUBBAGP
            ;;bag::DISJOINT-of-APPEND
            bag::DISJOINT-COMMUTATIVE ;;bzo really?
            ;;DISJOINT-NIL         
            ;;bag::DISJOINT-CONS
            ;;DISJOINT
            
            ;;SUBBAGP RULES
            bag::V2-SYNTAX-REMOVE-bag-IMPLICATION
            bag::V2-SYNTAX-REMOVE-bag-IMPLICATION-LEMMA
            ;;PERM-SUBBAGP-SUBBAGP-2
            bag::V1-SYNTAX-REMOVE-bag-IMPLICATION
            ;;V1-SYNTAX-REMOVE-LIST-IMPLICATION-LEMMA
            ;;bag::SUBBAGP-REMOVE-bag-SUBBAGP-APPEND
            ;;bag::SUBBAGP-MEMBERp-REMOVE-1
            ;;SUBBAGP-PERM-SUBBAGP-CONS
            ;;bag::CONSP-SUBBAGP
            ;;bag::PERM-SUBBAGP-SUBBAGP
            ;;bag::SUBBAGP-APPEND-NIL
            bag::SYNTAX-SUBBAGP-IMPLEMENTS-SUBBAGP
            ;;REMOVE-1-SUBBAGP-APPEND
            bag::V0-REMOVE-1-SUBBAGP
            ;;bag::SUBBAGP-CDR-REMOVE-1
            ;;bag::SYNTAX-REMOVE-bag-1-NOT bzo this disappeared
            ;;V1-REMOVE-1-SUBBAGP
            ;;bag::SUBBAGP-REMOVE-bag-APPEND
            bag::SYNTAX-REMOVE-bag-1-IMPLEMENTS-SUBBAGP
            ;;bag::SUBBAGP-APPEND
            BLK-REC-LOWER-SUBBAGP
            BLK-UPPER-SUBBAGP
            BLK-REC-UPPER-SUBBAGP
            ;;bag::SUBBAGP-REMOVE-BAG
            ;;bag::SUBBAGP-REMOVE
            ;;SUBBAGP-X-X we want this one
            ;;bag::SUBBAGP-REMOVE-1
            ;;bag::SUBBAGP-IMPLIES-REMOVE-bag
            ;;bag::NON-CONSP-SUBBAGP
            ;;SUBBAGP-CDR
            ;;bag::SUBBAGP-CHAINING
            ;;SUBBAGP-IMPLIES-COMMON-MEMBERS-ARE-IRRELEVANT
            ;;SUBBAGP-APPEND-APPEND
            ;;SUBBAGP-APPEND-APPEND-LEFT
            ;;SUBBAGP-IMPLIES-SUBBAGP-APPEND-CAR
            ;;SUBBAGP-IMPLIES-SUBBAGP-APPEND-REC
            ;;bag::SUBBAGP-CONS
            ;;SUBBAGP-IMPLIES-SUBBAGP-CONS
            ;;SUBBAGP already out
            
            ;;MEMBERp RULES
            ;;bag::SYNTAX-MEMBERP-IMPLEMENTS-MEMBERP
            ;;bag::UNIQUE-REMOVE-1
            ;;bag::UNIQUE-MEMBERP-REMOVE
            ;;bag::SUBBAGP-CONS-CAR-MEMBERP
            MEMBERP-RELOCATE-BLK
            BLK-NON-MEMBERSHIP-MORE
            BLK-NON-MEMBERSHIP-LESS
            BLK-MEMBERSHIP
            BLK-MEMBERSHIP-SUBBAGP
            BLK-REC-MEMBERSHIP-SUBBAGP
            BLK-REC-MEMBERSHIP
            BLK-REC-NON-MEMBERSHIP-MORE
            BLK-REC-NON-MEMBERSHIP-LESS
            ;;bag::NOT-MEMBERP-IMPLIES-NOT-MEMBERP-REMOVE-1
            ;;bag::MEMBERP-FROM-DISJOINT-MEMBERP
            ;;bag::SUBBAGP-IMPLIES-MEMBERSHIP
            ;;bag::REMOVE-bag-ADDS-NO-TERMS
            ;;bag::MEMBERP-APPEND
            ;;bag::MEMBERP-SUBBAGP-NOT-CONSP-VERSION
            ;;bag::MEMBERP-SUBBAGP
            ;;bag::MEMBERP-X-REMOVE-X-IMPLIES-MEMBERP-X-REMOVE-1-Y
            ;;bag::MEMBERP-REMOVE
            ;;bag::memberp-remove-1-lemma ;;MEM-REM
            ;;MEMBERP
            ))


(defthm unsigned-byte-p--of--rv
  (implies (or (equal size 8)
               (equal size 16)
               (equal size 32)) ;;improve using a wintn rule?
  (acl2::unsigned-byte-p size (rv size gacc::off gacc::base gacc::spec))))

;;(in-theory (enable WFIXN-REWRITE-TO-LOGHEAD))

;;; ;this is a duplicate, because I wanted it to come last. -huh?
;; (defthmd unsigned-byte-p-wintn-equality-2
;;   (implies (or (equal size 8)
;;                (equal size 16)
;;                (equal size 32))
;;            (equal (gacc::wintn 8 size x)
;;                   (acl2::unsigned-byte-p size x))))
