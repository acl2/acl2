; Tests of the basic prover.
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prover-basic") ; todo: test separately?
(include-book "prover-basic-clause-processor")
(include-book "kestrel/utilities/deftest" :dir :system)

;; TODO: Add more tests

(deftest
  (prove-implication-with-basic-prover *t*
                                       '((0 natp '7))
                                       :rule-lists (list '(implies))))

;; todo: get this to prove without splitting (but there is only 1 literal before we split)
(deftest
  (prove-implication-with-basic-prover '((1 natp 0) (0 . x))
                                       '((1 natp 0) (0 . x))
                                       :rule-lists (list '(implies))
                                       ))

(deftest
  (must-fail (prove-implication-with-basic-prover *t* '((1 natp 0) (0 . x))
                                                  :rule-lists (list '(implies))
                                                  )))

(deftest
  (must-fail (prove-implication-with-basic-prover '((1 natp 0) (0 . x)) '((1 natp 0) (0 . y))
                                                  :rule-lists (list '(implies)) ;todo
                                                  )))

(defthm-with-basic-prover-clause-processor test1
  (natp 7))

(defthm-with-basic-prover-clause-processor test1b
  (not (natp 'a)))

(defthm-with-basic-prover-clause-processor test2
  (implies (natp x)
           (natp x)))

(must-fail
 (defthm-with-basic-prover-clause-processor test3
   (implies (integerp x)
            (natp x))))

(defthm-with-basic-prover-clause-processor test4
  (implies t
           (natp 7)))

(defthm-with-basic-prover-clause-processor boolor-1
  (boolor t x))

(defthm-with-basic-prover-clause-processor boolor-2
  (boolor x t))

(must-fail
 (defthm-with-basic-prover-clause-processor boolor-3
   (boolor nil (natp x))))

(must-fail
 (defthm-with-basic-prover-clause-processor boolor-4
   (boolor (natp x) nil)))

(must-fail
 (defthm-with-basic-prover-clause-processor boolor-5
   (boolor x x)))

(must-fail
 (defthm-with-basic-prover-clause-processor boolor-6
   (boolor (natp x) (natp x))))

(defthm-with-basic-prover-clause-processor not-1
  (not nil)
  :rule-classes nil
  )

(must-fail
 (defthm-with-basic-prover-clause-processor not-2
   (not t)
   :rule-classes nil
   ))

(must-fail
 (defthm-with-basic-prover-clause-processor not-3
   (not 7)
   :rule-classes nil
   ))

(must-fail
 (defthm-with-basic-prover-clause-processor implies-or-1
   (implies (or (natp x) (natp y))
            (natp y))))

(defthm-with-basic-prover-clause-processor or-1
  (implies x
           (or x y)))

(defthm-with-basic-prover-clause-processor or-2
  (implies y
           (or x y)))

(defthm-with-basic-prover-clause-processor or-3
  (implies (or x y)
           (or x y)))

(defthm-with-basic-prover-clause-processor or-3b
  (implies (or (natp x) (natp y))
           (or (natp x) (natp y))))

(must-fail
 (defthm-with-basic-prover-clause-processor or-false-1
   (implies (or x y)
            x)))

(must-fail
 (defthm-with-basic-prover-clause-processor or-false-2
   (implies (or x y)
            y)))

(defthm-with-basic-prover-clause-processor and-1
  (implies (and x y)
           x)
  :rule-classes nil)

(defthm-with-basic-prover-clause-processor and-2
  (implies (and x y)
           y)
  :rule-classes nil)

(must-fail
 (defthm-with-basic-prover-clause-processor and-false-1
   (implies x
            (and x y))
   :rule-classes nil))

(must-fail
 (defthm-with-basic-prover-clause-processor and-false-2
   (implies y
            (and x y))
   :rule-classes nil))


;todo
;; (defthm-with-basic-prover-clause-processor implies-boolor-1
;;   (implies (boolor (natp x) (natp y)) (natp y))
;;   :rules (implies booleanp-of-boolor)
;;   )

(defthm-with-basic-prover-clause-processor if-1
  (implies (natp x)
           (equal (if (natp x) x y) x))
  :rule-classes nil)

(defthm-with-basic-prover-clause-processor if-2
  (implies (member-equal '1 x)
           (equal (if (member-equal '1 x) x y) x))
;  :rules (implies equal-same)
  :rule-classes nil
  )

;; only one literal, and its a negated equality of a var that could be used to
;; substitute.  After substitution, no literals are left.
(must-fail
 (defthm-with-basic-prover-clause-processor subst-1
   (not (equal x (car y)))
   :rule-classes nil
   ))

;; simple variable subst example
(defthm-with-basic-prover-clause-processor subst-2
  (implies (equal x (car y))
           (equal (len x) (len (car y))))
  :rule-classes nil)

(deftest
  (local (include-book "boolean-rules-axe")) ;drop?
  (local (include-book "basic-rules"))

  (must-fail
   ;; a test that involves elim.
   (defthm-with-basic-prover-clause-processor tuple-elim-1
     (implies (and (true-listp x)
                   (equal 3 (len x)))
              (equal (len x) y))
     :rules (implies equal-same if-becomes-boolif BOOLIF-WHEN-QUOTEP-ARG3 booleanp-of-booland booleanp-of-equal) ;todo: few to none of these rules should need to be given explicitly
     :rule-classes nil
     )))

;; ;todo: get this working. it loops!
;; (deftest
;;   (local (include-book "boolean-rules-axe")) ;drop?
;;   (local (include-book "basic-rules"))

;;   (defstub foo (x) t)

;;   ;; a test that involves elim.
;;   (defthm-with-basic-prover-clause-processor tuple-elim-2
;;     (implies (and (true-listp x)
;;                   (equal 3 (len x)))
;;              (equal (foo x) (foo (cons (car x) (cons (cadr x) (cons (caddr x) nil))))))
;;     :rules (implies equal-same if-becomes-boolif BOOLIF-WHEN-QUOTEP-ARG3 booleanp-of-booland booleanp-of-equal BOOLAND-OF-T BOOL-FIX$INLINE BOOLAND-OF-NIL-ARG1
;;                     BOOLAND-OF-NON-NIL-ARG2) ;todo: few to none of these rules should need to be given explicitly
;;     :rule-classes nil
;;     ))

;todo: the bool functions are not built into the basic evaluator

(deftest
  (local (include-book "boolean-rules-axe")) ;drop?
  (local (include-book "basic-rules"))
  ;; requires splitting if we have no if-lifting rules
  (defthm-with-basic-prover-clause-processor split-1
    (natp (if (natp x) 3 4))
    :rules (implies equal-same if-becomes-boolif BOOLIF-WHEN-QUOTEP-ARG3 booleanp-of-booland booleanp-of-equal) ;todo: few to none of these rules should need to be given explicitly
    :rule-classes nil
    ))

;todo: test splitting where the splitter has disjuncts (constant and not).  same for its negation.

;; We immediately drop the nil disjunct
(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-1
   (boolor nil x)
   :rule-classes nil
   ))

;; We immediately drop the nil disjunct
(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-2
   (boolor x nil)
   :rule-classes nil
   ))

;; We immediately harvest the t disjunct, which proves the clause
(defthm-with-basic-prover-clause-processor harvest-disjuncts-3
   (boolor t x)
   :rule-classes nil
   )

;; We immediately harvest the t disjunct, which proves the clause
(defthm-with-basic-prover-clause-processor harvest-disjuncts-4
   (boolor x t)
   :rule-classes nil
   )

;; We immediately harvest the non-nil disjunct, which proves the clause
(defthm-with-basic-prover-clause-processor harvest-disjuncts-5
   (boolor 7 x)
   :rule-classes nil
   )

;; We immediately harvest the non-nil disjunct, which proves the clause
(defthm-with-basic-prover-clause-processor harvest-disjuncts-6
   (boolor x 7)
   :rule-classes nil
   )

;; We immediately deal with the t
(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-7
   (not (booland t x))
   :rule-classes nil
   ))

;; We immediately deal with the t
(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-8
   (not (booland x t))
   :rule-classes nil
   ))

;; We immediately deal with the 7
(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-9
   (not (booland 7 x))
   :rule-classes nil
   ))

;; We immediately deal with the 7
(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-10
   (not (booland x 7))
   :rule-classes nil
   ))

;; We immediately prove the clause, due to the nil
(defthm-with-basic-prover-clause-processor harvest-disjuncts-11
  (not (booland nil x))
  :rule-classes nil
  )

;; We immediately prove the clause, due to the nil
(defthm-with-basic-prover-clause-processor harvest-disjuncts-12
  (not (booland x nil))
  :rule-classes nil
  )

(defthm-with-basic-prover-clause-processor harvest-disjuncts-13
  (not (not t))
  :rule-classes nil
  )

(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-13b
   (not (not (not t)))
   :rule-classes nil
   ))

(defthm-with-basic-prover-clause-processor harvest-disjuncts-13c
  (not (not (not (not t))))
  :rule-classes nil
  )

(defthm-with-basic-prover-clause-processor harvest-disjuncts-14
  (not (not 7))
  :rule-classes nil
  )

(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-14b
   (not (not (not 7)))
   :rule-classes nil
   ))

(defthm-with-basic-prover-clause-processor harvest-disjuncts-14c
  (not (not (not (not 7))))
  :rule-classes nil
  )

(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-15
   (not (not nil))
   :rule-classes nil
   ))

(defthm-with-basic-prover-clause-processor harvest-disjuncts-15b
  (not (not (not nil)))
  :rule-classes nil
  )

;; the literals that get extracted are x and y
(must-fail
 (defthm-with-basic-prover-clause-processor harvest-disjuncts-16
   (not (booland (not x) (not y)))
   :rule-classes nil
   ))

;; test with a non-boolean
;; todo: get this to work without splitting?
(defthm-with-basic-prover-clause-processor non-boolean-1
  (implies (member-equal a x) (member-equal a x))
  :rule-classes nil
  )

(defthm-with-basic-prover-clause-processor contra-1
  (boolor x (not x))
  :rule-classes nil
  )

(defthm-with-basic-prover-clause-processor contra-1b
  (boolor (not x) x)
  :rule-classes nil
  )

(must-fail
 (defthm-with-basic-prover-clause-processor contra-2
   (boolor (equal x 3) (not x))
   :rule-classes nil))

(must-fail
 (defthm-with-basic-prover-clause-processor contra-2b
   (boolor x (equal x t))
   :rule-classes nil))

(defthm-with-basic-prover-clause-processor contra-2c
  (boolor x (equal x nil))
  :rule-classes nil
  )

(must-fail
 (defthm-with-basic-prover-clause-processor contra-2d
   (boolor (not x) (not (equal x t)))
   :rule-classes nil))

(must-fail
 (defthm-with-basic-prover-clause-processor contra-2d
   (boolor (not x) (equal x t))
   :rule-classes nil))

;; TODO: Test that machinery for detecting contradictions when making the assumption-array

;; todo: get this to work:
;; (defthm-with-basic-prover-clause-processor test1
;;   (EQUAL (IF C NIL T) (EQUAL NIL C))
;;   :rule-classes nil)

(defstub foo (x) t)

(must-fail
 ;; Replaces the var with the constant '3
 (defthm-with-basic-prover-clause-processor contra-2d
   (implies (equal x 3)
            (foo x))
   :rule-classes nil))

(deftest
  (defthm integerp-when-unsigned-byte-p
    (implies (unsigned-byte-p size x) ;size is a free var
             (integerp x)))
  (defthm-with-basic-prover-clause-processor free-1
    (implies (unsigned-byte-p 16 x)
             (integerp x))
    :rules (integerp-when-unsigned-byte-p)))
