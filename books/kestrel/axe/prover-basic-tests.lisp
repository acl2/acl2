; Tests of the basic prover.
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/axe/prover-basic" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;; TODO: Add more tests

(deftest
  (prove-implication-with-basic-prover *t*
                                       '((0 natp '7))
                                       :rule-lists (list '(implies))))

(deftest
  (prove-implication-with-basic-prover '((1 natp 0) (0 . x)) '((1 natp 0) (0 . x))
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
  (natp 7)
  :rules (implies) ;todo
  )

(defthm-with-basic-prover-clause-processor test2
  (implies (natp x)
           (natp x))
  :rules (implies) ;todo
  )

(must-fail
 (defthm-with-basic-prover-clause-processor test3
   (implies (integerp x)
            (natp x))
   :rules (implies) ;todo
   ))

(defthm-with-basic-prover-clause-processor test4
  (implies t
           (natp 7))
  :rules (implies) ;todo
  )

(defthm-with-basic-prover-clause-processor boolor-1
  (boolor t x)
  :rules (posp) ;todo, if no rule given, the prover doesn't properly get disjuncts!
  )

(defthm-with-basic-prover-clause-processor boolor-2
  (boolor x t)
  :rules (posp) ;todo, if no rule given, the prover doesn't properly get disjuncts!
  )

(must-fail
 (defthm-with-basic-prover-clause-processor boolor-3
   (boolor nil (natp x))
   :rules (posp) ;todo, if no rule given, the prover doesn't properly get disjuncts!
   ))

(must-fail
 (defthm-with-basic-prover-clause-processor boolor-4
   (boolor (natp x) nil)
   :rules (posp) ;todo, if no rule given, the prover doesn't properly get disjuncts!
   ))

(defthm-with-basic-prover-clause-processor not-1
  (not nil)
  :rules (posp) ;todo, if no rule given, the prover doesn't properly get disjuncts!
  :rule-classes nil
  )

(must-fail
 (defthm-with-basic-prover-clause-processor not-2
   (not t)
   :rules (posp) ;todo, if no rule given, the prover doesn't properly get disjuncts!
   :rule-classes nil
   ))

(must-fail
 (defthm-with-basic-prover-clause-processor not-3
   (not 7)
   :rules (posp) ;todo, if no rule given, the prover doesn't properly get disjuncts!
   :rule-classes nil
   ))

;todo
;; (defthm-with-basic-prover-clause-processor implies-or-1
;;   (implies (or (natp x) (natp y)) (natp y))
;;   :rules (implies)
;;   )

;todo
;; (defthm-with-basic-prover-clause-processor implies-boolor-1
;;   (implies (boolor (natp x) (natp y)) (natp y))
;;   :rules (implies booleanp-of-boolor)
;;   )

;for axe
;dup
(defthmd equal-same
  (equal (equal x x)
         t))

;todo: prove without splitting.  need to look up if tests in assumptions somehow.
(defthm-with-basic-prover-clause-processor if-1
  (implies (natp x)
           (equal (if (natp x) x y) x))
  :rules (implies equal-same)
  :rule-classes nil
  )

;todo: prove without splitting.  need to look up if tests in assumptions somehow, even if non-boolean.
(defthm-with-basic-prover-clause-processor if-2
  (implies (member-equal '1 x)
           (equal (if (member-equal '1 x) x y) x))
  :rules (implies equal-same)
  :rule-classes nil
  )

;; only one literal, and its a negated equality of a var that could be used to substitute
(must-fail
 (defthm-with-basic-prover-clause-processor subst-1
   (not (equal x (car y)))
   :rules (implies equal-same) ;todo: doesn't try to subst if no rules given?
   :rule-classes nil
   ))

;; simple variable subst example
(defthm-with-basic-prover-clause-processor subst-2
  (implies (equal x (car y))
           (equal (len x) (len (car y))))
  :rules (implies equal-same)
  :rule-classes nil
  )

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
;;     :rules (implies equal-same if-becomes-boolif BOOLIF-WHEN-QUOTEP-ARG3 booleanp-of-booland booleanp-of-equal BOOLAND-OF-T BOOL-FIX$INLINE BOOLAND-OF-NIL
;;                     BOOLAND-OF-NON-NIL-ARG2) ;todo: few to none of these rules should need to be given explicitly
;;     :rule-classes nil
;;     ))

;todo: the bool functions are not built into the basic evaluator
