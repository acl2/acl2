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
(defthm equal-same
  (equal (equal x x)
         t)
  :rule-classes nil)

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
