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

;todo
;; (defthm-with-basic-prover-clause-processor test5
;;   (boolor t x)
;;   ;:rules (implies) ;todo
;;   )
