; Tests of the basic prover.
;
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prover-basic")
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
