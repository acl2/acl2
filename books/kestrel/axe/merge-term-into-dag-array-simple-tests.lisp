; Tests of merge-term-into-dag-array-simple, etc
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "merge-term-into-dag-array-simple")
(include-book "std/testing/assert-equal" :dir :system)

(assert-event (mv-let (erp dag)
                (merge-term-into-dag-simple '(foo x) (acons 'x 1 nil) '((1 baz 0) (0 . y)))
                (and (not erp)
                     (equal dag '((2 foo 1) (1 baz 0) (0 . y))))))

;; wrapping the dag around a node other than the top one
(assert-event (mv-let (erp dag)
                (merge-term-into-dag-simple '(foo x) (acons 'x 0 nil) '((1 baz 0) (0 . y)))
                (and (not erp)
                     (equal dag '((1 foo 0) (0 . y))))))

;; test where the initial dag is actually a constant (which essentially gets ignored)
(assert-event (mv-let (erp dag)
                (merge-term-into-dag-simple '(foo x) (acons 'x ''5 nil) ''hello)
                (and (not erp)
                     (equal dag '((0 foo '5))))))
