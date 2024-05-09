; Tests of the functions in renaming.lisp.
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "renaming")
(include-book "kestrel/utilities/deftest" :dir :system)

;; Test :use
(assert-equal
 (apply-renaming-to-hints '(("Goal" :use foo))
                          (acons 'foo 'bar nil))
 '(("Goal" :use bar)))

;; Test :use :instance
(assert-equal
 (apply-renaming-to-hints '(("Goal" :use (:instance foo (x x))))
                          (acons 'foo 'bar nil))
 '(("Goal" :use (:instance bar (x x)))))

;; Test :use with several :instances
(assert-equal
 (apply-renaming-to-hints '(("Goal" :use ((:instance foo (x x))
                                          (:instance baz (x x)))))
                          (acons 'foo 'bar nil))
 '(("Goal" :use ((:instance bar (x x))
                 (:instance baz (x x))))))

;; Test :in-theory (enable ...)
(assert-equal
 (apply-renaming-to-hints '(("Goal" :in-theory (enable foo)))
                          (acons 'foo 'bar nil))
 '(("Goal" :in-theory (enable bar))))

;; Test :in-theory (disable ...)
(assert-equal
 (apply-renaming-to-hints '(("Goal" :in-theory (disable foo)))
                          (acons 'foo 'bar nil))
 '(("Goal" :in-theory (disable bar))))

;; Test :in-theory (e/d ... ...)
(assert-equal
 (apply-renaming-to-hints '(("Goal" :in-theory (e/d (foo) (baz foo))))
                          (acons 'foo 'bar nil))
 '(("Goal" :in-theory (e/d (bar) (baz bar)))))

;; Test :induct
(assert-equal
 (apply-renaming-to-hints '(("Goal" :induct (foo x)))
                          (acons 'foo 'bar nil))
 '(("Goal" :induct (bar x))))

;; Test :expand (single term)
(assert-equal
 (apply-renaming-to-hints '(("Goal" :expand (foo x)))
                          (acons 'foo 'bar nil))
 '(("Goal" :expand (bar x))))

;; Test :expand (list of terms)
(assert-equal
 (apply-renaming-to-hints '(("Goal" :expand ((foo2 x) (foo x))))
                          (acons 'foo 'bar nil))
 '(("Goal" :expand ((foo2 x) (bar x)))))

;; Test :do-not-induct
(assert-equal
 (apply-renaming-to-hints '(("Goal" :do-not-induct t))
                          (acons 'foo 'bar nil))
 '(("Goal" :do-not-induct t)))

;; Test :by :functional-instance
(assert-equal
 (apply-renaming-to-hints '(("Goal" :by (:functional-instance generic-map-opener
                                                             (generic-fn (lambda (l) (double-int10 l)))
                                                             (generic-map (lambda (l) (map-double-int10 l))))))
                          (acons 'double-int10 'double-int20  (acons 'map-double-int10 'map-double-int20 nil)))
 '(("Goal" :by (:functional-instance generic-map-opener
                                   (generic-fn (lambda (l) (double-int20 l)))
                                   (generic-map (lambda (l) (map-double-int20 l)))))))

;; Test union-theories quoted rune list
(assert-equal
 (apply-renaming-to-hints '(("Goal" :in-theory (union-theories '((:definition map-double-int10))
                                                               (theory 'minimal-theory))))
                          (acons 'double-int10 'double-int20  (acons 'map-double-int10 'map-double-int20 nil)))
 '(("Goal" :in-theory (union-theories '((:definition map-double-int20))
                                      (theory 'minimal-theory)))))

;; Test a computed hint:
(assert-equal
 (apply-renaming-to-hints '((and stable-under-simplificationp '(:use foo)))
                          (acons 'foo 'bar nil))
 '((and stable-under-simplificationp '(:use bar))))
