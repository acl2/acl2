; Tests of restore-mv-lets-in-term
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "restore-mv-lets-in-term")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  ;; multi-valued:
  (defun foo (x) (mv x x))
  (assert-equal (restore-mv-lets-in-term '(mv-nth '0 (mv-list '2 (foo x))) (w state))
                ;; catches the return values of the call of FOO using mv-let:
                '(mv-let (v0 v1)
                   (foo x)
                   (declare (ignore v1))
                   v0)))

;; TODO: Should this work?
;; (deftest
;;   (assert-equal (restore-mv-lets-in-term '(mv-nth '0 (mv-list '2 (cons x (cons y 'nil)))) (w state))
;;                 '(mv-let (v0 v1)
;;                    (foo x)
;;                    (declare (ignore v1))
;;                    v0)))

;; TODO: Get this to work:
;; (deftest
;;   ;; multi-valued:
;;   (defun foo (x) (mv x x)) ;todo: weird error if this is missing
;;   (assert-equal (restore-mv-lets-in-term
;;                  '(+ (mv-nth '0 (mv-list '2 (foo x)))
;;                      (mv-nth '1 (mv-list '2 (foo x))))
;;                  (w state))
;;                 ;; catches the return values of the call of FOO using mv-let:
;;                 ' (MV-LET (V0 V1)
;;                     (FOO X)
;;                     (+ v0 v1))))
