; Tests of make-axe-rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-axe-rules")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (DEFTHM MEMBER-OF-CONS
    (EQUAL (MEMBER A (CONS B X))
           (IF (EQUAL A B)
               (CONS B X)
               (MEMBER A X)))
    :hints (("Goal" :in-theory (enable MEMBER))))

  ;; Tricky test involving remove-guard-holders:
  (assert-equal (make-axe-rules! '(member-of-cons) (w state))
                '(((MEMBER-EQUAL A (CONS B X))
                   (IF (EQUAL A B)
                       (CONS B X)
                       (MEMBER-EQUAL A X))
                   MEMBER-OF-CONS NIL))))

;; TODO: Why didn't this test pass?
;; (deftest
;;   (DEFTHM theorem-with-a-let
;;     (let ((x (+ 1 y)))
;;       (equal (+ x x)
;;              (+ 2 (* 2 y)))))
;;   (must-fail (make-axe-rules '(theorem-with-a-let) (w state))))

;; TODO: Add tests for syntaxp and axe-syntaxp hyps
