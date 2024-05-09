; Tests for remove-hints.lisp
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-hints")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal (remove-unneeded-nils-in-e/d-args '((a) nil)) '((a)))
(assert-equal (remove-unneeded-nils-in-e/d-args '((a) (b) nil)) '((a) (b)))
(assert-equal (remove-unneeded-nils-in-e/d-args '((a) (b) nil nil)) '((a) (b)))
(assert-equal (remove-unneeded-nils-in-e/d-args '(nil nil (a))) '((a)))
(assert-equal (remove-unneeded-nils-in-e/d-args '(nil nil nil nil (a))) '((a)))
(assert-equal (remove-unneeded-nils-in-e/d-args '(nil nil (a) (b))) '((a) (b)))
(assert-equal (remove-unneeded-nils-in-e/d-args '((a) nil (b))) '((a b)))
(assert-equal (remove-unneeded-nils-in-e/d-args '((a) nil (b) (c))) '((a b) (c)))
(assert-equal (remove-unneeded-nils-in-e/d-args '((a) (b) nil (c) (d))) '((a) (b c) (d)))
(assert-equal (remove-unneeded-nils-in-e/d-args '((a) (b) nil (d))) '((a) (b d)))

(assert-equal (simplify-e/d '(e/d (a))) '(enable a))
(assert-equal (simplify-e/d '(e/d (a) nil)) '(enable a))
(assert-equal (simplify-e/d '(e/d nil nil (a))) '(enable a))
(assert-equal (simplify-e/d '(e/d nil (b))) '(disable b))

(assert! (mv-let (removal-type res)
           (remove-from-hint-keyword-value-list-in-nth-way 0 '(:in-theory (enable foo bar)))
           (and (equal removal-type '(:remove-enable-item foo))
                (equal res '(:in-theory (enable bar))))))

(assert! (mv-let (removal-type res)
           (remove-from-hint-keyword-value-list-in-nth-way 1 '(:in-theory (enable foo bar)))
           (and (equal removal-type '(:remove-enable-item bar))
                (equal res '(:in-theory (enable foo))))))

(assert! (mv-let (removal-type res)
           (remove-from-hint-keyword-value-list-in-nth-way 0 '(:in-theory (e/d (foo) (bar))))
           (and (equal removal-type '(:remove-enable-item foo))
                (equal res '(:in-theory (disable bar))))))

(assert! (mv-let (removal-type res)
           (remove-from-hint-keyword-value-list-in-nth-way 1 '(:in-theory (e/d (foo) (bar))))
           (and (equal removal-type '(:remove-disable-item bar))
                (equal res '(:in-theory (enable foo))))))
