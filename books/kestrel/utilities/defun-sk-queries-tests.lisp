; DEFUN-SK Queries -- Tests
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the utilities in defun-sk-queries.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defun-sk-queries")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (assert! (not (defun-sk-check 'cons (w state)))))

(must-succeed
 (assert! (not (defun-sk-check 'not (w state)))))

(must-succeed
 (assert! (not (defun-sk-check 'len (w state)))))

(must-succeed*
 (defun-sk f () (exists b (atom b)))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-suff
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (exists b (atom b)) :strengthen nil)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-suff
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (exists b (atom b)) :strengthen t)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-suff
                 :default
                 t
                 t
                 t)))

(must-succeed*
 (defun-sk f () (exists b (atom b)) :skolem-name fw)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(atom b)
                 '(atom b)
                 'fw
                 'f-suff
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (exists b (atom b)) :thm-name ft)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'ft
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (exists (b) (atom b)) :witness-dcls nil)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-suff
                 :default
                 nil
                 nil
                 t)))

(must-succeed*
 (defun-sk f (a) (exists b (cons a b)))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(cons a b)
                 '(cons a b)
                 'f-witness
                 'f-suff
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f (a) (exists b (cons a b)) :strengthen nil :skolem-name fw)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(cons a b)
                 '(cons a b)
                 'fw
                 'f-suff
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f (a) (exists b (cons a b)) :strengthen t :thm-name ft)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(cons a b)
                 '(cons a b)
                 'f-witness
                 'ft
                 :default
                 t
                 t
                 t)))

(must-succeed*
 (defun-sk f (a1 a2 a3) (exists b (list a1 a2 a3 b))
   :skolem-name fw :thm-name ft)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b)
                 '(cons a1 (cons a2 (cons a3 (cons b 'nil))))
                 '(list a1 a2 a3 b)
                 'fw
                 'ft
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (exists (b1 b2) (cons b1 b2)))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b1 b2)
                 '(cons b1 b2)
                 '(cons b1 b2)
                 'f-witness
                 'f-suff
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f (a1 a2)
   (exists (b1 b2 b3) (let ((lhs (list a1 a2))
                            (rhs (list b1 b2 b3)))
                        (equal lhs rhs))))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'exists
                 '(b1 b2 b3)
                 '((lambda (lhs rhs) (equal lhs rhs))
                   (cons a1 (cons a2 'nil))
                   (cons b1 (cons b2 (cons b3 'nil))))
                 '(let ((lhs (list a1 a2))
                        (rhs (list b1 b2 b3)))
                    (equal lhs rhs))
                 'f-witness
                 'f-suff
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall b (atom b)))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-necc
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall b (atom b)) :rewrite :default)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-necc
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall b (atom b)) :rewrite :direct)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-necc
                 :direct
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall (b) (atom b))
   :rewrite (implies (not (atom b)) (not (f))))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-necc
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall b (atom b))
   :rewrite (implies (f) (atom b)))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-necc
                 :direct
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall b (atom b))
   :rewrite (implies (f) (not (consp b))))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-necc
                 :custom
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall b (atom b))
   :thm-name f-custom
   :rewrite (implies (f) (not (consp b))))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'f-witness
                 'f-custom
                 :custom
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall b (atom b)) :rewrite :direct :skolem-name fw)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b)
                 '(atom b)
                 '(atom b)
                 'fw
                 'f-necc
                 :direct
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f () (forall (b1 b2) (+ b1 b2)))
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b1 b2)
                 '(binary-+ b1 b2)
                 '(+ b1 b2)
                 'f-witness
                 'f-necc
                 :default
                 nil
                 t
                 t)))

(must-succeed*
 (defun-sk f (a) (forall (b1 b2 b3) (* a b1 b2 b3)) :witness-dcls nil)
 (assert-equal (defun-sk-check 'f (w state))
               (defun-sk-info 'forall
                 '(b1 b2 b3)
                 '(binary-* a (binary-* b1 (binary-* b2 b3)))
                 '(* a b1 b2 b3)
                 'f-witness
                 'f-necc
                 :default
                 nil
                 nil
                 t)))
