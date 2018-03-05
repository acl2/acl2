; SOFT (Second-Order Functions and Theorems) -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "implementation")
(include-book "kestrel/utilities/testing" :dir :system)

; Matt K. mod: Avoid ACL2(p) error from fvmeas-i (clause-processor returns more
; than two values).
(set-waterfall-parallelism nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; GitHub Issue #690 (https://github.com/acl2/acl2/issues/690):

(must-succeed*

 (defunvar ?p (*) => *)

 (defun-sk2 exists[?p] (?p) ()
   (exists x (?p x)))

 (verify-guards exists[?p])

 (defun-inst exists[symbolp]
   (exists[?p] (?p . symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DEFUNVAR:

(must-fail ; bad name
 (defunvar "?f" () => *)
 :with-output-off nil)

(must-fail ; bad name
 (defunvar '?f () => *)
 :with-output-off nil)

(must-fail ; bad arguments
 (defunvar ?f 33 => *)
 :with-output-off nil)

(must-fail ; bad arguments
 (defunvar ?f (3 *) => *)
 :with-output-off nil)

(must-fail ; bad arguments
 (defunvar ?f (* state *) => *)
 :with-output-off nil)

(must-fail ; bad arguments
 (defunvar ?f (x y) => *)
 :with-output-off nil)

(must-fail ; bad arrow
 (defunvar ?f (* *) #\> *)
 :with-output-off nil)

(must-fail ; bad result
 (defunvar ?f (* *) => (1 2 3))
 :with-output-off nil)

(must-fail ; bad options
 (defunvar ?f (*) => * bad)
 :with-output-off nil)

(must-fail ; bad options
 (defunvar ?f (*) => * :other nil)
 :with-output-off nil)

(must-fail ; bad options
 (defunvar ?f (*) => * :print 4)
 :with-output-off nil)

(must-fail ; bad options
 (defunvar ?f (*) => * :print nil :other 2)
 :with-output-off nil)

(must-fail ; bad options
 (defunvar ?f (*) => * :print nil :print nil)
 :with-output-off nil)

(defunvar ?nullary () => *)

;; Example 1 in :DOC DEFUNVAR:
(defunvar ?f (*) => *)

;; Example 2 in :DOC DEFUNVAR:
(defunvar ?p (*) => *)

;; Example 3 in :DOC DEFUNVAR:
(defunvar ?g (* *) => *)

(defunvar ?many (* * * * * * * * *) => *)

(must-succeed ; print everything
 (defunvar ?a (*) => * :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defunvar ?a (*) => * :print nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DEFUN2:

(must-fail ; bad name
 (defun2 "h" (?f ?g) (x y) (cons (?f x) (?g x y)))
 :with-output-off nil)

(must-fail ; bad function parameters
 (defun2 h (1 2 3) (x y) (cons (?f x) (?g x y)))
 :with-output-off nil)

(must-fail ; extra function parameters
 (defun2 h (?f ?g ?many) (x y) (cons (?f x) (?g x y)))
 :with-output-off nil)

(must-fail ; missing function parameters
 (defun2 h (?f) (x y) (cons (?f x) (?g x y)))
 :with-output-off nil)

(must-succeed*
 ;; a well-founded relation
 (defun o-p$ (x) (o-p x))
 (defun o<$ (x y) (o< x y))
 (defun id (x) x)
 (defthm o<$-is-well-founded-relation
   (and (implies (o-p$ x) (o-p (id x)))
        (implies (and (o-p$ x)
                      (o-p$ y)
                      (o<$ x y))
                 (o< (id x) (id y))))
   :rule-classes :well-founded-relation)
 ;; well-founded relation is not O<
 (must-fail
  (defun2 h (?f) (x)
    (declare (xargs :well-founded-relation o<$))
    (if (zp x)
        (?f x)
      (h (1- x))))
  :with-output-off nil)
 :with-output-off nil)

(must-fail ; bad :PRINT option
 (defun2 h (?f) (x) (?f x) :print 456)
 :with-output-off nil)

(defun2 nonrec (?f ?g) (x y)
  (cons (?f x) (?g x y)))

(defun2 rec (?f) (x)
  (if (consp x) (rec (car x)) (?f x)))

(defun2 fvguard (?f ?g) (x y)
  (declare (xargs :guard (?g x y)))
  (list (?f (cons x y))))

(defun2 fvmeas (?f) (x)
  (declare (xargs :measure (acl2-count (?f x))))
  (if (and (consp x)
           (< (acl2-count (?f (cdr x)))
              (acl2-count (?f x))))
      (fvmeas (cdr x))
    0))

(defun2 call-nonrec (?f ?g) (z)
  (if (consp z) (nonrec (car z) (cdr z)) nil))

;; Example 1 in :DOC DEFUN2:
(defun2 quad[?f] (?f) (x)
  (?f (?f (?f (?f x)))))

;; Example 2 in :DOC DEFUN2:
(defun2 all[?p] (?p) (l)
  (declare (xargs :guard t))
  (cond ((atom l) (null l))
        (t (and (?p (car l)) (all[?p] (cdr l))))))

;; Example 3 in :DOC DEFUN2:
(defun2 map[?f][?p] (?f ?p) (l)
  (declare (xargs :guard (all[?p] l)))
  (cond ((endp l) nil)
        (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))

;; Example 4 in :DOC DEFUN2:
(defun2 fold[?f][?g] (?f ?g) (bt)
  (cond ((atom bt) (?f bt))
        (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))

(must-succeed ; print everything
 (defun2 h (?f) (x) (?f x) :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defun2 h (?f) (x) (?f x) :print nil)
 :with-output-off nil)

(must-succeed ; print the function output only
 (defun2 h (?f) (x) (?f x) :print :fn-output)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DEFCHOOSE2:

(must-fail ; bad name
 (defchoose2 #\h (b) (?f ?g) (x y)
   (< (fix b) (fix (?f (?g x y)))))
 :with-output-off nil)

(must-fail ; bad function parameters
 (defchoose2 h (b) 789 (x y)
   (< (fix b) (fix (?f (?g x y)))))
 :with-output-off nil)

(must-fail ; extra function parameters
 (defchoose2 h (b) (?nullary ?g ?f) (x y)
   (< (fix b) (fix (?f (?g x y)))))
 :with-output-off nil)

(must-fail ; missing function paramters
 (defchoose2 h (b) (?g) (x y)
   (< (fix b) (fix (?f (?g x y)))))
 :with-output-off nil)

(must-fail ; bad :PRINT option
 (defchoose2 h (b) (?f) (x)
   (equal b (?f x))
   :print "all")
 :with-output-off nil)

(defchoose2 choose (b) (?g ?f) (x y)
  (< (fix b) (fix (?f (?g x y)))))

(defchoose2 choose1 (b) (?g ?f) (x y)
  (< (fix b) (fix (?f (?g x y))))
  :strengthen t)

(defchoose2 choose2 (b) (?g ?f) (x y)
  (< (fix b) (fix (?f (?g x y))))
  :strengthen nil)

;; Example 1 in :DOC DEFCHOOSE2:
(defchoose2 fixpoint[?f] x (?f) ()
  (equal (?f x) x))

(must-succeed ; print everything
 (defchoose2 h (b) (?f) (x)
   (equal b (?f x))
   :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defchoose2 h (b) (?f) (x)
   (equal b (?f x))
   :print nil)
 :with-output-off nil)

(must-succeed ; print the function output only
 (defchoose2 h (b) (?f) (x)
   (equal b (?f x))
   :print :fn-output)
 :with-output-off nil)

(must-succeed ; :PRINT after another option
 (defchoose2 h (b) (?f) (x)
   (equal b (?f x))
   :strengthen t
   :print :all)
 :with-output-off nil)

(must-succeed ; :PRINT before another option
 (defchoose2 h (b) (?f) (x)
   (equal b (?f x))
   :print :all
   :strengthen t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DEFUN-SK2:

(must-fail ; bad name
 (defun-sk2 (h 1) (?f ?g) (x y)
   (forall (z w) (equal (?f (?g x y)) (cons z w))))
 :with-output-off nil)

(must-fail ; bad function parameters
 (defun-sk2 h ("?f" ?g) (x y)
   (forall (z w) (equal (?f (?g x y)) (cons z w))))
 :with-output-off nil)

(must-fail ; extra function parameters
 (defun-sk2 h (?f ?many ?g) (x y)
   (forall (z w) (equal (?f (?g x y)) (cons z w))))
 :with-output-off nil)

(must-fail ; missing function parameters (used in body)
 (defun-sk2 h (?g) (x y)
   (forall (z w) (equal (?f (?g x y)) (cons z w))))
 :with-output-off nil)

(must-fail ; missing function parameters (used in custom rewrite rule)
 (defun-sk2 h (?g) (x y)
   (forall (z w) (equal (?g x y) (cons z w)))
   :rewrite (implies (and (?f x) (h x y))
                     (equal (?g x y) (cons z w))))
 :with-output-off nil)

(must-fail ; bad :PRINT option
 (defun-sk2 h (?f) (x)
   (forall y (equal y (?f x)))
   :print (1 2 2))
 :with-output-off nil)

(defun-sk2 ex (?f ?g) (x y)
  (exists (z w) (equal (?f (?g x y)) (cons z w))))

(defun-sk2 fa (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w))))

(defun-sk2 fa-rw1 (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :rewrite :default)

(defun-sk2 fa-rw2 (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :rewrite :direct)

(defun-sk2 fa-rw3 (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :rewrite (implies (and (atom x) (fa-rw3 x y))
                    (equal (?f (?g x y)) (cons z w))))

(defun-sk2 qok (?f ?g) (x y)
  (forall (exists w) (equal (?f (?g x y)) (cons exists w)))
  :quant-ok t)

(defun-sk2 not-qok (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :quant-ok nil)

(progn
  (defun-sk2 sk-name (?f ?g) (x y)
    (exists (z w) (equal (?f (?g x y)) (cons z w)))
    :skolem-name wit)
  (assert! (function-namep 'wit (w state))))

(progn
  (defun-sk2 thm-name (?f ?g) (x y)
    (exists (z w) (equal (?f (?g x y)) (cons z w)))
    :thm-name th)
  (assert! (theorem-namep 'th (w state))))

(defun-sk2 wit-dcl (?f ?g) (x y)
  (exists (z w) (equal (?f (?g x y)) (cons z w)))
  :witness-dcls ((declare (xargs :guard (natp (?f x))))))

(defun-sk2 strong (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :strengthen t)

(defun-sk2 not-strong (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :strengthen nil)

(defun-sk2 constrained (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :constrain t)

(defun-sk2 not-constrained (?f ?g) (x y)
  (forall (z w) (equal (?f (?g x y)) (cons z w)))
  :constrain nil)

;; Example 1 in :DOC DEFUN-SK2:
(defun-sk2 injective[?f] (?f) ()
  (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))

(must-succeed ; print everything
 (defun-sk2 h (?f) (x)
   (forall y (equal y (?f x)))
   :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defun-sk2 h (?f) (x)
   (forall y (equal y (?f x)))
   :print nil)
 :with-output-off nil)

(must-succeed ; print the function output only
 (defun-sk2 h (?f) (x)
   (forall y (equal y (?f x)))
   :print :fn-output)
 :with-output-off nil)

(must-succeed ; :PRINT after another option
 (defun-sk2 h (?f) (x)
   (forall y (equal y (?f x)))
   :skolem-name h-wit
   :print :all)
 :with-output-off nil)

(must-succeed ; :PRINT before another option
 (defun-sk2 h (?f) (x)
   (forall y (equal y (?f x)))
   :print :all
   :skolem-name h-wit)
 :with-output-off nil)

(must-succeed ; :PRINT between two options
 (defun-sk2 h (?f) (x)
   (forall y (equal y (?f x)))
   :thm-name h-thm
   :print :all
   :skolem-name h-wit)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DEFUN-INST:

(must-fail ; bad name
 (defun-inst "i" (?f) (nonrec (?g . cons)))
 :with-output-off nil)

(must-fail ; bad function parameters or 2nd-order function with instantiation
 (defun-inst i (1 2) (nonrec (?g . cons)))
 :with-output-off nil)

(must-fail ; bad reference to 2nd-order function to instantiate
 (defun-inst i (?f) (nonrec$ (?g . cons)))
 :with-output-off nil)

(must-fail ; bad instantiation
 (defun-inst i (?f) (nonrec "abc"))
 :with-output-off nil)

(must-fail ; no instantiation
 (defun-inst i (?f) (nonrec))
 :with-output-off nil)

(must-fail ; bad function variable in instantiation
 (defun-inst i (?f) (nonrec (?gg . cons)))
 :with-output-off nil)

(must-fail ; trivial pair in instantiation
 (defun-inst i (?f) (nonrec (?g . ?g)))
 :with-output-off nil)

(must-fail ; extra function variable in instantiation
 (defun-inst i (?f) (nonrec (?g . cons) (?p . atom)))
 :with-output-off nil)

(must-fail ; extra function parameters
 (defun-inst i (?f) (nonrec (?g . cons) (?f . atom)))
 :with-output-off nil)

(must-fail ; missing function parameters (not instantiated)
 (defun-inst i (nonrec (?g . cons)))
 :with-output-off nil)

(must-fail ; missing function parameters (introduced by instantiation)
 (defun-inst i (?g) (nonrec (?f . ?p)))
 :with-output-off nil)

(must-fail ; missing 2nd-order function with instantiation
 (defun-inst i (?g))
 :with-output-off nil)

(must-fail ; bad option
 (defun-inst i (?f) (nonrec (?g . cons))
   :bad 3)
 :with-output-off nil)

(must-fail ; bad :PRINT option
 (defun-inst i (?f) (nonrec (?g . cons))
   :print "ALL")
 :with-output-off nil)

(must-fail ; bad option for plain 2nd-order function
 (defun-inst i (?f) (nonrec (?g . cons))
   :skolem-name wit)
 :with-output-off nil)

(must-fail ; bad option for plain 2nd-order function
 (defun-inst i (?f) (nonrec (?g . cons))
   :thm-name th)
 :with-output-off nil)

(must-fail ; bad option for plain 2nd-order function
 (defun-inst i (?f) (nonrec (?g . cons))
   :rewrite :direct)
 :with-output-off nil)

(must-fail ; duplicate options
 (defun-inst i (?f) (nonrec (?g . cons))
   :verify-guards nil :print :all :verify-guards nil)
 :with-output-off nil)

(defun-inst nonrec-i (?f) (nonrec (?g . cons)))

(defun-inst nonrec-j (?g) (nonrec (?f . atom)))

(progn
  (defun-inst nonrec-k (nonrec (?f . atom) (?g . cons)))
  (assert-equal (nonrec-k 3 'a) (cons t (cons 3 'a))))

(defun-inst nonrec-l (?p) (nonrec (?f . ?p) (?g . cons)))

(progn
  (defun-inst rec-i (rec (?f . fix)))
  (assert-equal (rec-i (cons (cons (cons 40 'a) #\a) "a")) 40))

(progn
  (assert! (guard-verified-p 'fvguard (w state)))
  (progn
    (defun-inst fvguard-i (?f) (fvguard (?g . cons)))
    (assert! (guard-verified-p 'fvguard-i (w state))))
  (progn
    (defun-inst fvguard-i-t (?f) (fvguard (?g . cons))
      :verify-guards t)
    (assert! (guard-verified-p 'fvguard-i-t (w state))))
  (progn
    (defun-inst fvguard-i-n (?f) (fvguard (?g . cons))
      :verify-guards nil)
    (assert! (not (guard-verified-p 'fvguard-i-n (w state))))))

(progn
  (assert! (not (guard-verified-p 'fvmeas (w state))))
  (progn
    (defun-inst fvmeas-i (fvmeas (?f . len)))
    (assert! (not (guard-verified-p 'fvmeas-i (w state)))))
  (progn
    (defun-inst fvmeas-i-t (fvmeas (?f . len))
      :verify-guards t)
    (assert! (guard-verified-p 'fvmeas-i-t (w state))))
  (progn
    (defun-inst fvmeas-i-n (fvmeas (?f . len))
      :verify-guards nil)
    (assert! (not (guard-verified-p 'fvmeas-i-n (w state))))))

(must-fail ; missing ((?F . LEN)) instance of nonrec
 (defun-inst call-nonrec-i (?g) (call-nonrec (?f . len)))
 :with-output-off nil)

(progn
  (defun-inst nonrec-len (?g) (nonrec (?f . len)))
  (defun-inst call-nonrec-i (?g) (call-nonrec (?f . len))))

;; Example 1 in :DOC DEFUN-INST:
(progn
  (defun wrap (x) (list x))
  (defun-inst quad[wrap]
    (quad[?f] (?f . wrap))))

;; Example 2 in :DOC DEFUN-INST:
(progn
  (defun octetp (x) (declare (xargs :guard t)) (and (natp x) (< x 256)))
  (defun-inst all[octetp]
    (all[?p] (?p . octetp))))

;; Example 3 in :DOC DEFUN-INST:
(defun-inst map[code-char][octetp]
  (map[?f][?p] (?f . code-char) (?p . octetp)))

;; Example 4 in :DOC DEFUN-INST:
(defun-inst fold[nfix][binary-+]
  (fold[?f][?g] (?f . nfix) (?g . binary-+)))

(must-succeed ; print everything
 (defun-inst i (?f) (nonrec (?g . cons))
   :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defun-inst i (?f) (nonrec (?g . cons))
   :print nil)
 :with-output-off nil)

(must-succeed ; print result
 (defun-inst i (?f) (nonrec (?g . cons))
   :print :result)
 :with-output-off nil)

(must-succeed ; print result
 (defun-inst i (?f) (nonrec (?g . cons))
   :print :result)
 :with-output-off nil)

(must-succeed ; :PRINT after another option
 (defun-inst i (?f) (nonrec (?g . cons))
   :verify-guards nil
   :print nil)
 :with-output-off nil)

(must-succeed ; :PRINT before another option
 (defun-inst i (?f) (nonrec (?g . cons))
    :print nil
    :verify-guards nil)
 :with-output-off nil)

(must-fail ; bad option for choice 2nd-order function
 (defun-inst i (?f) (choose (?g . cons))
   :verify-guards nil)
 :with-output-off nil)

(must-fail ; bad option for choice 2nd-order function
 (defun-inst i (?f) (choose (?g . cons))
   :skolem-name wit)
 :with-output-off nil)

(must-fail ; bad option for choice 2nd-order function
 (defun-inst i (?f) (choose (?g . cons))
   :thm-name wit)
 :with-output-off nil)

(must-fail ; bad option for choice 2nd-order function
 (defun-inst i (?f) (choose (?g . cons))
   :rewrite :direct)
 :with-output-off nil)

(must-fail ; duplicate options
 (defun-inst i (?f) (choose (?g . cons))
   :print :all :print :all)
 :with-output-off nil)

(defun-inst choose-i (?f) (choose (?g . cons)))

(defun-inst choose-j (?g) (choose (?f . atom)))

(defun-inst choose-k (choose (?f . atom) (?g . cons)))

(defun-inst choose-l (?p ?g) (choose (?f . ?p)))

(defun-inst choose1-i (choose1 (?f . atom) (?g . cons)))

(defun-inst choose2-i (choose2 (?f . atom) (?g . cons)))

;; Example 5 in :DOC DEFUN-INST:
(progn
  (defun twice (x) (* 2 (fix x)))
  (defun-inst fixpoint[twice]
    (fixpoint[?f] (?f . twice))))

(must-succeed ; print everything
 (defun-inst i (?f) (choose (?g . cons))
   :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defun-inst i (?f) (choose (?g . cons))
   :print nil)
 :with-output-off nil)

(must-succeed ; print result
 (defun-inst i (?f) (choose (?g . cons))
   :print :result)
 :with-output-off nil)

(must-fail ; bad option for quantifier 2nd-order function
 (defun-inst i (?f) (ex (?g . cons))
   :verify-guards nil)
 :with-output-off nil)

(must-fail ; duplicate options
 (defun-inst i (?f) (ex (?g . cons))
   :thm-name ex-thm :thm-name thm-ex)
 :with-output-off nil)

(defun-inst ex-i (?f) (ex (?g . cons)))

(defun-inst ex-j (?g) (ex (?f . atom)))

(defun-inst ex-k (ex (?f . atom) (?g . cons)))

(defun-inst ex-l (?p) (ex (?f . ?p) (?g . cons)))

(defun-inst fa-i (?f) (fa (?g . cons)))

(defun-inst fa-j (?g) (fa (?f . atom)))

(defun-inst fa-k (fa (?f . atom) (?g . cons)))

(defun-inst fa-l (?p) (fa (?f . ?p) (?g . cons)))

(defun-inst fa-rw1-i (fa-rw1 (?f . atom) (?g . cons)))

(defun-inst fa-rw1-j (fa-rw1 (?f . atom) (?g . cons))
  :rewrite :default)

(defun-inst fa-rw1-k (fa-rw1 (?f . atom) (?g . cons))
  :rewrite :direct)

(defun-inst fa-rw1-l (fa-rw1 (?f . atom) (?g . cons))
  :rewrite (implies (and (consp z) (fa-rw1-l x y))
                    (equal (atom (cons x y)) (cons z w))))

(defun-inst fa-rw2-i (?g) (fa-rw2 (?f . atom)))

(defun-inst fa-rw2-j (?g) (fa-rw2 (?f . atom))
  :rewrite :default)

(defun-inst fa-rw2-k (?g) (fa-rw2 (?f . atom))
  :rewrite :direct)

(defun-inst fa-rw2-l (?g) (fa-rw2 (?f . atom))
  :rewrite (implies (and (consp z) (fa-rw2-l x y))
                    (equal (atom (cons x y)) (cons z w))))

(defun-inst fa-rw3-i (?p ?g) (fa-rw2 (?f . ?p)))

(defun-inst fa-rw3-j (?p ?g) (fa-rw2 (?f . ?p))
  :rewrite :default)

(defun-inst fa-rw3-k (?p ?g) (fa-rw2 (?f . ?p))
  :rewrite :direct)

(defun-inst fa-rw3-l (?p ?g) (fa-rw2 (?f . ?p))
  :rewrite (implies (and (consp z) (fa-rw3-l x y))
                    (equal (?p (?g x y)) (cons z w))))

(defun-inst qok-i (?g) (qok (?f . len)))

(defun-inst not-qok-i (not-qok (?f . atom) (?g . cons)))

(defun-inst sk-name-i (?f) (sk-name (?g . cons)))

(progn
  (defun-inst sk-name-j (?f) (sk-name (?g . cons))
    :skolem-name wit-j)
  (assert! (function-namep 'wit-j (w state))))

(defun-inst thm-name-i (?f) (sk-name (?g . cons)))

(progn
  (defun-inst thm-name-j (?f) (thm-name (?g . cons))
    :thm-name th-j)
  (assert! (theorem-namep 'th-j (w state))))

(defun-inst wit-dcl-i (wit-dcl (?f . atom) (?g . cons)))

(defun-inst strong-i (?p ?g) (strong (?f . ?p)))

(defun-inst not-strong-i (not-strong (?f . atom) (?g . cons)))

(defun-inst constrained-i (constrained (?f . atom) (?g . cons)))

(defun-inst constrained-j (constrained (?f . atom) (?g . cons))
  :constrain t)

(defun-inst constrained-k (constrained (?f . atom) (?g . cons))
  :constrain nil)

(defun-inst not-constrained-i (constrained (?f . atom) (?g . cons)))

(defun-inst not-constrained-j (constrained (?f . atom) (?g . cons))
  :constrain t)

(defun-inst not-constrained-k (constrained (?f . atom) (?g . cons))
  :constrain nil)

;; Example 6 in :DOC DEFUN-INST:
(defun-inst injective[quad[?f]] (?f)
  (injective[?f] (?f . quad[?f])))

(must-succeed ; print everything
 (defun-inst i (?f) (ex (?g . cons))
   :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defun-inst i (?f) (ex (?g . cons))
   :print nil)
 :with-output-off nil)

(must-succeed ; print result
 (defun-inst i (?f) (ex (?g . cons))
   :print :result)
 :with-output-off nil)

(must-succeed ; :PRINT after another option
 (defun-inst i (?f) (ex (?g . cons))
   :thm-name ithm
   :print :all)
 :with-output-off nil)

(must-succeed ; :PRINT before another option
 (defun-inst i (?f) (ex (?g . cons))
   :print :all
   :thm-name ithm)
 :with-output-off nil)

(must-succeed ; :PRINT between two options
 (defun-inst i (?f) (ex (?g . cons))
   :skolem-name iwit
   :print :all
   :thm-name ithm)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 2nd-order theorems:

(defthm consp-of-nonrec
  (consp (nonrec x y)))

(defthm natp-of-rec-when-atom-and-natp-of-?f
  (implies (and (atom x)
                (natp (?f x)))
           (natp (rec x))))

(defthm len-of-fvguard
  (equal (len (fvguard x y)) 1))

(defthm fvmeas-is-0
  (equal (fvmeas x) 0))

(defthm booleanp-of-all[?p]
  (booleanp (all[?p] l)))

; Example 1 in :DOC DEFTHM-2ND-ORDER:
(defthm len-of-map[?f][?p]
  (equal (len (map[?f][?p] l)) (len l)))

; Example 2 in :DOC DEFTHM-2ND-ORDER:
(defthm injective[quad[?f]]-when-injective[?f]
  (implies (injective[?f]) (injective[quad[?f]]))
  :hints
  (("Goal" :use
    ((:instance
      injective[?f]-necc
      (x (?f (?f (?f (?f (mv-nth 0 (injective[quad[?f]]-witness)))))))
      (y (?f (?f (?f (?f (mv-nth 1 (injective[quad[?f]]-witness))))))))
     (:instance
      injective[?f]-necc
      (x (?f (?f (?f (mv-nth 0 (injective[quad[?f]]-witness))))))
      (y (?f (?f (?f (mv-nth 1 (injective[quad[?f]]-witness)))))))
     (:instance
      injective[?f]-necc
      (x (?f (?f (mv-nth 0 (injective[quad[?f]]-witness)))))
      (y (?f (?f (mv-nth 1 (injective[quad[?f]]-witness))))))
     (:instance
      injective[?f]-necc
      (x (?f (mv-nth 0 (injective[quad[?f]]-witness))))
      (y (?f (mv-nth 1 (injective[quad[?f]]-witness)))))
     (:instance
      injective[?f]-necc
      (x (mv-nth 0 (injective[quad[?f]]-witness)))
      (y (mv-nth 1 (injective[quad[?f]]-witness))))))))

;; Example 3 in :DOC DEFTHM-2ND-ORDER:
(progn
  (defunvar ?io (* *) => *)
  (defun-sk2 atom-io[?f][?io] (?f ?io) ()
    (forall x (implies (atom x) (?io x (?f x))))
    :rewrite :direct)
  (defun-sk2 consp-io[?g][?io] (?g ?io) ()
    (forall (x y1 y2)
            (implies (and (consp x) (?io (car x) y1) (?io (cdr x) y2))
                     (?io x (?g y1 y2))))
    :rewrite :direct)
  (defthm fold-io[?f][?g][?io]
    (implies (and (atom-io[?f][?io]) (consp-io[?g][?io]))
             (?io x (fold[?f][?g] x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DEFTHM-INST:

(must-fail ; bad name
 (defthm-inst #\n (consp-of-nonrec (?g . cons)))
 :with-output-off nil)

(must-fail ; bad reference to 2nd-order theorem to instantiate
 (defthm-inst i (consp-of-nonrec-wrong (?g . cons)))
 :with-output-off nil)

(must-fail ; bad instantiation
 (defthm-inst i (consp-of-nonrec "AAA"))
 :with-output-off nil)

(must-fail ; no instantiation
 (defthm-inst i (consp-of-nonrec))
 :with-output-off nil)

(must-fail ; bad function variable in instantiation
 (defthm-inst i (consp-of-nonrec (?gg . cons)))
 :with-output-off nil)

(must-fail ; trivial pair in instantiation
 (defthm-inst i (consp-of-nonrec (?g . ?g)))
 :with-output-off nil)

(must-fail ; bad options
 (defthm-inst i (consp-of-nonrec (?g . cons))
   '(4/5 #\q))
 :with-output-off nil)

(must-fail ; bad options
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :bad 3)
 :with-output-off nil)

(must-fail ; bad :PRINT option
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :print 3/2)
 :with-output-off nil)

(must-fail ; duplicate options
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :rule-classes :rewrite :rule-classes nil)
 :with-output-off nil)

(defthm-inst consp-of-nonrec-i (consp-of-nonrec (?g . cons)))

(defthm-inst consp-of-nonrec-j (consp-of-nonrec (?f . atom)))

(defthm-inst consp-of-nonrec-k (consp-of-nonrec (?f . atom) (?g . cons)))

(defthm-inst consp-of-nonrec-l (consp-of-nonrec (?f . ?p) (?g . cons)))

(defthm-inst natp-of-rec-when-atom-and-natp-of-?f-i
  (natp-of-rec-when-atom-and-natp-of-?f (?f . fix)))

(defthm-inst len-of-fvguard-i (len-of-fvguard (?g . cons)))

(defthm-inst fvmeas-is-0-i (fvmeas-is-0 (?f . len)))

(defthm-inst booleanp-of-all[octet] (booleanp-of-all[?p] (?p . octetp)))

(defthm-inst booleanp-of-all[octet]-type (booleanp-of-all[?p] (?p . octetp))
  :rule-classes :type-prescription)

(defthm-inst booleanp-of-all[octet]-none (booleanp-of-all[?p] (?p . octetp))
  :rule-classes nil)

; Example 1 in :DOC DEFTHM-INST:
(defthm-inst len-of-map[code-char][octetp]
  (len-of-map[?f][?p] (?f . code-char) (?p . octetp)))

(must-fail ; missing ((?F . WRAP)) instance of INJECTIVE[?F]
 (defthm-inst injective[quad[wrap]]-when-injective[wrap]
   (injective[quad[?f]]-when-injective[?f] (?f . wrap)))
 :with-output-off nil)

; Example 2 in :DOC DEFTHM-INST:
(progn
  (defun-inst injective[quad[wrap]]
    (injective[quad[?f]] (?f . wrap)))
  (defun-inst injective[wrap]
    (injective[?f] (?f . wrap)))
  (defthm-inst injective[quad[wrap]]-when-injective[wrap]
    (injective[quad[?f]]-when-injective[?f] (?f . wrap))))

(must-succeed ; print everything
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :print :all)
 :with-output-off nil)

(must-succeed ; print nothing
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :print nil)
 :with-output-off nil)

(must-succeed ; print result
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :print :result)
 :with-output-off nil)

(must-succeed ; :PRINT after another option
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :rule-classes nil
   :print :all)
 :with-output-off nil)

(must-succeed ; :PRINT before another option
 (defthm-inst i (consp-of-nonrec (?g . cons))
   :print :all
   :rule-classes nil)
 :with-output-off nil)
