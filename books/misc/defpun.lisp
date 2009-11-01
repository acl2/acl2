;  Copyright (C) 2000 Panagiotis Manolios and J Strother Moore
 
; Modified May 2004 by Matt Kaufmann, in order to allow stobjs.  Thanks to John
; Matthews for providing a motivating example.  NOTE:  Do not use a :stobjs
; declaration in your defpun!

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.
 
;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.
 
;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 
;  Written by Panagiotis Manolios and J Strother Moore who can be
;  reached as follows.
 
;  Email: pete@cs.utexas.edu, moore@cs.utexas.edu
 
;  Postal Mail:
;  Department of Computer Sciences
;  Taylor Hall 2.124 [C0500]
;  The University of Texas at Austin
;  Austin, TX 78712-1188 USA

; To introduce an arbitrary tail-recursive function we proceed in
; three steps.  First is the proof that we can admit the generic one
; argument tail recursive function.  This ``generic theorem'' is
; proved once; the proof is not redone for each new function.  Second,
; the generic theorem is used to introduce the arity one version of
; the desired function.  Third, we prove that the arity one version is
; a witness for the desired equation.

; Here is an example.  Suppose we wish to admit the tail recursive
; factorial.

; (defun trfact (n a)
;   (if (equal n 0)
;       a
;     (trfact (- n 1) (* n a))))

; We first recognize that this is probably tail recursive (without
; checking that trfact is new, that the vars are distinct, etc.).
; Successful recognition produces

; (mv '((n (car x))
;       (a (cadr x)))
;     '(equal n 0)
;     'a
;     '(list (- n 1) (* n a)))

; Using the output of this check, we introduce three defuns

; (defun defpun-test1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     (equal n 0)))

; (defun defpun-base1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     a))

; (defun step1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     (list (- n 1) (* n a))))

; We then use the generic theorem to introduce

; (defun trfact1 (x)
;   (if (defpun-test1 x)
;       (defpun-base1 x)
;     (trfact1 (step1 x))))

; We then define

; (defun trfact (n a)
;   (trfact1 (list n a)))

; and we prove that it satisfies the constraint

; (equal (trfact n a)
;        (if (equal n 0)
;            a
;          (trfact (- n 1) (* n a))))

; Now we write the code to do all this.

; First, we prove the generic theorem.  We use the proof Pete
; developed in his prototype implementation of defpartial but for the
; generic case.

(in-package "ACL2")

(defmacro defun-nonexec (name args &rest rst)
  `(defun-nx ,name ,args ,@rst))

(defstub defpun-test (x) t)
(defstub defpun-base (x) t)
(defstub defpun-st (x) t)

(defun defpun-stn (x n)
  (if (zp n) x (defpun-stn (defpun-st x) (1- n))))

(defchoose fch (n)
  (x)
  (defpun-test (defpun-stn x n)))

(defun defpun-fn (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (defpun-test x))
      (defpun-base x)
      (defpun-fn (defpun-st x) (1- n))))

(defun defpun-f (x)
  (if (defpun-test (defpun-stn x (fch x)))
      (defpun-fn x (fch x))
      nil))

; The following encapsulate exports one constrained function, namely,
; defpun-f, with the constraint

; (DEFTHM GENERIC-TAIL-RECURSIVE-DEFPUN-F
;   (EQUAL (DEFPUN-F X)
;          (IF (DEFPUN-TEST X) (DEFPUN-BASE X) (DEFPUN-F (DEFPUN-ST X))))
;   :RULE-CLASSES NIL)

; Nothing else is exported.

(encapsulate nil
 (local (defthm defpun-test-fch
          (implies (defpun-test x)
                   (defpun-test (defpun-stn x (fch x))))
          :hints
          (("goal" :use ((:instance fch (n 0)))))))
 (local (defthm defpun-test-defpun-f-def
          (implies (defpun-test x)
                   (equal (defpun-f x) (defpun-base x)))))
 (local (defthm open-defpun-stn
          (implies (and (integerp n) (< 0 n))
                   (equal (defpun-stn x n) (defpun-stn (defpun-st x) (1- n))))))

 (local (defthm +1-1 (equal (+ -1 +1 x) (fix x))))

 (local (defthm defpun-st-defpun-stn-fch
          (implies (defpun-test (defpun-stn (defpun-st x) (fch (defpun-st x))))
                   (defpun-test (defpun-stn x (fch x))))
          :hints
          (("goal" :use
            ((:instance fch (n (1+ (nfix (fch (defpun-st x))))))
             (:instance fch (n 1)))))
          :rule-classes :forward-chaining))
 (local (defthm defpun-test-nil-fch
          (implies (not (defpun-test x))
                   (iff (defpun-test (defpun-stn (defpun-st x) (fch (defpun-st x))))
                        (defpun-test (defpun-stn x (fch x)))))
          :hints
          (("subgoal 2" :expand (defpun-stn x (fch x))
            :use
            ((:instance fch (x (defpun-st x))
                        (n (+ -1 (fch x)))))))))
 (local (defthm defpun-fn-defpun-st
          (implies (and (defpun-test (defpun-stn x n)) (defpun-test (defpun-stn x m)))
                   (equal (defpun-fn x n) (defpun-fn x m)))
          :rule-classes nil))
 (defthm generic-tail-recursive-defpun-f
   (equal (defpun-f x)
          (if (defpun-test x) (defpun-base x) (defpun-f (defpun-st x))))
   :hints
   (("subgoal 1" :expand (defpun-fn x (fch x)))
    ("subgoal 1.2'" :use
     ((:instance defpun-fn-defpun-st (x (defpun-st x))
                 (n (+ -1 (fch x)))
                 (m (fch (defpun-st x)))))))
   :rule-classes nil))

(defun arity-1-tail-recursive-encap (defpun-f defpun-test defpun-base defpun-st)

; Execution of this function produces an encapsulation that introduces
; a constrained tail recursive defpun-f with the constraint
; (equal (defpun-f x) (if (defpun-test x) (defpun-base x) (defpun-f (defpun-st x)))),
; where defpun-test, defpun-base and defpun-st are previously defined functions of arity 1.

  (declare (xargs :mode :program))

  (let ((defpun-stn (packn-pos (list defpun-f "-defpun-stn") defpun-f))
        (fch (packn-pos (list defpun-f "-fch") defpun-f))
        (defpun-fn  (packn-pos (list defpun-f "-defpun-fn") defpun-f)))

    `(encapsulate
      ((,defpun-f (x) t))
    
      (local (in-theory (disable ,defpun-test ,defpun-base ,defpun-st)))

      (local (defun-nonexec ,defpun-stn (x n)
               (if (zp n)
                   x
                 (,defpun-stn (,defpun-st x) (1- n)))))

      (local (defchoose ,fch (n) (x)
               (,defpun-test (,defpun-stn x n))))

      (local (defun-nonexec ,defpun-fn (x n)
               (declare (xargs :measure (nfix n)))
               (if (or (zp n)
                       (,defpun-test x))
                   (,defpun-base x) 
                 (,defpun-fn (,defpun-st x) (1- n)))))

      (local (defun-nonexec ,defpun-f (x)
               (if (,defpun-test (,defpun-stn x (,fch x)))
                   (,defpun-fn x (,fch x))
                 nil)))

      (local (in-theory '(,defpun-f ,defpun-test ,defpun-base ,defpun-st ,defpun-stn ,defpun-fn

; This last entry is needed when defpun-fn is a constant function returning T, NIL,
; or 0 (one of the singleton type sets)

                             (:type-prescription ,defpun-fn))))
      (defthm ,(packn-pos (list defpun-f "-DEF") defpun-f)
        (equal (,defpun-f x)
               (if (,defpun-test x) 
                   (,defpun-base x) 
                 (,defpun-f (,defpun-st x))))
        :hints (("Goal"
                 :use
                 (:functional-instance GENERIC-TAIL-RECURSIVE-DEFPUN-F
                                       (defpun-f ,defpun-f)
                                       (defpun-test ,defpun-test)
                                       (defpun-base ,defpun-base)
                                       (defpun-st ,defpun-st)
                                       (defpun-stn ,defpun-stn)
                                       (fch ,fch)
                                       (defpun-fn ,defpun-fn)
                                       ))
                ("Subgoal 2" :use ,fch))
                                 
        :rule-classes nil)
      )
    ))

; Second, we recognize probably tail-recursive definitions and introduce
; the appropriate functions of arity 1.

; Note that probably-tail-recursivep and destructure-tail-recursion should be
; kept in sync.

(defun probably-tail-recursivep (defpun-f vars body)
  (and (symbolp defpun-f)
       (symbol-listp vars)
       (true-listp body)
       (eq (car body) 'IF)
       (or (and (consp (caddr body))
                (eq (car (caddr body)) defpun-f))
           (and (consp (cadddr body))
                (eq (car (cadddr body)) defpun-f)))))

(defun destructure-tail-recursion-aux (vars x)
  (declare (xargs :mode :program))
  (cond ((endp vars) nil)
        (t (cons (list (car vars)
                       (list 'car x))
                 (destructure-tail-recursion-aux (cdr vars)
                                               (list 'cdr x))))))

(defun destructure-tail-recursion (defpun-f vars body)
  (declare (xargs :mode :program))
  (cond
   ((and (consp (caddr body))
         (eq (car (caddr body)) defpun-f))
    (mv (destructure-tail-recursion-aux vars 'x)
        (list 'NOT (cadr body))
        (cadddr body)
        (cons 'LIST (cdr (caddr body)))))
   (t
    (mv (destructure-tail-recursion-aux vars 'x)
        (cadr body)
        (caddr body)
        (cons 'LIST (cdr (cadddr body)))))))

(defun arbitrary-tail-recursive-encap (defpun-f vars body keypairs)
  (declare (xargs :mode :program))
  (mv-let
   (bindings defpun-test-body defpun-base-body step-body)
   (destructure-tail-recursion defpun-f vars body)
   (let ((f1 (packn-pos (list defpun-f "-arity-1") defpun-f))
         (defpun-test1 (packn-pos (list defpun-f "-arity-1-defpun-test") defpun-f))
         (defpun-base1 (packn-pos (list defpun-f "-arity-1-defpun-base") defpun-f))
         (step1 (packn-pos (list defpun-f "-arity-1-step") defpun-f)))
     `(encapsulate
       ((,defpun-f ,vars t))
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (local (defun-nonexec ,defpun-test1 (x) (let ,bindings ,defpun-test-body)))
       (local (defun-nonexec ,defpun-base1 (x) (let ,bindings ,defpun-base-body)))
       (local (defun-nonexec ,step1 (x) (let ,bindings ,step-body)))
       (local ,(arity-1-tail-recursive-encap f1 defpun-test1 defpun-base1 step1))
       (local (defun-nonexec ,defpun-f ,vars (,f1 (list ,@vars))))
       (defthm ,(packn-pos (list defpun-f "-DEF") defpun-f)
         (equal (,defpun-f ,@vars) ,body)
         :hints (("Goal" :use (:instance ,(packn-pos (list f1 "-DEF") defpun-f)
                                         (x (list ,@vars)))))
         ,@keypairs)))))

(defun remove-xargs-domain-and-measure (dcl)
  (case-match dcl
              (('declare ('xargs ':domain dom-expr
                                 ':measure measure-expr
                                 . rest))
               (mv nil dom-expr measure-expr rest))
              (('declare ('xargs ':gdomain dom-expr
                                 ':measure measure-expr
                                 . rest))
               (mv t dom-expr measure-expr rest))
              (& (mv nil nil 0 nil))))

(mutual-recursion
 (defun subst-defpun-fn-into-pseudo-term (new-defpun-fn old-defpun-fn pterm)
   (declare (xargs :mode :program))
   (cond
    ((atom pterm) pterm)
    ((eq (car pterm) 'quote) pterm)
    ((or (eq (car pterm) 'let)
         (eq (car pterm) 'let*))
     (list (car pterm)
           (subst-defpun-fn-into-pseudo-bindings new-defpun-fn old-defpun-fn (cadr pterm))
           (subst-defpun-fn-into-pseudo-term new-defpun-fn old-defpun-fn (caddr pterm))))
    ((eq (car pterm) 'cond)
     (cons 'cond
           (subst-defpun-fn-into-pseudo-cond-clauses new-defpun-fn old-defpun-fn (cdr pterm))))
    (t
     (cons (if (eq (car pterm) old-defpun-fn)
               new-defpun-fn
             (car pterm))
           (subst-defpun-fn-into-pseudo-term-list new-defpun-fn old-defpun-fn (cdr pterm))))))
 
 (defun subst-defpun-fn-into-pseudo-bindings (new-defpun-fn old-defpun-fn pbindings)
   (declare (xargs :mode :program))
   (cond
    ((atom pbindings) pbindings)
    (t (cons (list (car (car pbindings))
                   (subst-defpun-fn-into-pseudo-term new-defpun-fn old-defpun-fn
                                              (cadr (car pbindings))))
             (subst-defpun-fn-into-pseudo-bindings new-defpun-fn old-defpun-fn (cdr pbindings))))))

 (defun subst-defpun-fn-into-pseudo-cond-clauses (new-defpun-fn old-defpun-fn pclauses)
   (declare (xargs :mode :program))
   (cond
    ((atom pclauses) pclauses)
    (t (cons (list (subst-defpun-fn-into-pseudo-term new-defpun-fn old-defpun-fn
                                              (car (car pclauses)))
                   (subst-defpun-fn-into-pseudo-term new-defpun-fn old-defpun-fn
                                              (cadr (car pclauses))))
             (subst-defpun-fn-into-pseudo-cond-clauses new-defpun-fn old-defpun-fn
                                                (cdr pclauses))))))

 (defun subst-defpun-fn-into-pseudo-term-list (new-defpun-fn old-defpun-fn list)
   (declare (xargs :mode :program))
   (cond
    ((atom list) list)
    (t (cons (subst-defpun-fn-into-pseudo-term new-defpun-fn old-defpun-fn (car list))
             (subst-defpun-fn-into-pseudo-term-list new-defpun-fn old-defpun-fn (cdr list)))))))

(defun default-defpun-rule-classes (keyword-alist)

; We add :rule-classes :definition to keyword-alist if :rule-classes is
; not mentioned in it.

  (cond
   ((keyword-value-listp keyword-alist)
    (cond ((assoc-keyword :rule-classes keyword-alist)
           keyword-alist)
          (t (list* :rule-classes :definition keyword-alist))))
   (t keyword-alist)))

(defun destructure-dcl-body-keypairs (lst)

; Lst is the tail of some defpun.  It optionally contains a DECLARE
; form, a body, and some keyword binding pairs, in that order.  We
; return the three components.  Body must be present, and if keyword
; binding pairs are present, the length of that part of the list must
; be even.  So the parity of the length of the list determines which
; optional components are present.

; 0. illegal - never allowed to happen
; 1. body
; 2. dcl body
; 3. body :rule-classes classes
; 4. dcl body :rule-classes classes
; 5. body :rule-classes classes :hints hints
; 6. dcl body :rule-classes classes :hints hints
; etc.
; If rule-classes is unspecified it defaults to :definition.

  (cond
   ((evenp (length lst))
    (mv (car lst)
        (cadr lst)
        (default-defpun-rule-classes (cddr lst))))
   (t (mv nil
          (car lst)
          (default-defpun-rule-classes (cdr lst))))))

(defun defpun-syntax-er nil
  '(er soft 'defpun
       "The proper shape of a defpun event is~%~
        (defpun g (v1 ... vn) body).~%~
        A single optional declare form may be present ~
        before the body.  If present, the form must be one of three:~%~
        (DECLARE (XARGS :witness defpun-fn))~%~
        or~%~
        (DECLARE (XARGS :domain dom-expr :measure m . rest))~%~
        or~%~
        (DECLARE (XARGS :gdomain dom-expr :measure m . rest)).~%~
        An optional keyword alist may be ~
        present after the body.  The declare form is used during the ~
        admission of the witness function.  The keyword alist is ~
        attached to the equality axiom constraining the new function ~
        symbol.  If the :rule-classes keyword is not specified by the ~
        keyword alist, :definition is used."))

(defmacro defpun (g vars &rest rest)
  (cond
   ((and (symbolp g)
         (symbol-listp vars)
         (not (endp rest)))

; This form may be legal, so we will destructure it and proceed.  Otherwise,
; we will cause an error.

    (mv-let
     (dcl body keypairs)
     (destructure-dcl-body-keypairs rest)
     (cond
      ((not (keyword-value-listp keypairs))
       (defpun-syntax-er))
      ((and (not dcl)
            (probably-tail-recursivep g vars body))
       (arbitrary-tail-recursive-encap g vars body keypairs))
      ((and dcl
            (match dcl
                   ('declare ('xargs ':witness &))))
       `(encapsulate
         ((,g ,vars t))
         (local (defun-nonexec ,g ,vars (,(caddr (cadr dcl))
                                 ,@vars)))
         (defthm ,(packn-pos (list g "-DEF") g)
           (equal (,g ,@vars)
                  ,body)
           ,@keypairs)))
      ((not (and (consp dcl)
                 (eq (car dcl) 'declare)))
       (defpun-syntax-er))
      (t
       (mv-let
        (closed-domp dom-expr measure-expr rest-of-xargs)
        (remove-xargs-domain-and-measure dcl)
        (cond
         (closed-domp
          (let ((gwit (packn-pos (list "THE-" g) g)))
            `(encapsulate
              nil
              (defun ,gwit ,vars
                (declare (xargs :measure
                                (if ,dom-expr
                                    ,measure-expr
                                  0)
                                :guard ,dom-expr
                                :verify-guards nil
                                ,@rest-of-xargs))
                (if ,dom-expr
                    ,(subst-defpun-fn-into-pseudo-term gwit g body)
                  'undef))
              (encapsulate
               ((,g ,vars t))
               (local (defun-nonexec ,g ,vars (,gwit ,@vars)))
               (defthm ,(packn-pos (list g "-DEF") g)
                 (implies ,dom-expr
                          (equal (,g ,@vars)
                                 ,body))
                 ,@keypairs))
              (defthm ,(packn-pos (list g "-IS-UNIQUE") g)
                (implies ,dom-expr
                         (equal (,g ,@vars)
                                (,gwit ,@vars))))
              (in-theory (disable ,(packn-pos (list g "-IS-UNIQUE") g)))
              (verify-guards ,gwit))))
         (t `(encapsulate
              ((,g ,vars t))
              (local (defun-nonexec ,g ,vars
                       (declare (xargs :measure
                                       (if ,dom-expr
                                           ,measure-expr
                                         0)
                                       ,@rest-of-xargs))
                       (if ,dom-expr
                           ,body
                         'undef)))
              (defthm ,(packn-pos (list g "-DEF") g)
                (implies ,dom-expr
                         (equal (,g ,@vars)
                                ,body))
                ,@keypairs)))))))))
   (t (defpun-syntax-er))))
