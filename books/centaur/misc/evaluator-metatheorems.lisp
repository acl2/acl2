; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; Have you ever wanted a clause processor to help you prove the
;; correctness of other clause processors?  If so, you might be beyond
;; help.  However, this book defines several functions and theorems
;; that might aid in proving claims about evaluator functions as
;; defined with defevaluator or defevaluator-fast.  See defapply.lisp
;; for an example of how they may be used.  The functions can be used
;; as-is; the theorems will need to be functionally instantiated so as
;; to be usable with the evaluator of your choice, unless the
;; evaluator defined in this book suits your needs.




(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "clause-processors/ev-theoremp" :dir :system)



(defevaluator evmeta-ev evmeta-ev-lst
  ((eql a b)
   (equal a b)
   (implies a b)
   (if a b c)
   (not a)
   (use-by-hint a)
   (use-these-hints a)
   (car x)
   (cdr x)
   (nth n x)
   (cons a b)
   (consp x)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc-eq by assoc-equal).]
   (assoc-equal x a)
   (kwote-lst lst)
   (symbolp x)
   (pairlis$ a b)
   (return-last fn x y)
   (hide a)
   (mv-nth n x)
   (mv-list n x)

   (typespec-check ts x)
   (iff a b)
   (binary-+ a b)
   (unary-- a)
   (len x)))





(def-ev-theoremp evmeta-ev)


;; Constraint 0.
(defun ev-expand-fncall-clause (evfn evlstfn name)
  `((not (use-these-hints '('(:use ,name))))
    (not (consp x))
    (equal (car x) 'quote)
    (equal (,evfn x a)
           (,evfn (cons (car x)
                        (kwote-lst
                         (,evlstfn (cdr x) a)))
                  'nil))))


(defthm ev-expand-fncall-clause-correct
  (implies (and (evmeta-ev-theoremp
                 (disjoin (ev-expand-fncall-clause
                           evfn evlstfn name)))
                (and (consp (evmeta-ev x a)))
                (not (equal (car (evmeta-ev x a)) 'quote))
                (not (equal evfn 'quote))
                (not (equal evlstfn 'quote)))
           (equal (evmeta-ev `(,evfn ,x ,ma) a)
                  (evmeta-ev
                   `(,evfn (cons (car ,x)
                                 (kwote-lst
                                  (,evlstfn (cdr ,x) ,ma)))
                           nil)
                   a)))
  :hints (("goal" :in-theory (enable use-these-hints
                                     evmeta-ev-constraint-0)
           :use ((:instance
                  evmeta-ev-falsify
                  (x (disjoin (ev-expand-fncall-clause
                               evfn evlstfn name)))
                  (a `((x . ,(evmeta-ev x a))
                       (a . ,(evmeta-ev ma a)))))))))

(in-theory (disable ev-expand-fncall-clause))

;; Constraint 1.
(defun ev-lookup-var-clause (evfn name)
  `((not (use-by-hint ',name))
    (not (symbolp x))
    (equal (,evfn x a)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc-eq by assoc-equal).]
           (if x (cdr (assoc-equal x a)) 'nil))))

(defthm ev-lookup-var-clause-correct
  (implies (and (evmeta-ev-theoremp
                 (disjoin (ev-lookup-var-clause evfn name)))
                (symbolp (evmeta-ev x a))
                (not (equal evfn 'quote)))
           (equal (evmeta-ev `(,evfn ,x ,ma) a)
                  (and (evmeta-ev x a)
                       (cdr (assoc-eq (evmeta-ev x a)
                                      (evmeta-ev ma a))))))
  :hints(("Goal" :in-theory (enable use-by-hint
                                    evmeta-ev-constraint-0)
          :use ((:instance
                 evmeta-ev-falsify
                 (x (disjoin (ev-lookup-var-clause evfn name)))
                 (a `((x . ,(evmeta-ev x a))
                      (a . ,(evmeta-ev ma a)))))))))


(in-theory (disable ev-lookup-var-clause))

;; Constraint 2.
(defun ev-quote-clause (evfn name)
  `((not (use-by-hint ',name))
    (not (consp x))
    (not (equal (car x) 'quote))
    (equal (,evfn x a)
           (car (cdr x)))))

(defthm ev-quote-clause-correct
  (implies (and (evmeta-ev-theoremp
                 (disjoin (ev-quote-clause evfn name)))
                (consp (evmeta-ev x a))
                (equal (car (evmeta-ev x a)) 'quote)
                (not (equal evfn 'quote)))
           (equal (evmeta-ev `(,evfn ,x ,ma) a)
                  (cadr (evmeta-ev x a))))
  :hints (("goal" :in-theory (enable use-by-hint
                                     evmeta-ev-constraint-0)
           :use ((:instance
                  evmeta-ev-falsify
                  (x (disjoin (ev-quote-clause evfn name)))
                  (a `((x . ,(evmeta-ev x a))
                      (a . ,(evmeta-ev ma a)))))))))


(in-theory (disable ev-quote-clause))

;; Constraint 3.
(defun ev-lambda-clause (evfn evlstfn name)
  `((not (use-by-hint ',name))
    (not (consp x))
    (not (consp (car x)))
    (equal (,evfn x a)
           (,evfn (car (cdr (cdr (car x))))
                  (pairlis$ (car (cdr (car x)))
                            (,evlstfn (cdr x) a))))))

(defthm ev-lambda-clause-correct
  (implies (and (evmeta-ev-theoremp
                 (disjoin (ev-lambda-clause evfn evlstfn name)))
                (consp (evmeta-ev x a))
                (consp (car (evmeta-ev x a)))
                (not (equal evfn 'quote))
                (not (equal evlstfn 'quote)))
           (equal (evmeta-ev `(,evfn ,x ,ma) a)
                  (evmeta-ev
                   `(,evfn (car (cdr (cdr (car ,x))))
                           (pairlis$ (car (cdr (car ,x)))
                                     (,evlstfn (cdr ,x) ,ma)))
                   a)))
  :hints (("goal" :in-theory (enable use-by-hint
                                     evmeta-ev-constraint-0)
           :use ((:instance
                  evmeta-ev-falsify
                  (x (disjoin (ev-lambda-clause evfn evlstfn name)))
                  (a `((x . ,(evmeta-ev x a))
                       (a . ,(evmeta-ev ma a)))))))))

(in-theory (disable ev-lambda-clause))

;; Constraint 4.
(defun evlst-atom-clause (evlstfn name)
  `((not (use-by-hint ',name))
    (consp x-lst)
    (equal (,evlstfn x-lst a) 'nil)))

(defthm evlst-atom-clause-correct
  (implies (and (evmeta-ev-theoremp
                 (disjoin (evlst-atom-clause evlstfn name)))
                (not (consp (evmeta-ev x-lst a)))
                (not (equal evlstfn 'quote)))
           (equal (evmeta-ev `(,evlstfn ,x-lst ,ma) a)
                  nil))
  :hints (("goal" :in-theory (enable use-by-hint
                                     evmeta-ev-constraint-0)
           :use ((:instance
                  evmeta-ev-falsify
                  (x (disjoin (evlst-atom-clause evlstfn name)))
                  (a `((x-lst . ,(evmeta-ev x-lst a))
                       (a . ,(evmeta-ev ma a)))))))))

(in-theory (disable evlst-atom-clause))

;; Constraint 5.
(defun evlst-cons-clause (evfn evlstfn name)
  `((not (use-by-hint ',name))
    (not (consp x-lst))
    (equal (,evlstfn x-lst a)
           (cons (,evfn (car x-lst) a)
                 (,evlstfn (cdr x-lst) a)))))

(defthm evlst-cons-clause-correct
  (implies (and (evmeta-ev-theoremp
                 (disjoin (evlst-cons-clause evfn evlstfn name)))
                (consp (evmeta-ev x-lst a))
                (not (equal evlstfn 'quote))
                (not (equal evfn 'quote)))
           (equal (evmeta-ev `(,evlstfn ,x-lst ,ma) a)
                  (cons (evmeta-ev `(,evfn (car ,x-lst) ,ma) a)
                        (evmeta-ev `(,evlstfn (cdr ,x-lst) ,ma)
                                     a))))
  :hints (("goal" :in-theory (enable use-by-hint
                                     evmeta-ev-constraint-0)
           :use ((:instance
                  evmeta-ev-falsify
                  (x (disjoin (evlst-cons-clause evfn evlstfn name)))
                  (a `((x-lst . ,(evmeta-ev x-lst a))
                       (a . ,(evmeta-ev ma a)))))))))

(in-theory (disable evlst-cons-clause))

;; Constraints 6 and up.
;; (defun n-cdrs-of-term (n term)
;;   (if (zp n)
;;       term
;;     (list 'cdr (n-cdrs-of-term (1- n) term))))

(defun ev-apply-arglist (n evfn term alist)
  (if (zp n)
      nil
    (cons `(,evfn (car ,term) ,alist)
          (ev-apply-arglist (1- n) evfn `(cdr ,term) alist))))

(defun ev-apply-arglist-on-result (n evfn res alist)
  (if (zp n)
      nil
    (cons `(,evfn ',(car res) ',alist)
          (ev-apply-arglist-on-result
           (1- n) evfn (cdr res) alist))))

(defthm evmeta-ev-lst-ev-apply-arglist
  (implies (not (equal evfn 'quote))
           (equal (evmeta-ev-lst
                   (ev-apply-arglist arity evfn term alist) a)
                  (evmeta-ev-lst
                   (ev-apply-arglist-on-result
                    arity evfn
                    (evmeta-ev term a)
                    (evmeta-ev alist a))
                   nil)))
  :hints (("goal" :in-theory (enable evmeta-ev-constraint-0)
           :induct (ev-apply-arglist arity evfn term alist))))

(defthm evmeta-ev-ev-apply-arglist
  (implies (and (not (equal evfn 'quote))
                (not (equal fn 'quote)))
           (equal (evmeta-ev
                   (cons fn
                         (ev-apply-arglist arity evfn term alist))
                   a)
                  (evmeta-ev
                   (cons fn
                         (kwote-lst
                          (evmeta-ev-lst
                           (ev-apply-arglist-on-result
                            arity evfn
                            (evmeta-ev term a)
                            (evmeta-ev alist a))
                           nil)))
                   nil)))
  :hints(("Goal" :in-theory (enable evmeta-ev-constraint-0))))

(defun ev-function-clause (evfn fn arity name)
  `((not (use-by-hint ',name))
    (not (consp x))
    (not (equal (car x) ',fn))
    (equal (,evfn x a)
           (,fn . ,(ev-apply-arglist arity evfn '(cdr x) 'a)))))

(defthm ev-function-clause-correct
  (implies (and (evmeta-ev-theoremp
                 (disjoin (ev-function-clause evfn fn arity name)))
                (consp (evmeta-ev x a))
                (equal (car (evmeta-ev x a)) fn)
                (not (equal evfn 'quote))
                (not (equal fn 'quote)))
           (equal (evmeta-ev `(,evfn ,x ,ma) a)
                  (evmeta-ev
                   `(,fn . ,(ev-apply-arglist
                             arity evfn `(cdr ,x) ma))
                   a)))
  :hints (("goal" :in-theory (enable use-by-hint
                                     evmeta-ev-constraint-0)
           :use ((:instance
                  evmeta-ev-falsify
                  (x (disjoin (ev-function-clause
                               evfn fn arity name)))
                  (a `((x . ,(evmeta-ev x a))
                       (a . ,(evmeta-ev ma a))))))
           :expand ((:free (res alist)
                           (ev-apply-arglist-on-result
                            1 evfn res alist)))
           :do-not-induct t)
;;           (and stable-under-simplificationp
;;                '(:expand ((:free (evfn term a)
;;                                  (ev-apply-arglist-on-result
;;                                   2 evfn term a)))))
          ))

(in-theory (disable ev-function-clause))



(defun is-n-cdrs-of-x (n term x)
  (if (zp n)
      (eq term x)
    (case-match term
      (('cdr inner)
       (is-n-cdrs-of-x (1- n) inner x)))))

(defun list-of-ev-apps-p (lst evfn index x)
  (if (atom lst)
      (eq lst nil)
    (let ((first (car lst)))
      (case-match first
        ((!evfn ('car n-cdrs-of-x) 'a)
         (and (is-n-cdrs-of-x (1+ index) n-cdrs-of-x x)
              (list-of-ev-apps-p (cdr lst) evfn (1+ index) x)))))))

(defun ev-collect-apply-lemmas1 (lemmas evfn evlstfn)
  (if (atom lemmas)
      nil
    (b* ((rule (car lemmas))
         (hyps (access rewrite-rule rule :hyps))
         (equiv (access rewrite-rule rule :equiv))
         (lhs (access rewrite-rule rule :lhs))
         (rhs (access rewrite-rule rule :rhs))
         (rune (access rewrite-rule rule :rune))
         (aggregate (list hyps rhs))
         (rest (ev-collect-apply-lemmas1 (cdr lemmas) evfn evlstfn)))
      (if (eq equiv 'equal)
          (case-match lhs
            ((!evfn . '(x a))
             (case-match aggregate
               ;; constraint 0: ev-expand-fncall
               (('((consp  x)
                   (synp 'nil '(syntaxp (not (equal a ''nil)))
                         '(if (not (equal a ''nil)) 't 'nil))
                   (not (equal (car x) 'quote)))
                 (!evfn ('cons '(car x)
                               ('kwote-lst (!evlstfn . '((cdr x) a))))
                        ''nil))
                (hons-acons :expand-fncall rune rest))

               ;; constraint 1: ev-lookup-var
               (('((symbolp x))
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc-eq by assoc-equal).]
                 '(if x (cdr (assoc-equal x a)) 'nil))
                (hons-acons :lookup-var rune rest))

               ;; constraint 2: ev-quote
               (('((consp x) (equal (car x) 'quote))
                 '(car (cdr x)))
                (hons-acons :quote rune rest))

               ;; constraint 3: ev-lambda
               (('((consp x) (consp (car x)))
                 (!evfn '(car (cdr (cdr (car x))))
                        ('pairlis$ '(car (cdr (car x)))
                                   (!evlstfn . '((cdr x) a)))))
                (hons-acons :lambda rune rest))

               ;; constraints 6+: ev-function
               ;; special case 1: return-last
               (((('consp 'x) ('equal ('car 'x) '(quote return-last)))
                 (!evfn . '((car (cdr (cdr (cdr x)))) a)))
                (hons-acons 'return-last (cons 3 rune)
                            rest))

               (((('consp 'x) ('equal ('car 'x) '(quote mv-list)))
                 (!evfn . '((car (cdr (cdr x))) a)))
                (hons-acons 'mv-list (cons 2 rune)
                            rest))

               (((('consp 'x) ('equal ('car 'x) ('quote fn)))
                 (fn . list-of-ev-apps))
                (if (list-of-ev-apps-p list-of-ev-apps evfn 0 'x)
                    (hons-acons fn (cons (len list-of-ev-apps) rune)
                                rest)
                  rest))

               (& rest)))

            ;; constraint 4: evlst-atom
            ((!evlstfn . '(x-lst a))
             (case-match aggregate
               (('((not (consp x-lst)))
                 ''nil)
                (hons-acons :lst-atom rune rest))
               (('((consp x-lst))
                 ('cons (!evfn . '((car x-lst) a))
                        (!evlstfn . '((cdr x-lst) a))))
                (hons-acons :lst-cons rune rest))
               (& rest)))

            (& rest))
        rest))))

(defun ev-collect-apply-lemmas (evfn evlstfn world)
  (ev-collect-apply-lemmas1
   (append (fgetprop evfn 'lemmas nil world)
           (fgetprop evlstfn 'lemmas nil world))
   evfn evlstfn))


