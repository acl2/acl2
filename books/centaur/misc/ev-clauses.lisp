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

(include-book "evaluator-metatheorems")
;; These were removed from evaluator-metatheorems for some reason, but they're
;; still used e.g. in defapply.lisp.

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
