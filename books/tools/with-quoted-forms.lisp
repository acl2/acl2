; Copyright (C) 2009 Centaur Technology
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
(include-book "std/util/bstar" :dir :system)

;; This book provides a macro WITH-QUOTED-FORMS which may be
;; useful for computing complicated :USE hints.  Often we have a term
;; in which there are many nested variable bindings and we want to
;; instantiate a theorem by setting certain free variables of the
;; theorem to the bound value of some deeply-nested variable of our
;; term.  For example, say we have the term:

;; (let* ((c (foo a b))
;;        (d (bar c a))
;;        (e (baz d c b)))
;;   ...)

;; and that we want to instantiate a theorem TH with variable x bound
;; to the value of E in the above expression.  Ordinarily, we would
;; manually expand the binding of E in order to create the use hint:
;; :use ((:instance th
;;                  (x (baz (bar (foo a b) a) (foo a b) b))))
;; With more complicated sequences of bindings, this can be quite
;; tedious and error-prone.  Using our macro, one can instead write
;; the hint as a computed hint as follows:
;; (with-quoted-forms
;;  (let* ((c (foo a b))
;;         (d (bar c a))
;;         (e (baz d c b)))
;;    `(:use ((:instance th (x ,(fq e)))))))
;; Note that we simply have copied the let* bindings from above, and
;; that where we want the term of E to appear, we instead used the
;; form (fq e).  The result of evaluating this form is the desired use
;; hint from above.

;; How does this work?  First, the form is translated so as to expand
;; away any macros.  Next, it is fully beta-reduced: lambdas are
;; eliminated by replacing occurrences of variables in their bodies
;; with the corresponding bindings.  However, during this process,
;; occurrences of the function FQ (stands for "form-quote") are
;; treated differently: they are turned into quotes after their
;; arguments are beta-reduced.  Thus the occurrence of (FQ E) is
;; replaced by (QUOTE (BAZ (BAR (FOO A B) A) (FOO A B) B)) in the
;; expression above.  Finally, the resulting form is evaluated.

;; Note that the expansion of WITH-QUOTED-FORMS is a call that takes
;; STATE and produces a value-triple.  This is necessary so that it
;; can translate (macroexpand) the given term.

(defthm alistp-pairlis$
  (alistp (pairlis$ a b)))


(mutual-recursion
 (defun beta-reduce-with-quotes (x alist)
   (declare (xargs :guard (and (pseudo-termp x)
                               (alistp alist))))
   (cond ((eq x nil) nil)
         ((atom x)
          (let ((look (assoc x alist)))
            (if look (cdr look) x)))
         ((eq (car x) 'quote) x)
         ((eq (car x) 'fq)
          (cons 'quote (beta-reduce-with-quotes-list (cdr x) alist)))
         ((symbolp (car x))
          (cons (car x) (beta-reduce-with-quotes-list (cdr x) alist)))
         (t (beta-reduce-with-quotes
             (caddar x)
             (pairlis$ (cadar x)
                       (beta-reduce-with-quotes-list
                        (cdr x) alist))))))
 (defun beta-reduce-with-quotes-list (x alist)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (alistp alist))))
   (if (atom x)
       nil
     (cons (beta-reduce-with-quotes (car x) alist)
           (beta-reduce-with-quotes-list (cdr x) alist)))))

(defun fq (x) x)

(defun with-quoted-forms-fn (form state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((er trans)
        (translate form t nil nil 'with-quoted-var-terms
                   (w state) state))
       (reduce (beta-reduce-with-quotes trans nil))
       ((er (cons & val))
        (simple-translate-and-eval
         reduce nil nil
         "Term for with-quoted-forms"
         'with-quoted-var-terms
         (w state) state t)))
    (value val)))

(defmacro with-quoted-forms (form)
  `(with-quoted-forms-fn ',form state))



;; VAR-FQ-BINDINGS makes a list of bindings appropriate for use in a
;; substitution list for a use hint, where each variable name is bound to its
;; FQ.  For example, these two are equivalent:
;;    `(:use ((:instance foo (a ,(fq a)) (b ,(fq b)))))))
;;    `(:use ((:instance foo . ,(var-fq-bindings (a b)))))))

(defun var-fq-bindings-lst (vars)
  (if (atom vars)
      nil
    (cons ``(,',(car vars) ,(fq ,(car vars)))
          (var-fq-bindings-lst (cdr vars)))))


(defmacro var-fq-bindings (vars)
  (cons 'list (var-fq-bindings-lst vars)))




;; This is a different scheme yet: beta-reduce-collect-bindings beta-reduces
;; some term and collects all of the beta-reduced lambda bindings within it
;; into a single alist.  Of course, if a variable is bound more than once, one
;; may shadow the other in the alist.

;; The wrapper macro bind-as-in-definition can be used as follows.
;; Often one needs to prove a theorem about some complicated function and must
;; invoke other theorems via :use hints with substitutions involving
;; intermediate results within the function body.  Say the function is FOO and
;; the terms we want to access are the bound values of variables A, B, and C.
;; Then a computed hint can be generated as follows:
;; (bind-as-in-definition
;;  foo
;;  (a b c)
;;  `(:use ((:instance bar-baz
;;                     (x ,a) (y ,b) (z ,c)))
;;         :in-theory (disable bar-baz)))
;;
;; Optionally, instead of supplying the function name, one can supply
;; a call to the function; the formals will then be bound as specified.
;;
;; Bind-as-in-definition looks up the definition of the given function and
;; beta-reduces its body, collecting the beta-reduced binding of each variable
;; bound by a lambda within that definition.  It then binds the listed
;; variables to the bindings found for them.

(mutual-recursion
 (defun beta-reduce-collect-bindings (x alist bindings)
   (declare (xargs :guard (and (pseudo-termp x)
                               (alistp alist))
                   :mode :program))
   (cond ((eq x nil) (mv nil bindings))
         ((atom x)
          (let ((look (assoc x alist)))
            (mv (if look (cdr look) x) bindings)))
         ((eq (car x) 'quote) (mv x bindings))
         (t
          (mv-let (lst bindings)
            (beta-reduce-collect-bindings-list (cdr x) alist bindings)
            (if (symbolp (car x))
                (mv (cons (car x) lst) bindings)
              (let ((new-bindings (pairlis$ (cadar x) lst)))
                (beta-reduce-collect-bindings
                 (caddar x)
                 new-bindings
                 (append new-bindings bindings))))))))
 (defun beta-reduce-collect-bindings-list (x alist bindings)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (alistp alist))))
   (if (atom x)
       (mv nil bindings)
     (b* (((mv car bindings)
           (beta-reduce-collect-bindings (car x) alist bindings))
          ((mv cdr bindings)
           (beta-reduce-collect-bindings-list (cdr x) alist bindings)))
       (mv (cons car cdr) bindings)))))

(defun bind-according-to-alist-lst (vars alist)
  (if (atom vars)
      nil
    (cons `(,(car vars) (cdr (assoc ',(car vars) ,alist)))
          (bind-according-to-alist-lst (cdr vars) alist))))

(defmacro bind-according-to-alist (alist vars &rest body)
  `(let ,(bind-according-to-alist-lst vars alist)
     . ,body))



(defun bind-as-in-definition-fn (fn-or-call vars term)
  `(b* ((fn-or-call ',fn-or-call)
        (fn (if (consp fn-or-call) (car fn-or-call) fn-or-call))
        (body (getprop fn 'unnormalized-body nil
                       'current-acl2-world (w state)))
        (alist (and (consp fn-or-call)
                    (pairlis$ (fgetprop fn 'formals nil (w state))
                              (cdr fn-or-call))))
        ((mv & bindings)
         (beta-reduce-collect-bindings body alist alist)))
     (bind-according-to-alist
      bindings
      ,vars
      . ,term)))

(defmacro bind-as-in-definition (fn vars &rest term)
  (bind-as-in-definition-fn fn vars term))
