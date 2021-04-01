; Centaur Miscellaneous Books
; Copyright (C) 2013 Centaur Technology
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
; beta-reduce-full.lisp
;
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "tools/flag" :dir :system)


;; note: intended to be compatible (redundant) with misc/beta-reduce.lisp
(defevaluator beta-eval beta-eval-list nil)

(mutual-recursion
 (defun beta-reduce-full-rec (x alist)
   (declare (xargs :guard (and (pseudo-termp x)
                               (symbol-alistp alist))
                   :verify-guards nil))
   (b* (((when (null x)) nil)
        ((when (variablep x)) (cdr (assoc x alist)))
        ((when (fquotep x)) x)
        (args (beta-reduce-full-rec-list (fargs x) alist))
        (fn (ffn-symb x))
        ((when (atom fn)) (cons fn args))
        (formals (lambda-formals fn))
        (body (lambda-body fn)))
     (beta-reduce-full-rec body (pairlis$ formals args))))
 (defun beta-reduce-full-rec-list (x alist)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (symbol-alistp alist))))
   (if (endp x)
       nil
     (cons (beta-reduce-full-rec (car x) alist)
           (beta-reduce-full-rec-list (cdr x) alist)))))

(flag::make-flag beta-reduce-flg beta-reduce-full-rec
                 :flag-mapping ((beta-reduce-full-rec term)
                                (beta-reduce-full-rec-list list)))

(defthm len-of-beta-reduce-full-rec-list
  (equal (len (beta-reduce-full-rec-list x alist))
         (len x)))

(defthm true-listp-of-beta-reduce-full-rec-list
  (true-listp (beta-reduce-full-rec-list x alist))
  :hints (("goal" :induct (len x))))

(defthm symbol-alistp-pairlis
  (implies (symbol-listp keys)
           (symbol-alistp (pairlis$ keys vals))))

(verify-guards beta-reduce-full-rec)

(defun beta-eval-alist (x a)
  (if (atom x)
      nil
    (cons (cons (caar x) (beta-eval (cdar x) a))
          (beta-eval-alist (cdr x) a))))

(defthm beta-eval-alist-of-pairlis
  (equal (beta-eval-alist (pairlis$ keys vals) a)
         (pairlis$ keys (beta-eval-list vals a))))

(defthm lookup-in-beta-eval-alist
  (implies k
           (equal (assoc k (beta-eval-alist x a))
                  (and (assoc k x)
                       (cons k (beta-eval (cdr (assoc k x)) a))))))

(local
 (defthm strip-cdrs-of-pairlis
   (implies (and (true-listp vals)
                 (equal (len keys) (len vals)))
            (equal (strip-cdrs (pairlis$ keys valS))
                   vals))))

(defthm-beta-reduce-flg
  (defthm pseudo-termp-of-beta-reduce-full-rec
    (implies (and (pseudo-termp x)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-termp (beta-reduce-full-rec x alist)))
    :flag term)
  (defthm pseudo-term-listp-of-beta-reduce-full-rec-list
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (beta-reduce-full-rec-list x alist)))
    :flag list))

(defthm-beta-reduce-flg
  (defthm beta-reduce-full-rec-correct
    (implies (pseudo-termp x)
             (equal (beta-eval (beta-reduce-full-rec x alist) a)
                    (beta-eval x (beta-eval-alist alist a))))
    :hints ('(:in-theory (enable beta-eval-constraint-0)))
    :flag term)
  (defthm beta-reduce-full-rec-list-correct
    (implies (pseudo-term-listp x)
             (equal (beta-eval-list (beta-reduce-full-rec-list x alist) a)
                    (beta-eval-list x (beta-eval-alist alist a))))
    :flag list))


(mutual-recursion
 (defun beta-reduce-full (x)
   (declare (xargs :guard (pseudo-termp x)))
   (b* (((when (or (variablep x)
                   (fquotep x))) x)
        (args (beta-reduce-full-list (fargs x)))
        (fn (ffn-symb x))
        ((when (atom fn)) (cons fn args))
        (formals (lambda-formals fn))
        (body (lambda-body fn)))
     (beta-reduce-full-rec body (pairlis$ formals args))))
 (defun beta-reduce-full-list (x)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (endp x)
       nil
     (cons (beta-reduce-full (car x))
           (beta-reduce-full-list (cdr x))))))

(defthm len-of-beta-reduce-full-list
  (equal (len (beta-reduce-full-list x))
         (len x)))

(defthm true-listp-of-beta-reduce-full-list
  (true-listp (beta-reduce-full-list x))
  :hints (("goal" :induct (len x))))


(defthm-beta-reduce-flg
  (defthm pseudo-termp-of-beta-reduce-full
    (implies (pseudo-termp x)
             (pseudo-termp (beta-reduce-full x)))
    :flag term)
  (defthm pseudo-term-listp-of-beta-reduce-full-list
    (implies (pseudo-term-listp x)
             (pseudo-term-listp (beta-reduce-full-list x)))
    :flag list))

(defthm-beta-reduce-flg
  (defthm beta-reduce-full-correct
    (implies (pseudo-termp x)
             (equal (beta-eval (beta-reduce-full x) a)
                    (beta-eval x a)))
    :hints ('(:in-theory (enable beta-eval-constraint-0)))
    :flag term)
  (defthm beta-reduce-full-list-correct
    (implies (pseudo-term-listp x)
             (equal (beta-eval-list (beta-reduce-full-list x) a)
                    (beta-eval-list x a)))
    :flag list))


