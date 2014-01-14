; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

; cert_param: (non-acl2r)

(include-book "system/sublis-var" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
;; Prove CONS-TERM and CONS-TERM1-MV2 are simply applying the fn to the args.

(defevaluator-fast cterm-ev cterm-ev-lst
  ((acl2-numberp x)
   (binary-* x y)
   (binary-+ x y)
   (unary-- x)
   (unary-/ x)
   (< x y)
   (car x)
   (cdr x)
   (char-code x)
   (characterp x)
   (code-char x)
   (complex x y)
   (complex-rationalp x)
   (coerce x y)
   (cons x y)
   (consp x)
   (denominator x)
   (equal x y)
   (imagpart x)
   (integerp x)
   (intern-in-package-of-symbol x y)
   (numerator x)
   (rationalp x)
   (realpart x)
   (stringp x)
   (symbol-name x)
   (symbol-package-name x)
   (symbolp x)
   (if x y z)
   (not x))
  :namedp t)

(defthm cterm-ev-cons-term-correct
  (equal (cterm-ev (cons-term fn args) a)
         (cterm-ev (cons fn args) a))
  :hints ((and stable-under-simplificationp
               '(:expand ((quote-listp (cdr args))
                          (quote-listp (cddr args)))))))

(defthm cterm-ev-cons-term1-mv2-correct
  (implies (and (quote-listp args)
                (equal (cterm-ev form a)
                       (cterm-ev (cons fn args) a)))
           (mv-let (flg result)
             (cons-term1-mv2 fn args form)
             (declare (ignore flg))
             (equal (cterm-ev result a)
                    (cterm-ev (cons fn args) a))))
  :hints (("goal" :do-not-induct t)
          (and stable-under-simplificationp
               '(:expand ((quote-listp (cdr args))
                          (quote-listp (cddr args)))))))

(defthm cons-term1-mv2-when-unchanged
  (mv-let (changedp result)
    (cons-term1-mv2 fn args form)
    (implies (not changedp)
             (equal result form))))

(defthm pseudo-termp-cons-term
  (implies (and (symbolp fn)
                (not (eq fn 'quote))
                (pseudo-term-listp args))
           (pseudo-termp (cons-term fn args))))

(defthm pseudo-termp-cons-term1-mv2
  (implies (and (symbolp fn)
                (not (eq fn 'quote))
                (pseudo-term-listp args))
           (pseudo-termp (cons-term1-mv2 fn args (cons fn args)))))

(in-theory (disable cons-term cons-term1-mv2))


; Goal now is to prove that sublis-var1 evaluates to the same thing as this
; much simpler function.  (Unfortunately we can't use substitute-into-term from
; unify-subst because it behaves differently on unbound variables.)

(mutual-recursion
 (defun term-subst (x alist)
   (declare (xargs :guard (and (symbol-alistp alist)
                               (pseudo-termp x))))
   (cond ((variablep x)
          (let ((a (assoc-eq x alist)))
            (if a (cdr a) x)))
         ((fquotep x) x)
         (t (cons (ffn-symb x)
                  (termlist-subst (fargs x) alist)))))
 (defun termlist-subst (x alist)
   (declare (xargs :guard (and (symbol-alistp alist)
                               (pseudo-term-listp x))))
   (if (endp x)
       x
     (cons (term-subst (car x) alist)
           (termlist-subst (cdr x) alist)))))

(make-flag term-subst-flg term-subst
           :flag-mapping ((term-subst . term)
                          (termlist-subst . list)))

;; (defthm-term-subst-flg
;;   (defthm term-subst-when-unchanged
;;     (implies (not (mv-nth 0 (sublis-var1 alist x)))
;;              (equal (cterm-ev (term-subst x alist) a)
;;                     (cterm-ev x a)))
;;     :hints ((and stable-under-simplificationp
;;                  '(:in-theory (enable cterm-ev-of-fncall-args))))
;;     :flag term)
;;   (defthm sublis-var1lst-is-termlist-subst
;;     (implies (not (mv-nth 0 (sublis-var1-lst alist x)))
;;              (equal (cterm-ev-lst (termlist-subst x alist) a)
;;                     (cterm-ev-lst x a)))
;;     :flag list))

(defthm-term-subst-flg
  (defthm sublis-var1-when-unchanged
    (implies (not (mv-nth 0 (sublis-var1 alist x)))
             (equal (cterm-ev (mv-nth 1 (sublis-var1 alist x)) a)
                    (cterm-ev x a)))
    :flag term)
  (defthm sublis-var1-lst-when-unchanged
    (implies (not (mv-nth 0 (sublis-var1-lst alist x)))
             (equal (cterm-ev-lst (mv-nth 1 (sublis-var1-lst alist x)) a)
                    (cterm-ev-lst x a)))
    :flag list))


(defthm-term-subst-flg
  (defthm sublis-var1-is-term-subst
    (equal (cterm-ev (mv-nth 1 (sublis-var1 alist x)) a)
           (cterm-ev (term-subst x alist) a))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable cterm-ev-of-fncall-args))))
    :flag term)
  (defthm sublis-var1-lst-is-termlist-subst
    (equal (cterm-ev-lst (mv-nth 1 (sublis-var1-lst alist x)) a)
           (cterm-ev-lst (termlist-subst x alist) a))
    :flag list))

(defthm len-of-termlist-subst
  (equal (len (termlist-subst x alist))
         (len x))
  :hints (("goal" :induct (len x)
           :expand ((termlist-subst x alist)))))

(defthm pseudo-termp-of-lookup
  (implies (and (pseudo-term-listp (strip-cdrs alist))
                (assoc x alist))
           (pseudo-termp (cdr (assoc x alist)))))

(defthm-term-subst-flg
  (defthm pseudo-termp-of-term-subst
    (implies (and (pseudo-termp x)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-termp (term-subst x alist)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x y) (pseudo-termp (cons x y)))))))
    :flag term)
  (defthm pseudo-term-listp-of-termlist-subst
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (termlist-subst x alist)))
    :flag list))

(defun cterm-ev-alist (x a)
  (if (atom x)
      nil
    (cons (cons (caar x) (cterm-ev (cdar x) a))
          (cterm-ev-alist (cdr x) a))))

(defthm lookup-in-cterm-ev-alist
  (implies k
           (equal (assoc k (cterm-ev-alist x a))
                  (and (assoc k x)
                       (cons k (cterm-ev (cdr (assoc k x)) a))))))

(defthm assoc-of-append-when-alistp-x
  (implies (alistp x)
           (equal (assoc k (append x y))
                  (or (assoc k x)
                      (assoc k y)))))

(defthm alistp-of-cterm-ev-alist
  (alistp (cterm-ev-alist x a)))

(defthm-term-subst-flg
  (defthm eval-of-term-subst
    (implies (and (pseudo-termp x)
                  (not (assoc nil alist)))
             (equal (cterm-ev (term-subst x alist) a)
                    (cterm-ev x (append (cterm-ev-alist alist a) a))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable cterm-ev-of-fncall-args))))
    :flag term)
  (defthm eval-of-termlist-subst
    (implies (and (pseudo-term-listp x)
                  (not (assoc nil alist))) 
             (equal (cterm-ev-lst (termlist-subst x alist) a)
                    (cterm-ev-lst x (append (cterm-ev-alist alist a) a))))
    :flag list))


(defthm eval-of-sublis-var
  (implies (and (pseudo-termp x)
                (not (assoc nil alist)))
           (equal (cterm-ev (sublis-var alist x) a)
                  (cterm-ev x (append (cterm-ev-alist alist a) a)))))

(in-theory (disable sublis-var))



