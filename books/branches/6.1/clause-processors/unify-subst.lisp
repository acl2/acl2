
; Unify-subst.lisp: Term unification and substitution functions, and theorems
; for reasoning about them.

; Copyright (C) 2010 Centaur Technology
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

;; This may be useful for meta and clause processor rules.  Sometimes one wants
;; to reason about terms that unify with some pattern term.  One choice is to
;; use case-match, but this can be a big hassle because, for a large term, you
;; end up with tons of hyps about (consp (caddar (cdddar (cdar term)))) and the
;; like.  This provides another way:  simple-one-way-unify checks if your term
;; matches some template and provides a substitution alist that gives the
;; correspondence if it does.   We provide theorems that allow you to then
;; reason about the template directly and later apply those conclusions to any
;; term that matches the template.

;; To use these theorems with your own evaluator, you'll need to provide an
;; alist evaluator function corresponding to unify-ev-alist, then use a
;; functional instance to substitute unify-ev, unify-ev-lst, and unify-ev-alist
;; for your evaluator, list-evaluator, and alist-evaluator.  You'll probably
;; also want to prove a lemma corresponding to assoc-equal-unify-ev-alist.

(include-book "tools/flag" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "tools/def-functional-instance" :dir :system)
(include-book "ev-find-rules")

(defevaluator unify-ev unify-ev-lst
  ((cons a b) (binary-+ a b)))

(defun unify-ev-alist (x al)
  (if (atom x)
      nil
    (cons (cons (caar x) (unify-ev (cdar x) al))
          (unify-ev-alist (cdr x) al))))
(defthm assoc-equal-unify-ev-alist
  (equal (cdr (assoc-equal k (unify-ev-alist x al)))
         (unify-ev (cdr (assoc-equal k x)) al)))

(defthm assoc-equal-unify-ev-alist-iff
  (implies k
           (iff (assoc-equal k (unify-ev-alist x al))
                (assoc-equal k x))))

(defthm assoc-equal-unify-ev-alist-when-assoc
  (implies (assoc k x)
           (assoc k (unify-ev-alist x al))))

(defthm unify-ev-alist-pairlis$
  (equal (unify-ev-alist (pairlis$ a b) al)
         (pairlis$ a
                   (unify-ev-lst b al))))

(local (defthm assoc-equal-consp
         (implies (alistp x)
                  (or (not (assoc-equal k x))
                      (consp (assoc-equal k x))))
         :rule-classes (:type-prescription
                        (:rewrite
                         :corollary (implies (and (alistp x)
                                                  (assoc-equal k x))
                                             (consp (assoc-equal k x)))))))



(defun all-keys-bound (keys alist)
  (if (atom keys)
      t
    (and (assoc-equal (car keys) alist)
         (all-keys-bound (cdr keys) alist))))

(defthmd all-keys-bound-member
  (implies (and (all-keys-bound keys alist)
                (member-equal k keys))
           (assoc-equal k alist)))

(defthm member-of-union-equal
  (iff (member-equal x (union-equal a b))
       (or (member-equal x a)
           (member-equal x b))))

(defthm all-keys-bound-union-equal
  (equal (all-keys-bound (union-equal a b) alist)
         (and (all-keys-bound a alist)
              (all-keys-bound b alist)))
  :hints(("Goal" :in-theory (enable union-equal all-keys-bound-member))))


(mutual-recursion
 (defun simple-term-vars (x)
   (cond ((null x) nil)
         ((atom x) (list x))
         ((eq (car x) 'quote) nil)
         (t (simple-term-vars-lst (cdr x)))))
 (defun simple-term-vars-lst (x)
   (if (atom x)
       nil
     (union-equal (simple-term-vars (car x))
                  (simple-term-vars-lst (cdr x))))))

(flag::make-flag simple-term-vars-flag simple-term-vars)

(defthm-simple-term-vars-flag
  (defthm unify-ev-of-acons-when-all-vars-bound
    (implies (and (all-keys-bound (simple-term-vars x) a)
                  (not (assoc k a))
                  (pseudo-termp x))
             (equal (unify-ev x (cons (cons k v) a))
                    (unify-ev x a)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable unify-ev-constraint-0))))
    :flag simple-term-vars)
  (defthm unify-ev-lst-of-acons-when-all-vars-bound
    (implies (and (all-keys-bound (simple-term-vars-lst x) a)
                  (not (assoc k a))
                  (pseudo-term-listp x))
             (equal (unify-ev-lst x (cons (cons k v) a))
                    (unify-ev-lst x a)))
    :flag simple-term-vars-lst))

(defthm all-keys-bound-of-unify-ev-alist
  (implies (all-keys-bound keys alist)
           (all-keys-bound keys (unify-ev-alist alist a))))


(mutual-recursion
 (defun substitute-into-term (x al)
   (declare (xargs :guard (and (pseudo-termp x)
                               (alistp al))))
   (cond ((null x) nil)
         ((atom x) (cdr (assoc-equal x al)))
         ((eq (car x) 'quote) x)
         (t (cons (car x) (substitute-into-list (cdr x) al)))))
 (defun substitute-into-list (x al)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (alistp al))))
   (if (atom x)
       nil
     (cons (substitute-into-term (car x) al)
           (substitute-into-list (cdr x) al)))))



(flag::make-flag substitute-into-term-flag substitute-into-term)



(defun pseudo-term-val-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (pseudo-termp (cdar x))
         (pseudo-term-val-alistp (cdr x)))))

(defthm pseudo-termp-assoc
  (implies (pseudo-term-val-alistp x)
           (pseudo-termp (cdr (assoc-equal k x)))))

(defthm-substitute-into-term-flag
  substitute-into-term-correct-lemma
  (substitute-into-term
   (implies
    (pseudo-termp x)
    (equal (unify-ev (substitute-into-term x subst) a)
           (unify-ev x (unify-ev-alist subst a))))
   :name substitute-into-term-correct)
  (substitute-into-list
   (implies
    (pseudo-term-listp x)
    (equal (unify-ev-lst (substitute-into-list x subst) a)
           (unify-ev-lst x (unify-ev-alist subst a))))
   :name substitute-into-list-correct)
  :hints (("goal" :induct (substitute-into-term-flag flag x subst))
          (and stable-under-simplificationp
               '(:in-theory (enable unify-ev-constraint-0)))))

(defthm len-substitute-into-list
  (equal (len (substitute-into-list x subst))
         (len x)))


(defthm-substitute-into-term-flag
  substitute-into-term-pseudo-termp-lemma
  (substitute-into-term
   (implies
    (and (pseudo-termp x) (pseudo-term-val-alistp subst))
    (pseudo-termp (substitute-into-term x subst)))
   :name substitute-into-term-pseudo-termp)
  (substitute-into-list
   (implies
    (and (pseudo-term-listp x) (pseudo-term-val-alistp subst))
    (pseudo-term-listp (substitute-into-list x subst)))
   :name substitute-into-list-pseudo-term-listp)
  :hints (("goal" :induct (substitute-into-term-flag flag x subst))
          (and stable-under-simplificationp
               '(:expand ((pseudo-termp x)
                          (:free (a b) (pseudo-termp (cons a b))))))))


;; assumes x is a lambda
(defun beta-reduce1 (x)
  (substitute-into-term
   (caddar x)
   (pairlis$ (cadar x) (cdr x))))

(defun lambdap (x)
  (and (consp x) (consp (car x)) (eq (caar x) 'lambda)))

(defthm beta-reduce1-correct
  (implies (and (lambdap x)
                (pseudo-termp x))
           (equal (unify-ev (beta-reduce1 x) al)
                  (unify-ev x al))))

(defthm pseudo-term-val-alistp-pairlis$
  (implies (pseudo-term-listp x)
           (pseudo-term-val-alistp (pairlis$ keys x))))

(defthm beta-reduce1-pseudo-termp
  (implies (pseudo-termp x)
           (pseudo-termp (beta-reduce1 x))))


(in-theory (disable beta-reduce1))




(defun unify-const (pat const alist)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (alistp alist))))
  (cond ((null pat)
         (if (eq const nil)
             (mv t alist)
           (mv nil (cons (cons pat (kwote const)) alist))))
        ((variablep pat)
         (let ((pair (assoc pat alist)))
           (if pair
               (let ((term (cdr pair)))
                 (if (and (quotep term)
                          (consp (cdr term))
                          (equal (unquote term) const)
                          (null (cddr term)))
                     (mv t alist)
                   (mv nil (cons (cons pat (kwote const)) alist))))
             (mv t (cons (cons pat (kwote const)) alist)))))
        ((eq (car pat) 'quote)
         (if (equal (unquote pat) const)
             (mv t alist)
           (mv nil (cons (cons pat (kwote const)) alist))))
        ((and (eq (car pat) 'cons)
              (int= (len pat) 3))
         (if (consp const)
             (b* (((mv car-ok alist)
                   (unify-const (second pat) (car const) alist))
                  ((unless car-ok) (mv nil alist)))
               (unify-const (third pat) (cdr const) alist))
           (mv nil (cons (cons pat (kwote const)) alist))))
        ((and (eq (car pat) 'binary-+)
              (int= (len pat) 3))
         (cond ((not (acl2-numberp const))
                (mv nil (cons (cons pat (kwote const)) alist)))
               ((quotep (second pat))
                (let ((num (unquote (second pat))))
                  (if (acl2-numberp num)
                      (unify-const (third pat) (- const num) alist)
                    (mv nil (cons (cons pat (kwote const)) alist)))))
               ((quotep (third pat))
                (let ((num (unquote (third pat))))
                  (if (acl2-numberp num)
                      (unify-const (second pat) (- const num) alist)
                    (mv nil (cons (cons pat (kwote const)) alist)))))
               (t (mv nil (cons (cons pat (kwote const)) alist)))))
        (t (mv nil (cons (cons pat (kwote const)) alist)))))

(defthm pseudo-term-val-alistp-of-unify-const
  (equal (pseudo-term-val-alistp
          (mv-nth 1 (unify-const pat const alist)))
         (pseudo-term-val-alistp alist)))

(defthm alistp-of-unify-const
  (equal (alistp (mv-nth 1 (unify-const pat const alist)))
         (alistp alist)))

(defthm unify-const-preserves-assoc-exists
  (implies (assoc k alist)
           (assoc k (mv-nth 1 (unify-const pat const alist)))))

(defthm unify-const-preserves-assoc
  (b* (((mv ok newalist) (unify-const pat const alist))
       (look (assoc k alist)))
    (implies (and ok
                  look)
             (equal (assoc k newalist)
                    look))))

(defthm acons-preserves-all-keys-bound
  (implies (all-keys-bound keys alist)
           (all-keys-bound keys (cons (cons k v) alist))))

(defthm unify-const-preserves-all-keys-bound
  (b* (((mv ?ok newalist) (unify-const pat const alist)))
    (implies (all-keys-bound keys alist)
             (all-keys-bound keys newalist))))
       

(encapsulate nil
  (local (defthm equal-of-len
           (equal (equal (len x) n)
                  (if (zp n)
                      (and (equal n 0)
                           (not (consp x)))
                    (and (consp x)
                         (equal (len (cdr x)) (1- n)))))))
  (local (in-theory (disable len)))
  (defthm all-keys-bound-of-unify-const
    (b* (((mv ok newalist) (unify-const pat const alist)))
      (implies ok
               (all-keys-bound (simple-term-vars pat) newalist)))
    :hints (("goal" :induct (unify-const pat const alist)
             :expand ((unify-const pat const alist))
             :in-theory (disable (:d unify-const)))
            (and stable-under-simplificationp
                 '(:expand ((simple-term-vars-lst (cddr pat))))))))


(defthm unify-const-preserves-eval
  (mv-let (ok subst)
    (unify-const pat const alist)
    (implies (and ok
                  (pseudo-termp term2)
                  (all-keys-bound (simple-term-vars term2) alist))
             (equal (unify-ev term2 (unify-ev-alist subst a))
                    (unify-ev term2 (unify-ev-alist alist a))))))

(defthm unify-const-preserves-eval-lst
  (mv-let (ok subst)
    (unify-const pat const alist)
    (implies (and ok
                  (pseudo-term-listp term2)
                  (all-keys-bound (simple-term-vars-lst term2) alist))
             (equal (unify-ev-lst term2 (unify-ev-alist subst a))
                    (unify-ev-lst term2 (unify-ev-alist alist a))))))


(defthm unify-const-correct
  (mv-let (ok subst)
    (unify-const pat const alist)
    (implies (and ok
                  (pseudo-termp pat))
             (equal (unify-ev pat (unify-ev-alist subst a))
                    const)))
  :hints (("goal" :induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable unify-ev-constraint-0)))))

(in-theory (disable unify-const))




(mutual-recursion
 (defun simple-one-way-unify (pat term alist)
   (declare (xargs :guard (and (pseudo-termp pat)
                               (pseudo-termp term)
                               (alistp alist))))
   (cond ((null pat)
          (if (or (eq term nil)
                  (equal term *nil*))
              (mv t alist)
            (mv nil (cons (cons pat term) alist))))
         ((atom pat)
          (let ((pair (assoc-equal pat alist)))
            (if pair
                (if (equal term (cdr pair))
                    (mv t alist)
                  (mv nil (cons (cons pat term) alist)))
              (mv t (cons (cons pat term) alist)))))
         ((atom term)
          (mv nil (cons (cons pat term) alist)))
         ((eq (car pat) 'quote)
          (if (equal pat term)
              (mv t alist)
            (mv nil (cons (cons pat term) alist))))
         ((eq (car term) 'quote)
          (unify-const pat (unquote term) alist))
         ((equal (car pat) (car term))
          (simple-one-way-unify-lst (cdr pat) (cdr term) alist))
         (t (mv nil (cons (cons pat term) alist)))))
 (defun simple-one-way-unify-lst (pat term alist)
   (declare (xargs :guard (and (pseudo-term-listp pat)
                               (pseudo-term-listp term)
                               (alistp alist))
                   :verify-guards nil))
   (if (atom pat)
       (if (atom term)
           (mv t alist)
         (mv nil alist))
     (if (atom term)
         (mv nil alist)
       (mv-let (ok alist)
         (simple-one-way-unify (car pat) (car term) alist)
         (if ok
             (simple-one-way-unify-lst (cdr pat) (cdr term) alist)
           (mv nil alist)))))))

(flag::make-flag simple-one-way-unify-flag simple-one-way-unify)


(defthm-simple-one-way-unify-flag
  pseudo-term-val-alistp-simple-one-way-unify-lemma
  (simple-one-way-unify
   (implies (and (pseudo-termp term)
                 (pseudo-term-val-alistp alist))
            (pseudo-term-val-alistp (mv-nth 1 (simple-one-way-unify
                                           pat term alist))))
   :name pseudo-term-val-alistp-simple-one-way-unify)
  (simple-one-way-unify-lst
   (implies (and (pseudo-term-listp term)
                 (pseudo-term-val-alistp alist))
            (pseudo-term-val-alistp (mv-nth 1 (simple-one-way-unify-lst
                                           pat term alist))))
   :name pseudo-term-val-alistp-simple-one-way-unify-lst)
  :hints (("Goal" :induct (simple-one-way-unify-flag flag pat term alist)
           :expand ((:free (x) (simple-one-way-unify pat x alist))
                    (:free (x) (simple-one-way-unify-lst pat x alist))
                    (:free (x) (simple-one-way-unify x term alist))
                    (:free (x) (simple-one-way-unify-lst x term alist))
                    (simple-one-way-unify nil nil alist)
                    (pseudo-termp term)))))


(defthm-simple-one-way-unify-flag
  alistp-simple-one-way-unify-lemma
  (simple-one-way-unify
   (implies (alistp alist)
            (alistp (mv-nth 1 (simple-one-way-unify
                               pat term alist))))
   :name alistp-simple-one-way-unify)
  (simple-one-way-unify-lst
   (implies (alistp alist)
            (alistp (mv-nth 1 (simple-one-way-unify-lst
                               pat term alist))))
   :name alistp-simple-one-way-unify-lst)
  :hints (("Goal" :induct (simple-one-way-unify-flag flag pat term alist)
           :expand ((:free (x) (simple-one-way-unify pat x alist))
                    (:free (x) (simple-one-way-unify-lst pat x alist))
                    (:free (x) (simple-one-way-unify x term alist))
                    (:free (x) (simple-one-way-unify-lst x term alist))
                    (simple-one-way-unify nil nil alist)
                    (pseudo-termp term)))))

(verify-guards simple-one-way-unify)




(defthm-simple-one-way-unify-flag
  assoc-one-way-unify-lemma
  (defthm assoc-equal-of-simple-one-way-unify-preserved
   (implies (and (assoc-equal k alist)
                 (mv-nth 0 (simple-one-way-unify pat x alist)))
            (equal (assoc-equal k (mv-nth 1 (simple-one-way-unify pat x alist)))
                   (assoc-equal k alist)))
   :flag simple-one-way-unify)
  (defthm assoc-equal-of-simple-one-way-unify-lst-preserved
    (implies (and (assoc-equal k alist)
                  (mv-nth 0 (simple-one-way-unify-lst pat x alist)))
             (equal (assoc-equal k (mv-nth 1 (simple-one-way-unify-lst pat x alist)))
                    (assoc-equal k alist)))
    :flag simple-one-way-unify-lst)
  :hints (("goal" :induct (simple-one-way-unify-flag flag pat x alist))))


(defthm-simple-term-vars-flag
  substitute-into-one-way-unify-reduce-lemma
  (simple-term-vars
   (implies (and (all-keys-bound (simple-term-vars term) alist)
                 (mv-nth 0 (simple-one-way-unify pat x alist)))
            (equal (substitute-into-term
                    term (mv-nth 1 (simple-one-way-unify pat x alist)))
                   (substitute-into-term term alist)))
   :name substitute-into-one-way-unify-reduce)
  (simple-term-vars-lst
   (implies (and (all-keys-bound (simple-term-vars-lst term) alist)
                 (mv-nth 0 (simple-one-way-unify pat x alist)))
            (equal (substitute-into-list
                    term (mv-nth 1 (simple-one-way-unify pat x alist)))
                   (substitute-into-list term alist)))
   :name substitute-into-one-way-unify-reduce-list)
  :hints (("goal" :induct (simple-term-vars-flag flag term)
            :in-theory (enable subsetp-equal))))

(defthm-simple-term-vars-flag
  substitute-into-one-way-unify-lst-reduce-lemma
  (simple-term-vars
   (implies (and (all-keys-bound (simple-term-vars term) alist)
                 (mv-nth 0 (simple-one-way-unify-lst pat x alist)))
            (equal (substitute-into-term
                    term (mv-nth 1 (simple-one-way-unify-lst pat x alist)))
                   (substitute-into-term term alist)))
   :name substitute-into-one-way-unify-lst-reduce)
  (simple-term-vars-lst
   (implies (and (all-keys-bound (simple-term-vars-lst term) alist)
                 (mv-nth 0 (simple-one-way-unify-lst pat x alist)))
            (equal (substitute-into-list
                    term (mv-nth 1 (simple-one-way-unify-lst pat x alist)))
                   (substitute-into-list term alist)))
   :name substitute-into-one-way-unify-lst-reduce-list)
  :hints (("goal" :induct (simple-term-vars-flag flag term)
            :in-theory (enable subsetp-equal))))


(defthm-simple-one-way-unify-flag
  one-way-unify-all-keys-bound-lemma
  (simple-one-way-unify
   (mv-let (ok subst)
     (simple-one-way-unify pat x alist)
     (declare (ignore ok))
     (implies (all-keys-bound keys alist)
              (all-keys-bound keys subst)))
   :name one-way-unify-all-keys-bound)
  (simple-one-way-unify-lst
   (mv-let (ok subst)
     (simple-one-way-unify-lst pat x alist)
     (declare (ignore ok))
     (implies (all-keys-bound keys alist)
              (all-keys-bound keys subst)))
   :name one-way-unify-lst-all-keys-bound)
  :hints (("goal" :induct (simple-one-way-unify-flag flag pat x alist))))


(defthm-simple-one-way-unify-flag
  one-way-unify-all-vars-bound-lemma
  (simple-one-way-unify
   (mv-let (ok subst)
     (simple-one-way-unify pat x alist)
     (implies ok
              (all-keys-bound (simple-term-vars pat) subst)))
   :name one-way-unify-all-vars-bound)
  (simple-one-way-unify-lst
   (mv-let (ok subst)
     (simple-one-way-unify-lst pat x alist)
     (implies ok
              (all-keys-bound (simple-term-vars-lst pat) subst)))
   :name one-way-unify-lst-all-vars-bound)
  :hints (("goal" :induct (simple-one-way-unify-flag flag pat x alist))))



;; (defthm-simple-one-way-unify-flag
;;   simple-one-way-unify-correct-lemma
;;   (simple-one-way-unify
;;    (mv-let (okp subst)
;;      (simple-one-way-unify pat x alist)
;;      (implies (and (pseudo-termp x)
;;                    okp)
;;               (equal (substitute-into-term pat subst) x)))
;;    :name simple-one-way-unify-correct)
;;   (simple-one-way-unify-lst
;;    (mv-let (okp subst)
;;      (simple-one-way-unify-lst pat x alist)
;;      (implies (and (pseudo-term-listp x)
;;                    okp)
;;               (equal (substitute-into-list pat subst) x)))
;;    :name simple-one-way-unify-lst-correct)
;;   :hints (("goal" :induct (simple-one-way-unify-flag flag pat x alist))))

(in-theory (disable simple-one-way-unify simple-one-way-unify-lst))

(defthm-simple-one-way-unify-flag
  (defthm simple-one-way-unify-preserves-eval
    (mv-let (ok subst)
      (simple-one-way-unify pat term alist)
      (implies (and ok
                    (pseudo-termp term2)
                    (all-keys-bound (simple-term-vars term2) alist))
               (equal (unify-ev term2 (unify-ev-alist subst a))
                      (unify-ev term2 (unify-ev-alist alist a)))))
    :hints ('(:expand ((:free (term) (simple-one-way-unify pat term alist))
                       (:free (term) (simple-one-way-unify nil term alist)))))
    :flag simple-one-way-unify)
  (defthm simple-one-way-unify-lst-preserves-eval
    (mv-let (ok subst)
      (simple-one-way-unify-lst pat term alist)
      (implies (and ok
                    (pseudo-termp term2)
                    (all-keys-bound (simple-term-vars term2) alist))
               (equal (unify-ev term2 (unify-ev-alist subst a))
                      (unify-ev term2 (unify-ev-alist alist a)))))
    :hints ('(:expand (simple-one-way-unify-lst pat term alist)))
    :flag simple-one-way-unify-lst))

(defthm-simple-one-way-unify-flag
  (defthm simple-one-way-unify-preserves-eval-lst
    (mv-let (ok subst)
      (simple-one-way-unify pat term alist)
      (implies (and ok
                    (pseudo-term-listp term2)
                    (all-keys-bound (simple-term-vars-lst term2) alist))
               (equal (unify-ev-lst term2 (unify-ev-alist subst a))
                      (unify-ev-lst term2 (unify-ev-alist alist a)))))
    :hints ('(:expand ((:free (term) (simple-one-way-unify pat term alist))
                       (:free (term) (simple-one-way-unify nil term alist)))))
    :flag simple-one-way-unify)
  (defthm simple-one-way-unify-lst-preserves-eval-lst
    (mv-let (ok subst)
      (simple-one-way-unify-lst pat term alist)
      (implies (and ok
                    (pseudo-term-listp term2)
                    (all-keys-bound (simple-term-vars-lst term2) alist))
               (equal (unify-ev-lst term2 (unify-ev-alist subst a))
                      (unify-ev-lst term2 (unify-ev-alist alist a)))))
    :hints ('(:expand (simple-one-way-unify-lst pat term alist)))
    :flag simple-one-way-unify-lst))

(defthm-simple-one-way-unify-flag
  (defthm simple-one-way-unify-correct
    (mv-let (ok subst)
      (simple-one-way-unify pat term alist)
      (implies (and ok
                    (pseudo-termp term)
                    (pseudo-termp pat))
               (equal (unify-ev pat (unify-ev-alist subst a))
                      (unify-ev term a))))
    :hints ('(:expand ((:free (term) (simple-one-way-unify pat term alist))
                       (:free (term) (simple-one-way-unify nil term alist))))
            (and stable-under-simplificationp
                 '(:in-theory (enable unify-ev-constraint-0))))
    :flag simple-one-way-unify)
  (defthm simple-one-way-unify-lst-correct
    (mv-let (ok subst)
      (simple-one-way-unify-lst pat term alist)
      (implies (and ok
                    (pseudo-term-listp term)
                    (pseudo-term-listp pat))
               (equal (unify-ev-lst pat (unify-ev-alist subst a))
                      (unify-ev-lst term a))))
    :hints ('(:expand (simple-one-way-unify-lst pat term alist)))
    :flag simple-one-way-unify-lst))


;; Note on the above theorem.

;; At first glance this seems like a nice rewrite rule: there are no free
;; variables and there's a nice reduction in term size.  But this exact pattern
;; of the LHS:
;; (eval pat (eval-alist (mv-nth 1 (simple-one-way-unify pat term alist)) a))
;; is rarely found, because usually the purpose of unifying is to resubstitute
;; into some different (but known equivalent) term -- so we're more likely to
;; see
;; (eval some-other-term (eval-alist (mv-nth 1 (simple-one-way-unify pat ...))))

;; A previous solution was to reverse the LHS/RHS of the rewrite:

;; (defthm simple-one-way-unify-usage
;;   (mv-let (ok subst)
;;     (simple-one-way-unify pat term alist)
;;     (implies (and ok
;;                   (pseudo-termp term)
;;                   (pseudo-termp pat))
;;              (equal (unify-ev term a)
;;                     (unify-ev pat (unify-ev-alist subst a))))))

;; This rule will then trigger on any LHS of the form (eval term a). But then
;; the first hyp requires that it finds a binding for pat and alist for which
;; we know (mv-nth 0 (simple-one-way-unify pat term alist)); that is, the term
;; is known to unify with some pattern.
;; But this isn't exactly a satisfactory rewrite rule either --  for one
;; thing, often when we have (eval term a), term isn't the thing that has been
;; unified, but (say) some subterm -- i.e. suppose the term we're unifying is
;; (f x y) and eval "understands" f, so that (eval term a) rewrites to (f (eval
;; x a) (eval y a)).  Then we've lost the opportunity to apply this rule,
;; because neither the (eval x a) nor (eval y a) will match (mv-nth 0
;; (simple-one-way-unify pat (f x y) alist)).

;; What we really want to do is instantiate this correctness theorem whenever
;; we know some unification occurred.  We could do this by rewriting as follows:
;; (iff (mv-nth 0 (simple-one-way-unify pat term alist))
;;      (and (hide (mv-nth 0 (simple-one-way-unify pat term alist)))
;;           ;; the above is because we actually want to rewrite on an
;;           ;; implication, not an iff
;;           (equal (eval term a)
;;                  (eval pat (eval-alist
;;                             (mv-nth 1 (simple-one-way-unify pat term alist))
;;                             a)))))
;; Unfortunately, A is free in this RHS.

;; Our solution is to look for evaluation alists in the clause and conjoin all
;; of them together.  Here is how we find evaluation alists:

(mutual-recursion
 (defun find-eval-alists-term (eval-fns x)
   ;; x is a term, eval-fns is a list (eval eval-lst eval-alist)
   (declare (xargs :guard (and (pseudo-termp x)
                               (symbol-listp eval-fns))
                   :verify-guards nil))
   (cond ((variablep x) nil)
         ((fquotep x) nil)
         ;; if any arg has evaluators, use those alists but ignore this one
         (t (let ((arg-envs (find-eval-alists-list eval-fns (fargs x))))
              (if (member-eq (ffn-symb x) eval-fns)
                  (let ((env (third x)))
                    (if (member-equal env arg-envs)
                        arg-envs
                      (cons env arg-envs)))
                arg-envs)))))
 (defun find-eval-alists-list (eval-fns x)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (symbol-listp eval-fns))))
   (if (atom x)
       nil
     (union-equal (find-eval-alists-term eval-fns (car x))
                  (find-eval-alists-list eval-fns (cdr x))))))

;; may verify the guards later

;; just like list-macro but produces a valid term, i.e. quotes the nil at the end
(defun list-term (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (cons 'cons
            (cons (car lst)
                  (cons (list-term (cdr lst)) nil)))
    ''nil))

;; The above is only used in a bind-free hyp, as follows:
(defun simple-one-way-unify-bind-free (rw-term eval-fns mfc state)
  (declare (xargs :mode :program :stobjs state)
           (ignorable state))
  (and (let ((lit (access rewrite-constant
                          (access metafunction-context mfc :rcnst)
                          :current-literal)))
         (and (consp lit)
              (eq (car lit) t) ;; negative literal, i.e. hyp
              (equal (cdr lit) rw-term)))
       (null (mfc-ancestors mfc))
       (let ((terms (find-eval-alists-list eval-fns (mfc-clause mfc))))
         (and terms ;; only do it if we found some candidates
              ;; if terms is (a b c d)
              ;; then (list-term terms) is
              ;; (cons a (cons b (cons c (cons d nil))))
              `((envs . ,(list-term terms)))))))

;;  The following is used in the
;; conclusion, expanding into a conjunction of equalities:
(defun unify-ev-simple-one-way-unify-equalities (pat term subst envs)
  (if (atom envs)
      t
    (and (equal (unify-ev term (car envs))
                (unify-ev pat (unify-ev-alist subst (car envs))))
         (unify-ev-simple-one-way-unify-equalities pat term subst (cdr envs)))))

(defund-nx unify-succeeded (pat term alist)
  (mv-nth 0 (simple-one-way-unify pat term alist)))

(defthm unify-succeeded-implies
  (implies (unify-succeeded pat term alist)
           (mv-nth 0 (simple-one-way-unify pat term alist)))
  :hints(("Goal" :in-theory (enable unify-succeeded)))
  :rule-classes (:rewrite :forward-chaining))

(defund-nx unify-lst-succeeded (pat term alist)
  (mv-nth 0 (simple-one-way-unify-lst pat term alist)))

(defthm unify-lst-succeeded-implies
  (implies (unify-lst-succeeded pat term alist)
           (mv-nth 0 (simple-one-way-unify-lst pat term alist)))
  :hints(("Goal" :in-theory (enable unify-lst-succeeded)))
  :rule-classes (:rewrite :forward-chaining))

(defthm simple-one-way-unify-usage
  (mv-let (ok subst)
    (simple-one-way-unify pat term alist)
    (implies (and (bind-free (simple-one-way-unify-bind-free
                              `(mv-nth '0 (simple-one-way-unify ,pat ,term ,alist))
                              '(unify-ev unify-ev-lst unify-ev-alist)
                              mfc state)
                             (envs))
                  (pseudo-termp term)
                  (pseudo-termp pat))
             (iff ok
                  (and (unify-succeeded pat term alist)
                       (unify-ev-simple-one-way-unify-equalities
                        pat term subst envs)))))
  :hints (("goal" :induct (len envs)
           :in-theory (enable unify-succeeded))))

;; rewrite rules for fast opening unify-ev-simple-one-way-unify-equalities
(defthm unify-ev-simple-one-way-unify-equalities-of-nil
  (equal (unify-ev-simple-one-way-unify-equalities pat term subst nil)
         t))

(defthm unify-ev-simple-one-way-unify-equalities-of-cons
  (equal (unify-ev-simple-one-way-unify-equalities pat term subst (cons a b))
         (and (equal (unify-ev term a)
                     (unify-ev pat (unify-ev-alist subst a)))
              (unify-ev-simple-one-way-unify-equalities pat term subst b))))

(in-theory (disable unify-ev-simple-one-way-unify-equalities))

;; same thing for unify-ev-lst:
(defun unify-ev-lst-simple-one-way-unify-equalities (pat term subst envs)
  (if (atom envs)
      t
    (and (equal (unify-ev-lst term (car envs))
                (unify-ev-lst pat (unify-ev-alist subst (car envs))))
         (unify-ev-lst-simple-one-way-unify-equalities pat term subst (cdr envs)))))



(defthm simple-one-way-unify-lst-usage
  (mv-let (ok subst)
    (simple-one-way-unify-lst pat term alist)
    (implies (and (bind-free (simple-one-way-unify-bind-free
                              `(mv-nth '0 (simple-one-way-unify-lst ,pat ,term ,alist))
                              '(unify-ev unify-ev-lst unify-ev-alist)
                              mfc state)
                             (envs))
                  (pseudo-term-listp term)
                  (pseudo-term-listp pat))
             (iff ok
                  (and (unify-lst-succeeded pat term alist)
                       (unify-ev-lst-simple-one-way-unify-equalities
                        pat term subst envs)))))
  :hints (("goal" :induct (len envs)
           :in-theory (enable unify-lst-succeeded))))

;; rewrite rules for fast opening unify-ev-lst-simple-one-way-unify-equalities
(defthm unify-ev-lst-simple-one-way-unify-equalities-of-nil
  (equal (unify-ev-lst-simple-one-way-unify-equalities pat term subst nil)
         t))

(defthm unify-ev-lst-simple-one-way-unify-equalities-of-cons
  (equal (unify-ev-lst-simple-one-way-unify-equalities pat term subst (cons a b))
         (and (equal (unify-ev-lst term a)
                     (unify-ev-lst pat (unify-ev-alist subst a)))
              (unify-ev-lst-simple-one-way-unify-equalities pat term subst b))))

(in-theory (disable unify-ev-lst-simple-one-way-unify-equalities))


;; (def-unify ev ev-alist) produces appropriate theorems for reasoning
;; about unification with the given evaluators.  Defines the ev-alist function
;; if needed.

(defconst *def-unify-template*
  '(encapsulate nil
     (local (in-theory (disable pseudo-termp default-car default-cdr)))
     (defun new-ev-alist (x al)
       (if (atom x)
           nil
         (cons (cons (caar x) (new-ev (cdar x) al))
               (new-ev-alist (cdr x) al))))

     (def-functional-instance
       simple-one-way-unify-correct-for-new-ev
       simple-one-way-unify-correct
       ((unify-ev new-ev)
        (unify-ev-lst new-ev-lst)
        (unify-ev-alist new-ev-alist))
       :hints ((and stable-under-simplificationp
                    '(:in-theory (enable new-ev-constraint-0)))))

     (def-functional-instance
       simple-one-way-unify-lst-correct-for-new-ev
       simple-one-way-unify-lst-correct
       ((unify-ev new-ev)
        (unify-ev-lst new-ev-lst)
        (unify-ev-alist new-ev-alist)))

     (def-functional-instance
       substitute-into-term-correct-for-new-ev
       substitute-into-term-correct
       ((unify-ev new-ev)
        (unify-ev-lst new-ev-lst)
        (unify-ev-alist new-ev-alist)))

     (def-functional-instance
       substitute-into-list-correct-for-new-ev
       substitute-into-list-correct
       ((unify-ev new-ev)
        (unify-ev-lst new-ev-lst)
        (unify-ev-alist new-ev-alist)))

     (defun new-ev-simple-one-way-unify-equalities (pat term subst envs)
       (if (atom envs)
           t
         (and (equal (new-ev term (car envs))
                     (new-ev pat (new-ev-alist subst (car envs))))
              (new-ev-simple-one-way-unify-equalities pat term subst (cdr envs)))))

     (defthm simple-one-way-unify-with-new-ev
       (mv-let (ok subst)
         (simple-one-way-unify pat term alist)
         (implies (and (bind-free (simple-one-way-unify-bind-free
                                   `(mv-nth '0 (simple-one-way-unify ,pat ,term ,alist))
                                   '(new-ev new-ev-lst new-ev-alist)
                                   mfc state)
                                  (envs))
                       (pseudo-termp term)
                       (pseudo-termp pat))
                  (iff ok
                       (and (unify-succeeded pat term alist)
                            (new-ev-simple-one-way-unify-equalities
                             pat term subst envs)))))
       :hints (("goal" :induct (len envs)
                :in-theory (enable unify-succeeded))))

     (defthm new-ev-simple-one-way-unify-equalities-of-nil
       (equal (new-ev-simple-one-way-unify-equalities pat term subst nil)
              t))
     
     (defthm new-ev-simple-one-way-unify-equalities-of-cons
       (equal (new-ev-simple-one-way-unify-equalities pat term subst (cons a b))
              (and (equal (new-ev term a)
                          (new-ev pat (new-ev-alist subst a)))
                   (new-ev-simple-one-way-unify-equalities pat term subst b))))

     (in-theory (disable new-ev-simple-one-way-unify-equalities))

     (defun new-ev-lst-simple-one-way-unify-equalities (pat term subst envs)
       (if (atom envs)
           t
         (and (equal (new-ev-lst term (car envs))
                     (new-ev-lst pat (new-ev-alist subst (car envs))))
              (new-ev-lst-simple-one-way-unify-equalities pat term subst (cdr envs)))))

     
     (defthm simple-one-way-unify-lst-with-new-ev
       (mv-let (ok subst)
         (simple-one-way-unify-lst pat term alist)
         (implies (and (bind-free (simple-one-way-unify-bind-free
                                   `(mv-nth '0 (simple-one-way-unify-lst ,pat ,term ,alist))
                                   '(new-ev new-ev-lst new-ev-alist)
                                   mfc state)
                                  (envs))
                       (pseudo-term-listp term)
                       (pseudo-term-listp pat))
                  (iff ok
                       (and (unify-lst-succeeded pat term alist)
                            (new-ev-lst-simple-one-way-unify-equalities
                             pat term subst envs)))))
       :hints (("goal" :induct (len envs)
                :in-theory (enable unify-lst-succeeded))))

     ;; rewrite rules for fast opening new-ev-lst-simple-one-way-unify-equalities
     (defthm new-ev-lst-simple-one-way-unify-equalities-of-nil
       (equal (new-ev-lst-simple-one-way-unify-equalities pat term subst nil)
              t))
     
     (defthm new-ev-lst-simple-one-way-unify-equalities-of-cons
       (equal (new-ev-lst-simple-one-way-unify-equalities pat term subst (cons a b))
              (and (equal (new-ev-lst term a)
                          (new-ev-lst pat (new-ev-alist subst a)))
                   (new-ev-lst-simple-one-way-unify-equalities pat term subst b))))

     (in-theory (disable new-ev-lst-simple-one-way-unify-equalities))

     (in-theory (disable simple-one-way-unify-correct-for-new-ev
                         simple-one-way-unify-lst-correct-for-new-ev))))

(defun def-unify-prefix-pair (new-ev ev sym)
  (let ((str (symbol-name sym)))
    (cons (intern$ (concatenate 'string (symbol-name new-ev) str) "ACL2")
          (intern-in-package-of-symbol
           (concatenate 'string (symbol-name ev) str) ev))))

(defun def-unify-prefix-pairs (new-ev ev syms)
  (if (atom syms)
      nil
    (cons (def-unify-prefix-pair new-ev ev (car syms))
          (def-unify-prefix-pairs new-ev ev (cdr syms)))))

(defun def-unify-suffix-pair (new-ev ev sym)
  (let ((str (symbol-name sym)))
    (cons (intern$ (concatenate 'string str (symbol-name new-ev)) "ACL2")
          (intern-in-package-of-symbol
           (concatenate 'string str (symbol-name ev)) ev))))

(defun def-unify-suffix-pairs (new-ev ev syms)
  (if (atom syms)
      nil
    (cons (def-unify-suffix-pair new-ev ev (car syms))
          (def-unify-suffix-pairs new-ev ev (cdr syms)))))
                
(defun def-unify-fn (ev ev-alist world)
  (b* ((ev-lst (find-ev-counterpart ev world))
       (constr-0 (ev-find-fncall-generic-rule ev world))
       (alist (append `((new-ev       . ,ev)
                        (new-ev-lst   . ,ev-lst)
                        (new-ev-alist . ,ev-alist)
                        (new-ev-constraint-0 . ,constr-0))
                      (def-unify-suffix-pairs
                        'new-ev ev
                        '(simple-one-way-unify-correct-for-
                          simple-one-way-unify-lst-correct-for-
                          substitute-into-term-correct-for-
                          substitute-into-list-correct-for-
                          simple-one-way-unify-with-
                          simple-one-way-unify-lst-with-))
                      (def-unify-prefix-pairs
                        'new-ev ev
                        '(-simple-one-way-unify-equalities
                          -simple-one-way-unify-equalities-of-nil
                          -simple-one-way-unify-equalities-of-cons))
                      (def-unify-prefix-pairs
                        'new-ev-lst ev-lst
                        '(-simple-one-way-unify-equalities
                          -simple-one-way-unify-equalities-of-nil
                          -simple-one-way-unify-equalities-of-cons)))))
    (sublis alist *def-unify-template*)))

(defmacro def-unify (ev ev-alist)
  `(make-event
    (def-unify-fn ',ev ',ev-alist (w state))))


(with-output :off :all :on (error) :gag-mode nil
  (local
   (progn
     (defevaluator my-ev my-ev-lst ((cons p q) (binary-+ f g) (len x)))
     (def-unify my-ev my-ev-alist)
     (defevaluator my-ev2 my-ev-lst2 ((if a b c) (cons g h) (binary-+ j l)))
     (def-unify my-ev2 my-ev-alist2))))



#||

;; Here's an example.  Say we have identity-functions id1, id2, id3 and we want
;; to write a meta-function that can pull a term out of a certain deep nesting
;; of these identities.  Here's how we might do that without case-match.

(defun id1 (x) x)
(defun id2 (x) x)
(defun id3 (x) x)

(defevaluator id-nest-ev id-nest-ev-lst
  ((id1 x) (id2 x) (id3 x)))

(defun id-nest-ev-alist (x al)
  (if (atom x)
      nil
    (cons (cons (caar x) (id-nest-ev (cdar x) al))
          (id-nest-ev-alist (cdr x) al))))

(defconst *nest-of-ids*
  '(id1 (id2 (id3 (id2 (id1 x))))))

(defthm nest-of-ids-result
  (equal (id-nest-ev *nest-of-ids* a)
         (cdr (assoc-equal 'x a))))

(defun nest-of-ids-meta (term)
  (mv-let (ok subst)
    (simple-one-way-unify *nest-of-ids* term nil)
    (if ok
        (cdr (assoc-equal 'x subst))
      term)))

(defthm assoc-equal-id-nest-ev-alist
  (equal (cdr (assoc-equal k (id-nest-ev-alist x a)))
         (id-nest-ev (cdr (assoc-equal k x)) a)))

(defthm simple-one-way-unify-usage-for-id-nest-ev 
  (mv-let (ok subst)
    (simple-one-way-unify template term alist)
    (implies (and ok
                  (pseudo-termp term)
                  (pseudo-termp template))
             (equal (id-nest-ev term a)
                    (id-nest-ev template (id-nest-ev-alist subst a)))))
  :hints (("goal" :use ((:functional-instance
                         simple-one-way-unify-usage
                         (unify-ev id-nest-ev)
                         (unify-ev-lst id-nest-ev-lst)
                         (unify-ev-alist id-nest-ev-alist))))
          (and stable-under-simplificationp
               '(:in-theory (enable id-nest-ev-constraint-0)))))

(defthm nest-of-ids-meta-correct
  (implies (pseudo-termp term)
           (equal (id-nest-ev term a)
                  (id-nest-ev (nest-of-ids-meta term) a))))





||#
