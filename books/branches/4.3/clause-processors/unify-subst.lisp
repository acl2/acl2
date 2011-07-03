
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
(include-book "tools/mv-nth" :dir :system)

(defevaluator unify-ev unify-ev-lst nil)

(local (defthm assoc-equal-consp
         (implies (alistp x)
                  (or (not (assoc-equal k x))
                      (consp (assoc-equal k x))))
         :rule-classes (:type-prescription
                        (:rewrite
                         :corollary (implies (and (alistp x)
                                                  (assoc-equal k x))
                                             (consp (assoc-equal k x)))))))

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

(defun unify-ev-alist (x al)
  (if (atom x)
      nil
    (cons (cons (caar x) (unify-ev (cdar x) al))
          (unify-ev-alist (cdr x) al))))

(defthm assoc-equal-unify-ev-alist
  (equal (cdr (assoc-equal k (unify-ev-alist x al)))
         (unify-ev (cdr (assoc-equal k x)) al)))

(defthm unify-ev-alist-pairlis$
  (equal (unify-ev-alist (pairlis$ a b) al)
         (pairlis$ a
                   (unify-ev-lst b al))))

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






(mutual-recursion
 (defun simple-one-way-unify (pat term alist)
   (declare (xargs :guard (and (pseudo-termp pat)
                               (pseudo-termp term)
                               (alistp alist))))
   (cond ((null pat)
          (if (eq term nil)
              (mv t alist)
            (mv nil alist)))
         ((atom pat)
          (let ((pair (assoc-equal pat alist)))
            (if pair
                (if (equal term (cdr pair))
                    (mv t alist)
                  (mv nil alist))
              (mv t (cons (cons pat term) alist)))))
         ((atom term) (mv nil alist))
         ((eq (car pat) 'quote)
          (if (equal pat term)
              (mv t alist)
            (mv nil alist)))
         ((equal (car pat) (car term))
          (simple-one-way-unify-lst (cdr pat) (cdr term) alist))
         (t (mv nil alist))))
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

(defthm-simple-one-way-unify-flag
  assoc-one-way-unify-lemma
  (simple-one-way-unify
   (implies (assoc-equal k alist)
            (equal (assoc-equal k (mv-nth 1 (simple-one-way-unify pat x alist)))
                   (assoc-equal k alist))))
  (simple-one-way-unify-lst
   (implies (assoc-equal k alist)
            (equal (assoc-equal k (mv-nth 1 (simple-one-way-unify-lst pat x alist)))
                   (assoc-equal k alist))))
  :hints (("goal" :induct (simple-one-way-unify-flag flag pat x alist))))



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

(defthm-simple-term-vars-flag
  substitute-into-one-way-unify-reduce-lemma
  (simple-term-vars
   (implies (all-keys-bound (simple-term-vars term) alist)
            (equal (substitute-into-term
                    term (mv-nth 1 (simple-one-way-unify pat x alist)))
                   (substitute-into-term term alist)))
   :name substitute-into-one-way-unify-reduce)
  (simple-term-vars-lst
   (implies (all-keys-bound (simple-term-vars-lst term) alist)
            (equal (substitute-into-list
                    term (mv-nth 1 (simple-one-way-unify pat x alist)))
                   (substitute-into-list term alist)))
   :name substitute-into-one-way-unify-reduce-list)
  :hints (("goal" :induct (simple-term-vars-flag flag term)
            :in-theory (enable subsetp-equal))))

(defthm-simple-term-vars-flag
  substitute-into-one-way-unify-lst-reduce-lemma
  (simple-term-vars
   (implies (all-keys-bound (simple-term-vars term) alist)
            (equal (substitute-into-term
                    term (mv-nth 1 (simple-one-way-unify-lst pat x alist)))
                   (substitute-into-term term alist)))
   :name substitute-into-one-way-unify-lst-reduce)
  (simple-term-vars-lst
   (implies (all-keys-bound (simple-term-vars-lst term) alist)
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



(defthm-simple-one-way-unify-flag
  simple-one-way-unify-correct-lemma
  (simple-one-way-unify
   (mv-let (okp subst)
     (simple-one-way-unify pat x alist)
     (implies (and (pseudo-termp x)
                   okp)
              (equal (substitute-into-term pat subst) x)))
   :name simple-one-way-unify-correct)
  (simple-one-way-unify-lst
   (mv-let (okp subst)
     (simple-one-way-unify-lst pat x alist)
     (implies (and (pseudo-term-listp x)
                   okp)
              (equal (substitute-into-list pat subst) x)))
   :name simple-one-way-unify-lst-correct)
  :hints (("goal" :induct (simple-one-way-unify-flag flag pat x alist))))
                 
(in-theory (disable simple-one-way-unify simple-one-way-unify-lst))

(defthm simple-one-way-unify-usage
  (mv-let (ok subst)
    (simple-one-way-unify template term alist)
    (implies (and ok
                  (pseudo-termp term)
                  (pseudo-termp template))
             (equal (unify-ev term a)
                    (unify-ev template (unify-ev-alist subst a)))))
  :hints (("goal" :use ((:instance substitute-into-term-correct
                                   (x template)
                                   (subst (mv-nth 1 (simple-one-way-unify
                                                     template term alist)))))
           :in-theory (disable substitute-into-term-correct))))

(defthm simple-one-way-unify-lst-usage
  (mv-let (ok subst)
    (simple-one-way-unify-lst template term alist)
    (implies (and ok
                  (pseudo-term-listp term)
                  (pseudo-term-listp template))
             (equal (unify-ev-lst term a)
                    (unify-ev-lst template (unify-ev-alist subst a)))))
  :hints (("goal" :use ((:instance substitute-into-list-correct
                                   (x template)
                                   (subst (mv-nth 1 (simple-one-way-unify-lst
                                                     template term alist)))))
           :in-theory (disable substitute-into-list-correct))))
    

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
