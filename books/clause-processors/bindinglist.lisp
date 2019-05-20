; Copyright (C) 2018 Centaur Technology
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

(include-book "unify-subst")
(include-book "std/alists/alist-fix" :dir :system)
(include-book "eval-alist-equiv")
(local (include-book "std/lists/sets" :dir :system))


(local (in-theory (enable assoc-is-hons-assoc-equal-when-key-nonnil)))


;; This was motivated by a desired feature of the GLMC clause processor.  We'd
;; like to take a list of B* bindings representing a nesting of lambdas and
;; translate them into some pseudo-term-based form that can be processed
;; logically.  This is tricky -- in general, B* binders can expand to IFs and
;; other forms besides just a nesting of lambdas.

;; The data structure we'll use is a list of pairs where each key is a list of
;; variables to be bound and each value is a list of terms to bind them to (of
;; equal lenth).  This can easily be converted into a lambda term but also
;; processed without doing so.

;; There are two possible interpretations for these sorts of binding lists.
;; The simple way is to take them as straightforward encodings of nestings of
;; lambdas.  That would suggest an evaluation scheme like this:

;; (defun my-ev-bindinglist (x a)
;;   ;; Produce the alist for evaluation of an inner body when evaluating the
;;   ;; bindinglist x under alist a.
;;   (if (atom x)
;;       a
;;     (ev-bindinglist (cdr x)
;;                     (pairlis$ (caar x)
;;                               (my-ev-lst (cdar x) a)))))

;; However, we're convinced this is the wrong approach.

;; Consider what happens when the body that you want to evaluate under the
;; bindings has free variables that are not present in the innermost binding.
;; Under this scheme, that variable will not be present in the alist when
;; evaluating that term.  But more likely what we want in that case is to get
;; some earlier binding of that variable, either from a previous binding in the
;; list or from the outside.  That suggests this evaluation scheme instead:

;; (defun my-ev-bindinglist (x a)
;;   ;; Produce the alist for evaluation of an inner body when evaluating the
;;   ;; bindinglist x under alist a.
;;   (if (atom x)
;;       a
;;     (ev-bindinglist (cdr x)
;;                     (append (pairlis$ (caar x)
;;                                       (my-ev-lst (cdar x) a))
;;                             a))))

;; This makes it somewhat more tricky to produce a lambda term from the
;; bindinglist -- we need to consider what variables are free at each step --
;; but it makes more sense from the perspective of translating something like
;; B* bindings.  It is also more flexible with respect to inner terms with
;; unpredictable free variables -- at each stage we only really need to list
;; bindings that are updated; variables bound to themselves are redundant.



(define bindinglist-p (x)
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (symbol-listp (caar x))      ;; lambda formals
         (pseudo-term-listp (cdar x)) ;; lambda actuals
         (equal (len (caar x)) (len (cdar x)))
         (bindinglist-p (cdr x))))
  ///
  (defthm symbol-listp-caar-of-bindinglist
    (implies (bindinglist-p x)
             (symbol-listp (caar x))))

  (defthm pseudo-term-listp-cdar-of-bindinglist
    (implies (bindinglist-p x)
             (pseudo-term-listp (cdar x))))

  (defthm len-cdar-of-bindinglist
    (implies (bindinglist-p x)
             (equal (len (cdar x))
                    (len (caar x)))))

  (defthm bindinglist-p-cdr-of-bindinglist
    (implies (bindinglist-p x)
             (bindinglist-p (cdr x))))

  (defthm consp-car-when-bindinglist-p
    (implies (bindinglist-p x)
             (iff (consp (car x))
                  (consp x))))

  (defthm bindinglist-p-of-cons
    (implies (and (consp a)
                  (symbol-listp (car a))
                  (pseudo-term-listp (cdr a))
                  (equal (len (car a)) (len (cdr a)))
                  (bindinglist-p b))
             (bindinglist-p (cons a b)))))


(defthm true-listp-of-unify-ev-lst
  (true-listp (unify-ev-lst x a))
  :hints (("Goal" :induct (len x)))
  :rule-classes :type-prescription)


;; (local (defthm assoc-of-alist-fix
;;          (implies k
;;                   (equal (assoc k (alist-fix x))
;;                          (assoc k x)))))

;; (local (defthm assoc-of-append
;;          (implies k
;;                   (equal (assoc k (append a b))
;;                          (or (assoc k a) (assoc k b))))))

(local (in-theory (enable unify-ev-of-nonsymbol-atom)))

(defines unify-ev-ind
  :flag-local nil
  (define unify-ev-ind (x)
    :flag term
    (cond ((not x) t)
          ((symbolp x) t)
          ((atom x) t)
          ((eq (car x) 'quote) nil)
          (t (unify-ev-lst-of-alist-fix-ind (cdr x)))))
  (define unify-ev-lst-of-alist-fix-ind (x)
    :flag list
    (if (atom x)
        t
      (list (unify-ev-ind (car x))
            (unify-ev-lst-of-alist-fix-ind (cdr x)))))
  ///
  (defthm-unify-ev-ind-flag
    (defthm unify-ev-of-alist-fix
      (equal (unify-ev x (alist-fix a))
             (unify-ev x a))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable unify-ev-of-fncall-args))))
      :flag term)
    (defthm unify-ev-lst-of-alist-fix
      (equal (unify-ev-lst x (alist-fix a))
             (unify-ev-lst x a))
      :flag list))

  (defthm-unify-ev-ind-flag
    (defthm unify-ev-of-append-alist-fix
      (equal (unify-ev x (append (alist-fix a) a))
             (unify-ev x a))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable unify-ev-of-fncall-args))))
      :flag term)
    (defthm unify-ev-lst-of-append-alist-fix
      (equal (unify-ev-lst x (append (alist-fix a) a))
             (unify-ev-lst x a))
      :flag list)))

(local (defthm true-listp-when-symbol-listp
         (implies (symbol-listp x)
                  (true-listp x))))

(local (defthm true-listp-when-pseudo-term-listp
         (implies (pseudo-term-listp x)
                  (true-listp x))))

(local (defthm alistp-of-pairlis$
         (alistp (pairlis$ a b))))

(local (defthm alistp-of-append
         (implies (and (alistp a) (alistp b))
                  (alistp (append a b)))))

(define unify-ev-bindinglist ((x bindinglist-p) (a alistp))
  ;; Returns the alist for evaluating a body term nested inside all the
  ;; bindings.
  :returns (final-alist alistp)
  (b* (((when (atom x)) (alist-fix a))
       ((cons formals actuals) (car x))
       (new-bindings (pairlis$ formals (unify-ev-lst actuals a))))
    (unify-ev-bindinglist (cdr x) (append new-bindings a))))

(define lambda-remove-redundant-bindings ((formals symbol-listp)
                                          (actuals pseudo-term-listp)
                                          (deleted-formals symbol-listp))
  :returns (mv (new-formals symbol-listp :hyp (symbol-listp formals))
               (new-actuals pseudo-term-listp  :hyp (pseudo-term-listp actuals)))
  :guard (eql (len formals) (len actuals))
  (cond ((atom formals) (mv nil nil))
        ((eq (car formals) (car actuals))
         (lambda-remove-redundant-bindings (cdr formals) (cdr actuals)
                                           (cons (car formals) deleted-formals)))
        ((member (car formals) deleted-formals)
         (lambda-remove-redundant-bindings (cdr formals) (cdr actuals) deleted-formals))
        (t
         (b* (((mv rest-f rest-a)
               (lambda-remove-redundant-bindings (cdr formals) (cdr actuals) deleted-formals)))
           (mv (cons (car formals) rest-f)
               (cons (car actuals) rest-a)))))
  ///
  (defret len-of-lambda-remove-redundant-bindings
    (equal (len new-actuals) (len new-formals)))

  (defret lookup-in-lambda-remove-redundant-bindings
    (equal (hons-assoc-equal k (pairlis$ new-formals new-actuals))
           (and (not (member k deleted-formals))
                (let ((look (hons-assoc-equal k (pairlis$ formals actuals))))
                  (and (not (equal (cdr look) k))
                       look)))))

  (defret not-member-when-deleted-formal
    (implies (member v deleted-formals)
             (not (member v new-formals))))

  (defret member-of-new-formals
    (implies (and (member v formals)
                  (not (member v deleted-formals)))
             (iff (member v new-formals)
                  (not (equal (cdr (hons-assoc-equal v (pairlis$ formals actuals))) v)))))

  ;; (defret lookup-in-lambda-remove-redundant-bindings-eval
  ;;   (equal (hons-assoc-equal k (pairlis$ new-formals (unify-ev-lst new-actuals a)))
  ;;          (and (not (member k deleted-formals))
  ;;               (let ((look (hons-assoc-equal k (pairlis$ formals actuals))))
  ;;                 (and look
  ;;                      (not (equal (cdr look) k))
  ;;                      (cons k (unify-ev (cdr look) a)))))))
  )





(local (defthm symbol-listp-of-set-diff
         (implies (symbol-listp x)
                  (symbol-listp (set-difference-eq x y)))
         :hints(("Goal" :in-theory (enable set-difference-eq)))))


(local (defthm symbol-listp-of-append
         (implies (and (symbol-listp a)
                       (symbol-listp b))
                  (symbol-listp (append a b)))))


;; (local (defthm pseudo-term-listp-of-append
;;          (implies (and (pseudo-term-listp a)
;;                        (pseudo-term-listp b))
;;                   (pseudo-term-listp (append a b)))))

(local (defthm pseudo-term-listp-of-repeat
         (implies (pseudo-termp x)
                  (pseudo-term-listp (repeat n x)))
         :hints(("Goal" :in-theory (enable repeat)))))

(local (defthm len-of-repeat
         (equal (len (repeat n x))
                (nfix n))
         :hints(("Goal" :in-theory (enable repeat)))))

(local (defthm unify-ev-lst-of-append
         (Equal (unify-ev-lst (append x y) a)
                (append (unify-ev-lst x a)
                        (unify-ev-lst y a)))))

(local (defthm unify-ev-lst-of-repeat
         (Equal (unify-ev-lst (repeat n x) a)
                (repeat n (unify-ev x a)))
         :hints(("Goal" :in-theory (enable repeat)))))

(local (defthm len-of-unify-ev-lst
           (equal (len (unify-ev-lst x a))
                  (len x))))

(local (defthm set-difference-of-append
         (equal (set-difference-eq (append a b) c)
                (append (set-difference-eq a c)
                        (set-difference-eq b c)))))

(local (include-book "std/alists/hons-assoc-equal" :dir :system))

(local (defthm hons-assoc-equal-of-pairlis-under-iff
         (iff (hons-assoc-equal k (pairlis$ keys vals))
              (member k keys))))





(define lambda-nest-to-bindinglist ((x pseudo-termp))
  :returns (mv (bindings bindinglist-p :hyp :guard)
               (body pseudo-termp :hyp :guard))
  (b* (((when (or (atom x)
                  (eq (car x) 'quote)
                  (mbe :logic (atom (car x))
                       :exec (symbolp (car x)))))
        (mv nil x))
       ((cons (list & formals body1) actuals) x)
       (free-vars (simple-free-vars body1 formals))
       ((mv reduced-formals reduced-actuals)
        (lambda-remove-redundant-bindings formals actuals nil))
       (final-formals (append free-vars reduced-formals))
       (final-actuals (append (repeat (len free-vars) ''nil) reduced-actuals))
       ((mv rest body) (lambda-nest-to-bindinglist body1)))
    (mv (cons (cons final-formals final-actuals) rest)
        body))
  ///

  (local (defthm pairlis$-of-append
           (implies (equal (len x1) (len x2))
                    (equal (pairlis$ (append x1 y1) (append x2 y2))
                           (append (pairlis$ x1 x2)
                                   (pairlis$ y1 y2))))))

  (local (defthm cdr-hons-assoc-equal-of-pairlis-repeat-nil
           (equal (cdr (hons-assoc-equal k (pairlis$ keys (repeat (len keys) nil))))
                  nil)
           :hints(("Goal" :in-theory (enable pairlis$ repeat)))))

  (local (Defthm hons-assoc-equal-of-pairlis$-unify-ev-lst
           (equal (hons-assoc-equal x (pairlis$ keys (unify-ev-lst vals a)))
                  (let ((look (hons-assoc-equal x (pairlis$ keys vals))))
                    (and look
                         (cons x (unify-ev (cdr look) a)))))))

  (local (defthm intersectp-when-member-both
           (implies (and (member x a)
                         (member x b))
                    (intersectp a b))
           :hints(("Goal" :in-theory (enable intersectp)))))


  (local
   (defthm-unify-ev-ind-flag
     (defthm unify-ev-of-lambda-nest-fixup
       (b* (((mv reduced-formals reduced-actuals)
             (lambda-remove-redundant-bindings formals actuals nil))
            (orig-alist (pairlis$ formals (unify-ev-lst actuals a)))
            (new-alist (append (pairlis$ free-vars (repeat (len free-vars) nil))
                               (pairlis$ reduced-formals (unify-ev-lst reduced-actuals a))
                               a)))
         (implies (and (double-rewrite (not (intersectp free-vars formals)))
                       (double-rewrite (subsetp (set-difference-eq (simple-term-vars x) formals) free-vars)))
                (equal (unify-ev x new-alist)
                       (unify-ev x orig-alist))))
       :hints ((and stable-under-simplificationp
                    '(:in-theory (enable unify-ev-of-fncall-args)
                      :expand ((simple-term-vars x)))))
       :flag term)
     (defthm unify-ev-lst-of-lambda-nest-fixup
       (b* (((mv reduced-formals reduced-actuals)
             (lambda-remove-redundant-bindings formals actuals nil))
            (orig-alist (pairlis$ formals (unify-ev-lst actuals a)))
            (new-alist (append (pairlis$ free-vars (repeat (len free-vars) nil))
                               (pairlis$ reduced-formals (unify-ev-lst reduced-actuals a))
                               a)))
         (implies (and (double-rewrite (not (intersectp free-vars formals)))
                       (double-rewrite (subsetp (set-difference-eq (simple-term-vars-lst x) formals) free-vars))) ;; argh
                  (equal (unify-ev-lst x new-alist)
                         (unify-ev-lst x orig-alist))))
       :hints ('(:expand ((simple-term-vars-lst x))))
       :flag list)))

  (local (Defthm intersectp-of-nil
           (not (intersectp nil a))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (defthm intersectp-of-cons
           (iff (intersectp a (cons b c))
                (or (member b a) (intersectp a c)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (defthm not-intersectp-of-set-diff
           (not (intersectp (set-difference-eq a b) b))
           :hints(("Goal" :in-theory (enable intersectp)))))


  (local (defun lambda-nest-to-bindinglist-correct-ind (x a)
           (b* (((when (or (atom x)
                           (eq (car x) 'quote)
                           (mbe :logic (atom (car x))
                                :exec (symbolp (car x)))))
                 a)
                ((cons (list & formals body1) actuals) x)
                (free-vars (simple-free-vars body1 formals))
                ((mv reduced-formals reduced-actuals)
                 (lambda-remove-redundant-bindings formals actuals nil))
                (final-formals (append free-vars reduced-formals))
                (final-actuals (append (repeat (len free-vars) ''nil) reduced-actuals))
                (new-a (append (pairlis$ final-formals (unify-ev-lst final-actuals a)) a)))
             (lambda-nest-to-bindinglist-correct-ind body1 new-a))))

  (defret lambda-nest-to-bindinglist-correct
    (equal (unify-ev body (unify-ev-bindinglist bindings a))
           (unify-ev x a))
    :hints (("goal" :induct (lambda-nest-to-bindinglist-correct-ind x a)
             :expand (<call>)
             :in-theory (enable unify-ev-bindinglist)))))

(local (defthm symbol-listp-of-union
         (implies (and (symbol-listp x)
                       (symbol-listp y))
                  (symbol-listp (union-eq x y)))))


(local (include-book "std/lists/take" :dir :system))
(local (in-theory (disable take)))

(define bindinglist-free-vars ((x bindinglist-p))
  :verify-guards nil
  :returns (vars symbol-listp)
  (if (atom x)
      nil
    (mbe :logic (union-eq (simple-term-vars-lst (take (len (caar x)) (cdar x)))
                          (set-difference-eq (bindinglist-free-vars (cdr x))
                                             (caar x)))
         :exec (acl2::simple-term-vars-lst-acc (cdar x)
                                               (set-difference-eq (bindinglist-free-vars (cdr x))
                                                                  (caar x)))))
  ///
  (verify-guards bindinglist-free-vars)

  (defret nil-not-member-of-bindinglist-free-vars
    (not (member nil (bindinglist-free-vars x)))))


(local (defthm true-listp-of-union
         (equal (true-listp (union-equal x y))
                (true-listp y))))

(define bindinglist-bound-vars ((x bindinglist-p))
  :returns (final-vars symbol-listp :hyp :guard)
  :verify-guards nil
  (if (atom x)
      nil
    (union-eq (caar x) (bindinglist-bound-vars (cdr x))))
  ///
  (defret true-listp-of-bindinglist-bound-vars
    (true-listp final-vars)
    :rule-classes :type-prescription)

  (verify-guards bindinglist-bound-vars))


(defthm unify-ev-when-eval-alists-agree
  (implies (and (eval-alists-agree vars a1 a2)
                (subsetp (simple-term-vars x) vars))
           (equal (unify-ev x a1)
                  (unify-ev x a2)))
  :hints (("goal" :use ((:functional-instance base-ev-when-eval-alists-agree
                         (base-ev unify-ev) (base-ev-list unify-ev-lst)))
           :in-theory (enable unify-ev-of-fncall-args))))

(defthm unify-ev-lst-when-eval-alists-agree
  (implies (and (eval-alists-agree vars a1 a2)
                (subsetp (simple-term-vars-lst x) vars))
           (equal (unify-ev-lst x a1)
                  (unify-ev-lst x a2)))
  :hints (("goal" :use ((:functional-instance base-ev-list-when-eval-alists-agree
                         (base-ev unify-ev) (base-ev-list unify-ev-lst))))))






(local (defun unify-ev-bindinglist-when-alists-agree-on-free-vars-ind (x a b)
         (if (atom x)
             (list a b)
           (b* (((cons formals actuals) (car x))
                (new-part (pairlis$ formals (unify-ev-lst actuals a))))
             (unify-ev-bindinglist-when-alists-agree-on-free-vars-ind
              (cdr x)
              (append new-part a)
              (append new-part b))))))

(local (defthm member-union
         (iff (member k (union-eq a b))
              (or (member k a) (member k b)))))

(local
 (defthm eval-alists-agree-of-union
   (iff (eval-alists-agree (union-eq x y) a b)
        (and (eval-alists-agree x a b)
             (eval-alists-agree y a b)))
   :hints(("Goal" :in-theory (enable eval-alists-agree union-eq
                                     lookup-when-eval-alists-agree)))))

(local (defthm set-difference-nil
         (implies (true-listp x)
                  (equal (set-difference-equal x nil) x))))

(local (defthm pairlis-of-unify-ev-lst-when-eval-alists-agree-of-take
         (implies (eval-alists-agree (simple-term-vars-lst (take (len vars) vals)) a b)
                  (equal (pairlis$ vars (unify-ev-lst vals a))
                         (pairlis$ vars (unify-ev-lst vals b))))
         :hints(("Goal" :induct (pairlis$ vars vals)
                 :in-theory (enable pairlis$ acl2::take simple-term-vars-lst)))))


(defthm unify-ev-bindinglist-when-eval-alists-agree-on-free-vars
  (implies (and (eval-alists-agree (bindinglist-free-vars x) a b)
                (eval-alists-agree (set-difference-eq (simple-term-vars body)
                                                 (bindinglist-bound-vars x)) a b))
           (equal (unify-ev body (unify-ev-bindinglist x a))
                  (unify-ev body (unify-ev-bindinglist x b))))
  :hints(("Goal" :in-theory (enable unify-ev-bindinglist
                                    bindinglist-free-vars
                                    bindinglist-bound-vars
                                    eval-alists-agree-by-bad-guy
                                    lookup-when-eval-alists-agree)
          :induct (unify-ev-bindinglist-when-alists-agree-on-free-vars-ind x a b)
          :expand ((:free (a) (unify-ev-bindinglist x a))))))

;; (local (defthm pseudo-term-listp-of-set-diff
;;          (implies (pseudo-term-listp x)
;;                   (pseudo-term-listp (set-difference-eq x y)))))

;; (local (defthm pseudo-term-listp-of-union
;;          (implies (and (pseudo-term-listp x)
;;                        (pseudo-term-listp y))
;;                   (pseudo-term-listp (union-eq x y)))))

(local (defthm pseudo-term-listp-when-symbol-listp
         (implies (symbol-listp x)
                  (pseudo-term-listp x))))


(local (defcong set-equiv equal (eval-alists-agree keys x y) 1
         :hints (("goal" :cases ((eval-alists-agree keys x y)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable eval-alists-agree-by-bad-guy
                                           lookup-when-eval-alists-agree))))))

(local (defthm eval-alists-agree-of-append
         (iff (eval-alists-agree (append a b) x y)
              (and (eval-alists-agree a x y)
                   (eval-alists-agree b x y)))
         :hints(("Goal" :in-theory (enable eval-alists-agree)))))


(define bindinglist-to-lambda-nest ((x bindinglist-p)
                                    (body pseudo-termp))
  :returns (term pseudo-termp :hyp :guard)
  :verify-guards nil
  (b* (((when (atom x)) body)
       ((cons formals actuals) (car x))
       (actuals (mbe :logic (take (len formals) actuals)
                     :exec actuals))
       (free-vars (union-eq (bindinglist-free-vars (cdr x))
                            (set-difference-eq (simple-term-vars body)
                                               (bindinglist-bound-vars (cdr x)))))
       (missing-vars (set-difference-eq free-vars formals))
       (rest-body (bindinglist-to-lambda-nest (cdr x) body))
       (full-formals (append formals missing-vars))
       (full-actuals (append actuals missing-vars)))
    `((lambda ,full-formals ,rest-body) . ,full-actuals))
  ///
  (local (defthm pairlis$-of-append
           (implies (equal (len x1) (len x2))
                    (equal (pairlis$ (append x1 y1) (append x2 y2))
                           (append (pairlis$ x1 x2)
                                   (pairlis$ y1 y2))))))

  (local (defthm simple-term-vars-lst-of-append
           (set-equiv (simple-term-vars-lst (append a b))
                      (append (simple-term-vars-lst a)
                              (simple-term-vars-lst b)))
           :hints(("Goal" :in-theory (enable simple-term-vars-lst)))))

  (local (defthm simple-term-vars-lst-of-symbol-list
           (implies (symbol-listp x)
                    (set-equiv (simple-term-vars-lst x)
                               (remove nil x)))
           :hints(("Goal" :in-theory (enable simple-term-vars-lst simple-term-vars)))))

  (local (defthm remove-equal-when-not-member
           (implies (not (member k x))
                    (set-equiv (remove-equal k x) x))))

  (local (defthm set-difference-of-set-difference
           (equal (set-difference-eq (set-difference-eq x y) z)
                  (set-difference-eq x (append y z)))
           :hints(("Goal" :in-theory (enable set-difference-eq)))))

  (local (defthmd set-difference-eq-when-set-equiv-append
           (implies (set-equiv a (append b c))
                    (set-equiv (set-difference-eq a d)
                               (append (set-difference-eq b d)
                                       (set-difference-eq c d))))
           :hints(("Goal" :in-theory (enable set-difference-eq)))))

  (defret free-vars-of-bindinglist-to-lambda-nest
    (set-equiv (simple-term-vars term)
               (union-eq (bindinglist-free-vars x)
                         (set-difference-eq (simple-term-vars body)
                                            (bindinglist-bound-vars x))))
    :hints(("Goal" :in-theory (enable simple-term-vars
                                      bindinglist-free-vars
                                      bindinglist-bound-vars)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable set-difference-eq-when-set-equiv-append)))))

  (local (defthm lookup-in-pairlis$-vars
           (equal (hons-assoc-equal k (pairlis$ vars (unify-ev-lst vars a)))
                  (and (member k vars)
                       (cons k (unify-ev k a))))
           :hints(("Goal" :in-theory (enable pairlis$)
                   :induct (len vars)))))

  (local (defthm unify-ev-when-member-of-nonnil-symbol-list
           (implies (and (member k vars)
                         (symbol-listp vars)
                         (not (member nil vars)))
                    (equal (unify-ev k a)
                           (cdr (hons-assoc-equal k a))))))

  (local (defthm cons-cdr-hons-assoc-equal
           (iff (equal (cons k (cdr (hons-assoc-equal k a)))
                       (hons-assoc-equal k a))
                (hons-assoc-equal k a))))


  (local (defthm lookup-in-pairlis$-append-not-first
           (implies (and (not (member v vars))
                         (equal (len vars) (len vals)))
                    (equal (hons-assoc-equal v (pairlis$ (append vars vars1) (append vals vals1)))
                           (hons-assoc-equal v (pairlis$ vars1 vals1))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal pairlis$)))))

  ;; (local (in-theory (disable alists-agree-by-witness)))

  (local (defthm pairlis$-of-unify-ev-lst-take
           (equal (pairlis$ vars (unify-ev-lst (take (len vars) vals) a))
                  (pairlis$ vars (unify-ev-lst vals a)))
           :hints(("Goal" :in-theory (enable pairlis$ acl2::take)
                   :induct (pairlis$ vars vals)))))

  (defret bindinglist-to-lambda-nest-correct
    (equal (unify-ev term a)
           (unify-ev body (unify-ev-bindinglist x a)))
    :hints (("goal" :induct (unify-ev-bindinglist x a)
             :in-theory (e/d (unify-ev-bindinglist
                                eval-alists-agree-by-bad-guy)
                             (unify-ev-when-eval-alists-agree)))
            (acl2::use-termhint
             (b* (((cons formals actuals) (car x))
                  (actuals (take (len formals) actuals))
                  (free-vars (union-eq (bindinglist-free-vars (cdr x))
                                       (set-difference-eq (simple-term-vars body)
                                                          (bindinglist-bound-vars (cdr x)))))
                  (missing-vars (set-difference-eq free-vars formals))
                  (rest-body (bindinglist-to-lambda-nest (cdr x) body))
                  (full-formals (append formals missing-vars))
                  (full-actuals (append actuals missing-vars))
                  (impl-alist (pairlis$ full-formals (unify-ev-lst full-actuals a)))
                  (spec-alist (append (pairlis$ formals (unify-ev-lst actuals a)) a)))
               `'(:use ((:instance unify-ev-when-eval-alists-agree
                         (x ,(hq rest-body))
                         (vars (simple-term-vars ,(hq rest-body)))
                         (a1 ,(hq impl-alist))
                         (a2  ,(hq spec-alist))))))))))


(define bindinglist-to-lambda-nest-aux ((x bindinglist-p)
                                        (body pseudo-termp))
  :returns (mv (term)
               (free-vars))
  (b* (((when (atom x)) (mv body (simple-term-vars body)))
       ((mv rest-body free-vars)
        (bindinglist-to-lambda-nest-aux (cdr x) body))
       ((cons formals actuals) (car x))
       (actuals (mbe :logic (take (len formals) actuals)
                     :exec actuals))
       (missing-vars (set-difference-eq free-vars formals))
       (full-formals (append formals missing-vars))
       (full-actuals (append actuals missing-vars))
       (new-free-vars (union-eq (simple-term-vars-lst actuals)
                                missing-vars)))
    (mv `((lambda ,full-formals ,rest-body) . ,full-actuals)
        new-free-vars))
  ///
  (local (defthm union-associative
           (equal (union-eq (union-eq x y) z)
                  (union-eq x (union-eq y z)))
           :hints(("Goal" :in-theory (enable union-eq)))))

  (local (defthm set-difference-of-union
           (equal (set-difference-eq (union-eq x y) z)
                  (union-eq (set-difference-eq x z)
                            (set-difference-eq y z)))
           :hints(("Goal" :in-theory (enable union-eq set-difference-eq)))))

  (local (defthm set-diff-of-equal-to-union
           (implies (equal xy (union-equal x y))
                    (equal (set-difference-eq xy z)
                           (union-eq (set-difference-eq x z)
                            (set-difference-eq y z))))))

  (local (defthm set-diff-of-set-diff
           (equal (set-difference-eq (set-difference-eq x y) z)
                  (set-difference-eq x (append y z)))
           :hints(("Goal" :in-theory (enable set-difference-eq)))))

  (defret bindinglist-to-lambda-nest-aux-free-vars-elim
    (equal free-vars
           (union-eq (bindinglist-free-vars x)
                     (set-difference-eq (simple-term-vars body)
                                        (bindinglist-bound-vars x))))
    :hints(("Goal" :in-theory (enable bindinglist-free-vars
                                      bindinglist-bound-vars))))

  (defret bindinglist-to-lambda-nest-aux-elim
    (equal term (bindinglist-to-lambda-nest x body))
    :hints(("Goal" :in-theory (enable bindinglist-to-lambda-nest)))))

(define bindinglist-to-lambda-nest-exec ((x bindinglist-p)
                                         (body pseudo-termp))
  :enabled t
  :guard-hints (("goal" :in-theory (enable bindinglist-to-lambda-nest)))
  (mbe :logic (bindinglist-to-lambda-nest x body)
       :exec (b* (((when (atom x)) body)
                  ((mv rest-body free-vars)
                   (bindinglist-to-lambda-nest-aux (cdr x) body))
                  ((cons formals actuals) (car x))
                  (actuals (mbe :logic (take (len formals) actuals)
                                :exec actuals))
                  (missing-vars (set-difference-eq free-vars formals))
                  (full-formals (append formals missing-vars))
                  (full-actuals (append actuals missing-vars)))
               `((lambda ,full-formals ,rest-body) . ,full-actuals))))


(defun translate-cmp-ignore-ok (x stobjs-out logic-modep known-stobjs ctx w state-vars)
  (declare (xargs :mode :program))
  ;; We override ignore-ok so that we can translate a list of B* binders
  ;; without giving a body that includes all the bound vars.
  (let ((w (putprop 'acl2-defaults-table 'table-alist
                    (put-assoc-equal-fast :ignore-ok t (table-alist 'acl2-defaults-table w))
                    w)))
    (translate-cmp x stobjs-out logic-modep known-stobjs ctx w state-vars)))

(define b*-binders-to-bindinglist ((x "list of bstar binders")
                                   wrld)
  :mode :program
  :returns (mv err bindinglist)
  (b* ((state-vars (default-state-vars nil))
       (ctx 'b*-binders-to-bindinglist)
       (marker-term `'(this is the b*-binder-to-bindinglist marker for . ,x))
       (bstar-term `(b* ,x ,marker-term))
       ((mv err translated-bstar-term)
        (translate-cmp-ignore-ok bstar-term
                                 t ;; stobjs-out -- logical use only
                                 t ;; logic-modep -- do the check, maybe not totally necessary
                                 nil ;; known-stobjs
                                 ctx wrld state-vars))
       ((when err)
        (mv (msg "In ~x0, error translating bstar term: ~@1~%" err translated-bstar-term) nil))
       ((mv bindings body) (lambda-nest-to-bindinglist translated-bstar-term))
       ((unless (equal body marker-term))
        (mv (msg "In ~x0, inner lambda body was not the expected marker term ~
                  but instead: ~x1~%This likely means you are using an ~
                  unsupported B* binder.  Binders should only create ~
                  LET/LET*/MV-LET bindings."
                 ctx body)
            nil)))
    (mv nil bindings)))


(make-event
 ;; assert-event doesn't work here b/c of program mode
 (b* (((mv err bindings)
       (b*-binders-to-bindinglist '((a (cons 'b st))
                                    ((mv c d) (mv (list a 'q) (nth n a))))
                                  (w state))))
   (if (and (equal err nil)
            (equal bindings
                   '(((A) (CONS 'B ST))
                     ((MV)
                      (CONS (CONS A (CONS 'Q 'NIL))
                            (CONS (NTH N A) 'NIL)))
                     ((C D) (MV-NTH '0 MV) (MV-NTH '1 MV))))
            (bindinglist-p bindings))
       '(value-triple :ok)
     (er hard? 'check-b*-binderst-to-bindinglist
         "Check failed!~%"))))
