; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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

(in-package "CMR")

(include-book "term-vars")
(include-book "std/alists/alist-fix" :dir :system)
(include-book "clause-processors/eval-alist-equiv" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "assoc-is-hons-assoc"))



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

(local (std::add-default-post-define-hook :fix))

(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (symbol-listp x))))

(define remove-non-pseudo-vars (x)
  (if (atom x)
      nil
    (if (pseudo-var-p (car x))
        (cons (car x) (remove-non-pseudo-vars (cdr x)))
      (remove-non-pseudo-vars (cdr x))))
  ///
  (defthm pseudo-var-list-p-of-remove-non-pseudo-vars
    (pseudo-var-list-p (remove-non-pseudo-vars x)))

  (defthm remove-non-pseudo-vars-when-pseudo-var-list-p
    (implies (pseudo-var-list-p x)
             (equal (remove-non-pseudo-vars x) x))))

(define remove-corresp-non-pseudo-vars (x (y true-listp))
  (if (atom x)
      nil
    (if (pseudo-var-p (car x))
        (cons (car y)
              (remove-corresp-non-pseudo-vars (cdr x) (cdr y)))
      (remove-corresp-non-pseudo-vars (cdr x) (cdr y))))
  ///
  
  (defthm pseudo-term-listp-of-remove-corresp-non-pseudo-vars
    (implies (pseudo-term-listp y)
             (pseudo-term-listp (remove-corresp-non-pseudo-vars x y))))

  (defthm len-of-remove-corresp-non-pseudo-vars
    (equal (len (remove-corresp-non-pseudo-vars x y))
           (len (remove-non-pseudo-vars x)))
    :hints(("Goal" :in-theory (enable remove-non-pseudo-vars))))

  (defthm remove-corresp-non-pseudo-vars-when-pseudo-var-list-p
    (implies (pseudo-var-list-p x)
             (equal (remove-corresp-non-pseudo-vars x y)
                    (take (len x) y)))
    :hints(("Goal" :in-theory (enable take))))

  (defthm lookup-in-remove-non-pseudo-vars-alist
    (implies (pseudo-var-p x)
             (equal (hons-assoc-equal x (pairlis$ (remove-non-pseudo-vars formals)
                                                  (remove-corresp-non-pseudo-vars formals actuals)))
                    (hons-assoc-equal x (pairlis$ formals actuals))))
    :hints(("Goal" :in-theory (enable remove-non-pseudo-vars)))))



(defthm true-listp-when-pseudo-term-listp
  (implies (pseudo-term-listp x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(define binding-p (x)
  (and (consp x)
       (pseudo-var-list-p (car x))
       (pseudo-term-listp (cdr x))
       (equal (len (car x)) (len (cdr x))))
  ///
  (defthm binding-p-compound-recognizer
    (implies (binding-p x)
             (and (consp x)
                  (true-listp x)))
    :rule-classes :compound-recognizer)

  (define binding-fix ((x binding-p))
    :returns (new-x binding-p :rule-classes (:rewrite (:type-prescription :typed-term new-x)))
    :inline t
    (mbe :logic (let* ((formals (car x))
                       (args (pseudo-term-list-fix (cdr x))))
                  (cons (remove-non-pseudo-vars formals)
                        (remove-corresp-non-pseudo-vars formals args)))
         :exec x)
    ///
    (defthm binding-fix-when-binding-p
      (implies (binding-p x)
               (equal (binding-fix x) x)))

    (deffixtype binding :pred binding-p :fix binding-fix :equiv binding-equiv :define t)

    (deffixequiv binding-fix)))

(define binding->formals ((x binding-p))
  :inline t
  :returns (formals pseudo-var-list-p :rule-classes (:rewrite (:type-prescription :typed-term formals))
                    :hints(("Goal" :in-theory (enable binding-fix))))
  (car (binding-fix x))
  ///
  (deffixequiv binding->formals))

(define binding->args ((x binding-p))
  :inline t
  :returns (args pseudo-term-listp :rule-classes (:rewrite (:type-prescription :typed-term args))
                    :hints(("Goal" :in-theory (enable binding-fix))))
  (cdr (binding-fix x))
  ///
  (defthm len-of-binding->args
    (equal (len (binding->args x))
           (len (binding->formals x)))
    :hints(("Goal" :in-theory (enable binding->formals binding-fix))))

  (deffixequiv binding->args))

(define binding ((formals pseudo-var-list-p)
                 (args pseudo-term-listp))
  :guard (equal (len formals) (len args))
  :inline t
  :returns (x binding-p
              :rule-classes (:rewrite (:type-prescription :typed-term x))
              :hints(("Goal" :in-theory (enable binding-p))))
  :hooks nil
  (mbe :logic (cons (remove-non-pseudo-vars formals)
                    (remove-corresp-non-pseudo-vars formals (pseudo-term-list-fix args)))
       :exec (cons formals args))
  ///
  (defthm binding->formals-of-binding
    (equal (binding->formals (binding formals args))
           (remove-non-pseudo-vars formals))
    :hints (("goal" :in-theory (e/d (binding->formals) (binding)))
            (and stable-under-simplificationp
                 '(:in-theory (enable binding)))))

  (defthm binding->args-of-binding
    (equal (binding->args (binding formals args))
           (remove-corresp-non-pseudo-vars formals (pseudo-term-list-fix args)))
    :hints (("goal" :in-theory (e/d (binding->args) (binding)))
            (and stable-under-simplificationp
                 '(:in-theory (enable binding)))))

  (defthm binding-of-accessors
    (equal (binding (binding->formals x)
                    (binding->args x))
           (binding-fix x))
    :hints(("Goal" :in-theory (enable binding-fix binding->formals binding->args))))

  (acl2::def-b*-binder binding
    :body
    (std::da-patbind-fn 'binding
                        '((formals . binding->formals)
                          (args . binding->args))
                        acl2::args acl2::forms acl2::rest-expr)))

(deflist bindinglist :elt-type binding :true-listp t)





(defthm-term-vars-flag
  (defthm base-ev-of-alist-fix
    (equal (base-ev x (acl2::alist-fix a))
           (base-ev x a))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable acl2::base-ev-when-pseudo-term-call))))
    :flag term-vars)
  (defthm base-ev-list-of-alist-fix
    (equal (base-ev-list x (acl2::alist-fix a))
           (base-ev-list x a))
    :flag termlist-vars))

(defthm true-listp-of-base-ev-list
  (true-listp (base-ev-list x a))
  :hints (("goal" :induct (len x)))
  :rule-classes :type-prescription)


;; (local (defthm assoc-of-alist-fix
;;          (implies k
;;                   (equal (assoc k (alist-fix x))
;;                          (assoc k x)))))

;; (local (defthm assoc-of-append
;;          (implies k
;;                   (equal (assoc k (append a b))
;;                          (or (assoc k a) (assoc k b))))))

;; (local (in-theory (enable unify-ev-of-nonsymbol-atom)))

;; (defines unify-ev-ind
;;   :flag-local nil
;;   (define unify-ev-ind (x)
;;     :flag term
;;     (cond ((not x) t)
;;           ((symbolp x) t)
;;           ((atom x) t)
;;           ((eq (car x) 'quote) nil)
;;           (t (unify-ev-lst-of-alist-fix-ind (cdr x)))))
;;   (define unify-ev-lst-of-alist-fix-ind (x)
;;     :flag list
;;     (if (atom x)
;;         t
;;       (list (unify-ev-ind (car x))
;;             (unify-ev-lst-of-alist-fix-ind (cdr x)))))
;;   ///
;;   (defthm-unify-ev-ind-flag
;;     (defthm unify-ev-of-alist-fix
;;       (equal (unify-ev x (alist-fix a))
;;              (unify-ev x a))
;;       :hints ((and stable-under-simplificationp
;;                    '(:in-theory (enable unify-ev-of-fncall-args))))
;;       :flag term)
;;     (defthm unify-ev-lst-of-alist-fix
;;       (equal (unify-ev-lst x (alist-fix a))
;;              (unify-ev-lst x a))
;;       :flag list))

;;   (defthm-unify-ev-ind-flag
;;     (defthm unify-ev-of-append-alist-fix
;;       (equal (unify-ev x (append (alist-fix a) a))
;;              (unify-ev x a))
;;       :hints ((and stable-under-simplificationp
;;                    '(:in-theory (enable unify-ev-of-fncall-args))))
;;       :flag term)
;;     (defthm unify-ev-lst-of-append-alist-fix
;;       (equal (unify-ev-lst x (append (alist-fix a) a))
;;              (unify-ev-lst x a))
;;       :flag list)))

;; (local (defthm true-listp-when-symbol-listp
;;          (implies (symbol-listp x)
;;                   (true-listp x))))

;; (local (defthm true-listp-when-pseudo-term-listp
;;          (implies (pseudo-term-listp x)
;;                   (true-listp x))))

(local (defthm alistp-of-pairlis$
         (alistp (pairlis$ a b))))

(local (defthm alistp-of-append
         (implies (and (alistp a) (alistp b))
                  (alistp (append a b)))))

(define base-ev-bindinglist ((x bindinglist-p) (a alistp))
  ;; Returns the alist for evaluating a body term nested inside all the
  ;; bindings.
  :returns (final-alist alistp)
  (b* (((when (atom x)) (acl2::alist-fix a))
       ((binding x1) (car x))
       (new-bindings (pairlis$ x1.formals (base-ev-list x1.args a))))
    (base-ev-bindinglist (cdr x) (append new-bindings a))))


(define remove-self-bindings ((formals symbol-listp)
                              (actuals pseudo-term-listp)
                              (seen-formals symbol-listp))
  :returns (mv (new-formals pseudo-var-list-p)
               (new-actuals pseudo-term-listp)
               (removed-formals symbol-listp))
  :hooks nil
  (cond ((atom formals) (mv nil nil nil))
        ((or (not (mbt (symbolp (car formals))))
             (not (car formals))
             (member-eq (car formals) seen-formals))
         (remove-self-bindings (cdr formals) (cdr actuals) seen-formals))
        ((eq (car formals) (pseudo-term-fix (car actuals)))
         (mv-let (rest-formals rest-actuals removed-formals)
           (remove-self-bindings (cdr formals) (cdr actuals)
                                 (cons (car formals) seen-formals))
           (mv rest-formals rest-actuals (cons (car formals) removed-formals))))
        (t (mv-let (rest-formals rest-actuals removed-formals)
             (remove-self-bindings (cdr formals) (cdr actuals) 
                                   (cons (car formals) seen-formals))
             (mv (cons (car formals) rest-formals)
                 (cons (pseudo-term-fix (car actuals)) rest-actuals)
                 removed-formals))))
  ///
  (defret pseudo-term-list-count-of-remove-self-bindings
    (implies (equal (len formals) (len actuals))
             (<= (pseudo-term-list-count new-actuals) (pseudo-term-list-count actuals)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (x y) (pseudo-term-list-count (cons x y)))
                     (pseudo-term-list-count actuals))))
    :rule-classes :linear)
  ;; (defret acl2-count-of-remove-self-bindings
  ;;   (<= (acl2-count new-actuals) (acl2-count (remove-corresp-non-symbols formals
  ;;                                                                        (pseudo-term-list-fix actuals))))
  ;;   :hints(("Goal" :in-theory (enable pseudo-term-list-fix remove-corresp-non-symbols)))
  ;;   :rule-classes :linear)

  (defthm remove-self-bindings-of-remove-non-symbols
    (equal (remove-self-bindings (remove-non-symbols formals)
                                 (remove-corresp-non-symbols formals actuals)
                                 seen-formals)
           (remove-self-bindings formals actuals seen-formals))
    :hints(("Goal" :in-theory (enable remove-non-symbols remove-corresp-non-symbols))))

  (fty::deffixequiv remove-self-bindings :omit (formals seen-formals)
    :hints(("Goal" :in-theory (enable pseudo-term-list-fix))))

  (defret len-of-remove-self-bindings
    (equal (len new-actuals) (len new-formals)))

  (std::defretd lookup-in-remove-self-bindings
    (equal (hons-assoc-equal k (pairlis$ new-formals new-actuals))
           (and (symbolp k) k
                (not (member k seen-formals))
                (let ((look (hons-assoc-equal k (pairlis$ formals (pseudo-term-list-fix actuals)))))
                  (and (not (eq (cdr look) k))
                       look))))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal pairlis$ pseudo-term-list-fix)
                                   (not)))))

  (std::defretd member-formals-of-remove-self-bindings
    (iff (member k new-formals)
         (and (symbolp k) k
              (not (member k seen-formals))
              (let ((look (hons-assoc-equal k (pairlis$ formals (pseudo-term-list-fix actuals)))))
                (and (not (eq (cdr look) k))
                     look))))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal pairlis$ pseudo-term-list-fix)
                                   (not)))))

  (local (defthm set-equiv-lemma
           (set-equiv (append a (cons b c))
                      (cons b (append a c)))
           :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))

  ;; (local (defthm set-equiv-lemma2
  ;;          (implies (set-equiv a b)
  ;;                   (equal (set-equiv (cons c a) (cons c b)) t))
  ;;          :hints(("Goal" :in-theory (enable set-unequal-witness-rw)))))

  (local (defthm set-equiv-lemma2
           (implies (set-equiv a (set-difference$ b (cons y (cons x c))))
                    (equal (set-equiv (cons x a) (cons x (set-difference$ b (cons y c)))) t))
           :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)
                   :do-not-induct t))))
  ;; (local (defthm set-equiv-lemma2
  ;;          (implies (set-equiv a (set-difference$ b (cons x c)))
  ;;                   (equal (set-equiv (cons x a) (cons x (set-difference$ b c))) t))
  ;;          :hints(("Goal" :in-theory (enable set-unequal-witness-rw)))))


  (defret <fn>-not-member-new-formals-when-member-seen-formals
    (implies (member k seen-formals)
             (not (member k new-formals))))

  (defret <fn>-removed-formals-redef
    (set-equiv removed-formals
               (set-difference-eq (remove-non-symbols formals)
                                  (cons nil (append seen-formals new-formals))))
    :hints(("Goal" :in-theory (e/d (set-difference-eq remove-non-symbols))
            :induct <call>))))



;; (define lambda-remove-redundant-bindings ((formals symbol-listp)
;;                                           (actuals pseudo-term-listp)
;;                                           (deleted-formals symbol-listp))
;;   :returns (mv (new-formals symbol-listp :hyp (symbol-listp formals))
;;                (new-actuals pseudo-term-listp  :hyp (pseudo-term-listp actuals)))
;;   :guard (eql (len formals) (len actuals))
;;   (cond ((atom formals) (mv nil nil))
;;         ((eq (car formals) (car actuals))
;;          (lambda-remove-redundant-bindings (cdr formals) (cdr actuals)
;;                                            (cons (car formals) deleted-formals)))
;;         ((member (car formals) deleted-formals)
;;          (lambda-remove-redundant-bindings (cdr formals) (cdr actuals) deleted-formals))
;;         (t 
;;          (b* (((mv rest-f rest-a)
;;                (lambda-remove-redundant-bindings (cdr formals) (cdr actuals) deleted-formals)))
;;            (mv (cons (car formals) rest-f)
;;                (cons (car actuals) rest-a)))))
;;   ///
;;   (defret len-of-lambda-remove-redundant-bindings
;;     (equal (len new-actuals) (len new-formals)))

;;   (defret lookup-in-lambda-remove-redundant-bindings
;;     (equal (hons-assoc-equal k (pairlis$ new-formals new-actuals))
;;            (and (not (member k deleted-formals))
;;                 (let ((look (hons-assoc-equal k (pairlis$ formals actuals))))
;;                   (and (not (equal (cdr look) k))
;;                        look)))))

;;   (defret not-member-when-deleted-formal
;;     (implies (member v deleted-formals)
;;              (not (member v new-formals))))

;;   (defret member-of-new-formals
;;     (implies (and (member v formals)
;;                   (not (member v deleted-formals)))
;;              (iff (member v new-formals)
;;                   (not (equal (cdr (hons-assoc-equal v (pairlis$ formals actuals))) v)))))

;;   ;; (defret lookup-in-lambda-remove-redundant-bindings-eval
;;   ;;   (equal (hons-assoc-equal k (pairlis$ new-formals (base-ev-list new-actuals a)))
;;   ;;          (and (not (member k deleted-formals))
;;   ;;               (let ((look (hons-assoc-equal k (pairlis$ formals actuals))))
;;   ;;                 (and look
;;   ;;                      (not (equal (cdr look) k))
;;   ;;                      (cons k (base-ev (cdr look) a)))))))
;;   )





;; (local (defthm symbol-listp-of-set-diff
;;          (implies (symbol-listp x)
;;                   (symbol-listp (set-difference-eq x y)))
;;          :hints(("Goal" :in-theory (enable set-difference-eq)))))


;; (local (defthm symbol-listp-of-append
;;          (implies (and (symbol-listp a)
;;                        (symbol-listp b))
;;                   (symbol-listp (append a b)))))


(local (defthm pseudo-term-listp-of-append
         (implies (and (pseudo-term-listp a)
                       (pseudo-term-listp b))
                  (pseudo-term-listp (append a b)))))

(local (defthm pseudo-term-listp-of-repeat
         (implies (pseudo-termp x)
                  (pseudo-term-listp (repeat n x)))
         :hints(("Goal" :in-theory (enable repeat)))))

(local (defthm len-of-repeat
         (equal (len (repeat n x))
                (nfix n))
         :hints(("Goal" :in-theory (enable repeat)))))

(local (defthm base-ev-list-of-append
         (Equal (base-ev-list (append x y) a)
                (append (base-ev-list x a)
                        (base-ev-list y a)))))

(local (defthm base-ev-list-of-repeat
         (Equal (base-ev-list (repeat n x) a)
                (repeat n (base-ev x a)))
         :hints(("Goal" :in-theory (enable repeat)))))

(local (defthm len-of-base-ev-list
           (equal (len (base-ev-list x a))
                  (len x))))

(local (defthm base-ev-list-of-list-fix
         (equal (base-ev-list (true-list-fix x) a)
                (base-ev-list x a))
         :hints(("Goal" :in-theory (enable true-list-fix)))))

(local (defthm set-difference-of-append
         (equal (set-difference-eq (append a b) c)
                (append (set-difference-eq a c)
                        (set-difference-eq b c)))))

(local (include-book "std/alists/hons-assoc-equal" :dir :system))

(local (defthm hons-assoc-equal-of-pairlis-under-iff
         (iff (hons-assoc-equal k (pairlis$ keys vals))
              (member k keys))))



(local (deflist pseudo-var-list :elt-type pseudo-var :true-listp t))

(define lambda-nest-to-bindinglist ((x pseudo-termp))
  :returns (mv (bindings bindinglist-p)
               (body pseudo-termp))
  :measure (pseudo-term-count x)
  (pseudo-term-case x
    :lambda
    (b* (;; BOZO if calling term-free-vars is expensive, could optimize by
         ;; requiring that lambda bodies never have free variables.  But might
         ;; take just as much to compute that.
         (free-vars (term-free-vars x.body x.formals))
         ((mv reduced-formals reduced-actuals ?removed-formals)
          (remove-self-bindings x.formals x.args nil))
         (final-formals (append free-vars reduced-formals))
         (final-actuals (append (repeat (len free-vars) ''nil) reduced-actuals))
         ((mv rest body) (lambda-nest-to-bindinglist x.body)))
      (mv (cons (binding final-formals final-actuals) rest)
          body))
    :otherwise (mv nil (pseudo-term-fix x)))
  
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

  (local (Defthm hons-assoc-equal-of-pairlis$-base-ev-list
           (equal (hons-assoc-equal x (pairlis$ keys (base-ev-list vals a)))
                  (let ((look (hons-assoc-equal x (pairlis$ keys (pseudo-term-list-fix vals)))))
                    (and look
                         (cons x (base-ev (cdr look) a)))))
           :hints(("Goal" :in-theory (enable pseudo-term-list-fix)
                   :induct (pairlis$ keys vals)))))

  (local (defthm intersectp-when-member-both
           (implies (and (member x a)
                         (member x b))
                    (intersectp a b))
           :hints(("Goal" :in-theory (enable intersectp)))))


  (local
   (defthm-term-vars-flag
     (defthm base-ev-of-lambda-nest-fixup
       (b* (((mv reduced-formals reduced-actuals &)
             (remove-self-bindings formals actuals nil))
            (orig-alist (pairlis$ formals (base-ev-list actuals a)))
            (new-alist (append (pairlis$ free-vars (repeat (len free-vars) nil))
                               (pairlis$ reduced-formals (base-ev-list reduced-actuals a))
                               a)))
         (implies (and (double-rewrite (not (intersectp free-vars formals)))
                       (double-rewrite (subsetp (set-difference-eq (term-vars x) formals) free-vars)))
                  (equal (base-ev x new-alist)
                         (base-ev x orig-alist))))
       :hints ((and stable-under-simplificationp
                    '(:in-theory (enable member-formals-of-remove-self-bindings
                                         lookup-in-remove-self-bindings
                                         acl2::base-ev-when-pseudo-term-call)
                      :expand ((term-vars x)))))
       :flag term-vars)
     (defthm base-ev-list-of-lambda-nest-fixup
       (b* (((mv reduced-formals reduced-actuals)
             (remove-self-bindings formals actuals nil))
            (orig-alist (pairlis$ formals (base-ev-list actuals a)))
            (new-alist (append (pairlis$ free-vars (repeat (len free-vars) nil))
                               (pairlis$ reduced-formals (base-ev-list reduced-actuals a))
                               a)))
         (implies (and (double-rewrite (not (intersectp free-vars formals)))
                       (double-rewrite (subsetp (set-difference-eq (termlist-vars x) formals) free-vars))) ;; argh
                  (equal (base-ev-list x new-alist)
                         (base-ev-list x orig-alist))))
       :hints ('(:expand ((termlist-vars x))))
       :flag termlist-vars)))

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
           (declare (Xargs :measure (pseudo-term-count x)))
           (pseudo-term-case x
             :lambda
             (b* ((free-vars (term-free-vars x.body x.formals))
                  ((mv reduced-formals reduced-actuals &)
                   (remove-self-bindings x.formals x.args nil))
                  (final-formals (append free-vars reduced-formals))
                  (final-actuals (append (repeat (len free-vars) ''nil) reduced-actuals))
                  (new-a (append (pairlis$ final-formals (base-ev-list final-actuals a)) a)))
               (lambda-nest-to-bindinglist-correct-ind x.body new-a))
             :otherwise a)))

  (defret lambda-nest-to-bindinglist-correct
    (equal (base-ev body (base-ev-bindinglist bindings a))
           (base-ev x a))
    :hints (("goal" :induct (lambda-nest-to-bindinglist-correct-ind x a)
             :expand (<call>)
             :in-theory (enable base-ev-bindinglist)))))

(local (defthm symbol-listp-of-union
         (implies (and (symbol-listp x)
                       (symbol-listp y))
                  (symbol-listp (union-eq x y)))))



(define bindinglist-free-vars ((x bindinglist-p))
  :verify-guards nil
  :returns (vars pseudo-var-list-p :rule-classes (:rewrite (:type-prescription :typed-term vars)))
  (if (atom x)
      nil
    (b* (((binding x1) (car x)))
      (mbe :logic (union-eq (termlist-vars x1.args)
                            (set-difference-eq (bindinglist-free-vars (cdr x))
                                               x1.formals))
           :exec (termlist-vars-acc x1.args
                                    (set-difference-eq (bindinglist-free-vars (cdr x))
                                                       x1.formals)))))
  ///
  (verify-guards bindinglist-free-vars))


(local (defthm true-listp-of-union
         (equal (true-listp (union-equal x y))
                (true-listp y))))

(define bindinglist-bound-vars ((x bindinglist-p))
  :returns (final-vars pseudo-var-list-p :rule-classes (:rewrite (:type-prescription :typed-term final-vars)))
  :verify-guards nil
  (if (atom x)
      nil
    (b* (((binding x1) (car x)))
      (union-eq x1.formals (bindinglist-bound-vars (cdr x)))))
  ///

  (verify-guards bindinglist-bound-vars))





(local (defun base-ev-bindinglist-when-alists-agree-on-free-vars-ind (x a b)
         (if (atom x)
             (list a b)
           (b* (((binding x1) (car x))
                (new-part (pairlis$ x1.formals (base-ev-list x1.args a))))
             (base-ev-bindinglist-when-alists-agree-on-free-vars-ind
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
                                     acl2::lookup-when-eval-alists-agree)))))

(local (defthm set-difference-nil
         (implies (true-listp x)
                  (equal (set-difference-equal x nil) x))))

(local (defthm pairlis-of-base-ev-list-when-eval-alists-agree-of-take
         (implies (eval-alists-agree (termlist-vars (take (len vars) vals)) a b)
                  (equal (pairlis$ vars (base-ev-list vals a))
                         (pairlis$ vars (base-ev-list vals b))))
         :hints(("Goal" :induct (pairlis$ vars vals)
                 :in-theory (enable pairlis$ take termlist-vars)))))


(defthm base-ev-bindinglist-when-eval-alists-agree-on-free-vars
  (implies (and (eval-alists-agree (bindinglist-free-vars x) a b)
                (eval-alists-agree (set-difference-eq (term-vars body)
                                                      (bindinglist-bound-vars x)) a b))
           (equal (base-ev body (base-ev-bindinglist x a))
                  (base-ev body (base-ev-bindinglist x b))))
  :hints(("Goal" :in-theory (enable base-ev-bindinglist
                                    bindinglist-free-vars
                                    bindinglist-bound-vars
                                    eval-alists-agree-by-bad-guy
                                    acl2::lookup-when-eval-alists-agree)
          :induct (base-ev-bindinglist-when-alists-agree-on-free-vars-ind x a b)
          :expand ((:free (a) (base-ev-bindinglist x a))))))

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
  :returns (term pseudo-termp)
  :verify-guards nil
  (b* (((when (atom x)) (pseudo-term-fix body))
       ((binding x1) (car x))
       (free-vars (union-eq (bindinglist-free-vars (cdr x))
                            (set-difference-eq (term-vars body)
                                               (bindinglist-bound-vars (cdr x)))))
       (missing-vars (set-difference-eq free-vars x1.formals))
       (rest-body (bindinglist-to-lambda-nest (cdr x) body))
       (full-formals (append missing-vars x1.formals))
       (full-actuals (append missing-vars x1.args)))
    (pseudo-term-lambda full-formals rest-body full-actuals))
  ///
  (local (defthm pairlis$-of-append
           (implies (equal (len x1) (len x2))
                    (equal (pairlis$ (append x1 y1) (append x2 y2))
                           (append (pairlis$ x1 x2)
                                   (pairlis$ y1 y2))))))

  (local (defthm termlist-vars-of-append
           (set-equiv (termlist-vars (append a b))
                      (append (termlist-vars a)
                              (termlist-vars b)))
           :hints(("Goal" :in-theory (enable termlist-vars)))))

  (local (defthmd term-vars-when-symbolp
           (implies (pseudo-var-p x)
                    (equal (term-vars x) (list x)))
           :hints(("Goal" :in-theory (enable pseudo-term-kind pseudo-term-var->name)
                   :expand ((term-vars x))))))

  (local (defthm termlist-vars-of-symbol-list
           (implies (symbol-listp x)
                    (set-equiv (termlist-vars x)
                               (remove nil x)))
           :hints(("Goal" :in-theory (enable termlist-vars
                                             term-vars-when-symbolp)))))

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

  (local (defthm remove-nil-of-pseudo-var-list
           (implies (pseudo-var-list-p x)
                    (equal (remove nil x) x))))

  (defret free-vars-of-bindinglist-to-lambda-nest
    (set-equiv (term-vars term)
               (union-eq (bindinglist-free-vars x)
                         (set-difference-eq (term-vars body)
                                            (bindinglist-bound-vars x))))
    :hints(("Goal" :in-theory (enable term-vars
                                      bindinglist-free-vars
                                      bindinglist-bound-vars)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable set-difference-eq-when-set-equiv-append)))))

  (local (defthm lookup-in-pairlis$-vars
           (equal (hons-assoc-equal k (pairlis$ vars (base-ev-list vars a)))
                  (and (member k vars)
                       (cons k (base-ev k a))))
           :hints(("Goal" :in-theory (enable pairlis$)
                   :induct (len vars)))))

  (local (defthm base-ev-when-member-of-nonnil-symbol-list
           (implies (and (member k vars)
                         (symbol-listp vars)
                         (not (member nil vars)))
                    (equal (base-ev k a)
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

  (local (defthm pairlis$-of-base-ev-list-take
           (equal (pairlis$ vars (base-ev-list (take (len vars) vals) a))
                  (pairlis$ vars (base-ev-list vals a)))
           :hints(("Goal" :in-theory (enable pairlis$ take)
                   :induct (pairlis$ vars vals)))))

  (local (defthm base-ev-when-member-pseudo-var-list
           (implies (and (member x lst)
                         (pseudo-var-list-p lst))
                    (equal (base-ev x a)
                           (cdr (hons-assoc-equal x a))))))

  (defret bindinglist-to-lambda-nest-correct
    (equal (base-ev term a)
           (base-ev body (base-ev-bindinglist x a)))
    :hints (("goal" :induct (base-ev-bindinglist x a)
             :in-theory (e/d (base-ev-bindinglist
                                eval-alists-agree-by-bad-guy)
                             (base-ev-when-agree-on-term-vars)))
            (acl2::use-termhint
             (b* (((binding x1) (car x))
                  (formals x1.formals)
                  (actuals x1.args)
                  (free-vars (union-eq (bindinglist-free-vars (cdr x))
                                       (set-difference-eq (term-vars body)
                                                          (bindinglist-bound-vars (cdr x)))))
                  (missing-vars (set-difference-eq free-vars formals))
                  (rest-body (bindinglist-to-lambda-nest (cdr x) body))
                  (full-formals (append missing-vars formals))
                  (full-actuals (append missing-vars actuals))
                  (impl-alist (pairlis$ full-formals (base-ev-list full-actuals a)))
                  (spec-alist (append (pairlis$ formals (base-ev-list actuals a)) a)))
               `'(:use ((:instance base-ev-when-agree-on-term-vars
                         (x ,(hq rest-body))
                         (a ,(hq impl-alist))
                         (b  ,(hq spec-alist))))))))))
    

(define bindinglist-to-lambda-nest-aux ((x bindinglist-p)
                                        (body pseudo-termp))
  :returns (mv (term)
               (free-vars))
  :verify-guards nil
  (b* (((when (atom x)) (mv (pseudo-term-fix body) (term-vars body)))
       ((mv rest-body free-vars)
        (bindinglist-to-lambda-nest-aux (cdr x) body))
       ((binding x1) (car x))
       (missing-vars (set-difference-eq free-vars x1.formals))
       (full-formals (append missing-vars x1.formals))
       (full-actuals (append missing-vars x1.args))
       (new-free-vars (union-eq (termlist-vars x1.args)
                                missing-vars)))
    (mv (pseudo-term-lambda full-formals rest-body full-actuals)
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
                     (set-difference-eq (term-vars body)
                                        (bindinglist-bound-vars x))))
    :hints(("Goal" :in-theory (enable bindinglist-free-vars
                                      bindinglist-bound-vars))))

  (defret bindinglist-to-lambda-nest-aux-elim
    (equal term (bindinglist-to-lambda-nest x body))
    :hints(("Goal" :in-theory (enable bindinglist-to-lambda-nest))))

  (verify-guards bindinglist-to-lambda-nest-aux))

(define bindinglist-to-lambda-nest-exec ((x bindinglist-p)
                                         (body pseudo-termp))
  :enabled t
  :guard-hints (("goal" :in-theory (enable bindinglist-to-lambda-nest)))
  (mbe :logic (bindinglist-to-lambda-nest x body)
       :exec (b* (((when (atom x)) body)
                  ((mv rest-body free-vars)
                   (bindinglist-to-lambda-nest-aux (cdr x) body))
                  ((binding x1) (car x))
                  (missing-vars (set-difference-eq free-vars x1.formals))
                  (full-formals (append missing-vars x1.formals))
                  (full-actuals (append missing-vars x1.args)))
               (pseudo-term-lambda full-formals rest-body full-actuals))))


(defun translate-cmp-ignore-ok (x stobjs-out logic-modep known-stobjs ctx w state-vars)
  (declare (xargs :mode :program))
  ;; We override ignore-ok so that we can translate a list of B* binders
  ;; without giving a body that includes all the bound vars.
  (let ((w #!acl2 (putprop 'acl2-defaults-table 'table-alist
                           (put-assoc-equal-fast :ignore-ok t (table-alist 'acl2-defaults-table w))
                           w)))
    (acl2::translate-cmp x stobjs-out logic-modep known-stobjs ctx w state-vars)))

(define b*-binders-to-bindinglist ((x "list of bstar binders")
                                   wrld)
  :mode :program
  :returns (mv err bindinglist)
  (b* ((state-vars (acl2::default-state-vars nil))
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


(define pseudo-term-list-max-count ((x pseudo-term-listp))
  :returns (max-count natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (pseudo-term-count (car x))
         (pseudo-term-list-max-count (cdr x)))))

(local
 (defsection pseudo-term-list-max-count

   (local (in-theory (enable pseudo-term-list-max-count)))

   (defthm pseudo-term-list-max-count-car
     (implies (consp x)
              (<= (pseudo-term-count (car x))
                  (pseudo-term-list-max-count x)))
     :rule-classes :linear)

   (defthm pseudo-term-list-max-count-cdr
     (<= (pseudo-term-list-max-count (cdr x))
         (pseudo-term-list-max-count x))
     :rule-classes :linear)

   (defthm pseudo-term-list-max-count-of-remove-corresp-non-pseudo-vars
     (implies (equal (len x) (len y))
              (<= (pseudo-term-list-max-count
                   (remove-corresp-non-pseudo-vars x y))
                  (pseudo-term-list-max-count y)))
     :hints(("Goal" :in-theory (enable remove-corresp-non-pseudo-vars)))
     :rule-classes :linear)

   (defthm pseudo-term-list-max-count-of-append-1
     (equal (pseudo-term-list-max-count (append a b))
            (max (pseudo-term-list-max-count a) (pseudo-term-list-max-count b))))

   (defthm pseudo-term-list-max-count-of-remove-self-bindings
     (implies (equal (len x) (len y))
              (<= (pseudo-term-list-max-count (mv-nth 1 (remove-self-bindings x y seen)))
                  (pseudo-term-list-max-count y)))
     :hints(("Goal" :in-theory (enable remove-self-bindings)))
     :rule-classes :linear)

   (defthm pseudo-term-list-max-count-of-repeat
     (equal (pseudo-term-list-max-count (repeat n x))
            (if (zp n) 0 (pseudo-term-count x)))
     :hints(("Goal" :in-theory (enable repeat))))

   (defthm pseudo-term-list-max-count-of-true-list-fix
     (equal (pseudo-term-list-max-count (true-list-fix x))
            (pseudo-term-list-max-count x)))

   (defthm pseudo-term-list-max-count-lte-pseudo-term-list-count
     (< (pseudo-term-list-max-count x) (pseudo-term-list-count x))
     :rule-classes :linear)

   (fty::deffixequiv pseudo-term-list-max-count)))

(define bindinglist-max-count ((x bindinglist-p))
  :returns (max-count natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (pseudo-term-list-max-count (binding->args (car x)))
         (bindinglist-max-count (cdr x)))))

(local
 (defsection bindinglist-max-count
   (local (in-theory (enable bindinglist-max-count)))

   (defthm bindinglist-max-count-car
     (implies (consp x)
              (<= (pseudo-term-list-max-count (binding->args (car x)))
                  (bindinglist-max-count x)))
     :rule-classes :linear)

   (defthm bindinglist-max-count-cdr
     (<= (bindinglist-max-count (cdr x))
         (bindinglist-max-count x))
     :rule-classes :linear)

   (fty::deffixequiv bindinglist-max-count
     :hints(("Goal" :in-theory (enable bindinglist-fix))))

   (local (defthm pseudo-term-list-max-count-of-remove-corresp-non-pseudo-vars-rw
            ;; gross, for some reason linear wasn't doing the trick
            (implies (equal (len x) (len y))
                     (equal (pseudo-term-list-max-count
                             (remove-corresp-non-pseudo-vars x y))
                            (min (pseudo-term-list-max-count y)
                                 (hide (pseudo-term-list-max-count
                                        (remove-corresp-non-pseudo-vars x y))))))
            :hints(("Goal" :expand ((:free (x) (hide x)))))))

   (defthm bindinglist-max-count-of-lambda-nest-to-bindinglist
     (b* (((mv bindings body) (lambda-nest-to-bindinglist x)))
       (<= (+ (bindinglist-max-count bindings) (pseudo-term-count body))
           (pseudo-term-count x)))
     :hints(("Goal" :in-theory (enable lambda-nest-to-bindinglist)
             :induct (lambda-nest-to-bindinglist x)
             :expand ((pseudo-term-count x))))
     :rule-classes
     ((:linear :trigger-terms
       ((bindinglist-max-count (mv-nth 0 (lambda-nest-to-bindinglist x)))
        (pseudo-term-count (mv-nth 1 (lambda-nest-to-bindinglist x)))))))

   (defthm body-count-of-lambda-nest-to-bindinglist
     (b* (((mv ?bindings body) (lambda-nest-to-bindinglist x)))
       (implies (pseudo-term-case x :lambda)
                (< (pseudo-term-count body)
                   (pseudo-term-count x))))
     :hints(("Goal" :in-theory (enable lambda-nest-to-bindinglist)
             :induct (lambda-nest-to-bindinglist x)
             :expand ((pseudo-term-count x))))
     :rule-classes :linear)))




(defines pseudo-term-binding-count
  (define pseudo-term-binding-count ((x pseudo-termp))
    :Returns (count posp :rule-classes :type-prescription)
    :measure (list (pseudo-term-count x) 1 0 0)
    :well-founded-relation acl2::nat-list-<
    :measure-debug t
    (pseudo-term-case x
      :const 1
      :var 1
      :fncall (+ 1 (pseudo-term-list-binding-count x.args))
      :lambda (b* (((mv bindings body) (lambda-nest-to-bindinglist x)))
                (+ 1
                   (bindinglist-count bindings)
                   (pseudo-term-binding-count body)))))

  (define pseudo-term-list-binding-count ((x pseudo-term-listp))
    :measure (list (pseudo-term-list-max-count x) 2 (len x) 0)
    :Returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1 (pseudo-term-binding-count (car x))
         (pseudo-term-list-binding-count (cdr x)))))

  (define bindinglist-count ((x bindinglist-p))
    :measure (list (bindinglist-max-count x) 3 (len x) 0)
    :Returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        2
      (+ 1 (binding-count (car x))
         (bindinglist-count (cdr x)))))

  (define binding-count ((x binding-p))
    :measure (list (pseudo-term-list-max-count (binding->args x))
                   3 0 0)
    :Returns (count posp :rule-classes :type-prescription)
    (+ 1 (pseudo-term-list-binding-count (binding->args x))))
  ///
  (fty::deffixequiv-mutual pseudo-term-binding-count)

  
  (defthm pseudo-term-binding-count-of-bindinglist-body
    (b* (((mv ?bindings body) (lambda-nest-to-bindinglist x)))
      (implies (equal (pseudo-term-kind x) :lambda)
               (< (pseudo-term-binding-count body)
                  (pseudo-term-binding-count x))))
    :hints (("goal" :expand ((pseudo-term-binding-count x))))
    :rule-classes :linear)

  (defthm pseudo-term-binding-count-of-bindinglist-bindings
    (b* (((mv bindings ?body) (lambda-nest-to-bindinglist x)))
      (implies (equal (pseudo-term-kind x) :lambda)
               (< (bindinglist-count bindings)
                  (pseudo-term-binding-count x))))
    :hints (("goal" :expand ((pseudo-term-binding-count x))))
    :rule-classes :linear)
  
  (defthm pseudo-term-list-binding-count-of-pseudo-term-call->args
    (implies (equal (pseudo-term-kind x) :fncall)
             (< (pseudo-term-list-binding-count (acl2::pseudo-term-call->args x))
                (pseudo-term-binding-count x)))
    :hints (("goal" :expand ((pseudo-term-binding-count x))))
    :rule-classes :linear)

  (defthm pseudo-term-list-binding-count-of-binding->args
    (< (pseudo-term-list-binding-count (binding->args x))
       (binding-count x))
    :rule-classes :linear)

  (defthm binding-count-of-car-weak
    (<= (binding-count (car x))
        (bindinglist-count x))
    :hints (("goal" :expand ((bindinglist-count x))))
    :rule-classes :linear)

  (defthm binding-count-of-car
    (implies (consp x)
             (< (binding-count (car x))
                (bindinglist-count x)))
    :rule-classes :linear)

  (defthm bindinglist-count-of-cdr-weak
    (<= (bindinglist-count (cdr x))
        (bindinglist-count x))
    :rule-classes :linear)

  (defthm bindinglist-count-of-cdr
    (implies (consp x)
             (< (bindinglist-count (cdr x))
                (bindinglist-count x)))
    :rule-classes :linear)

  (defthm bindinglist-count-of-cons
    (< (+ (binding-count x) (bindinglist-count y))
       (bindinglist-count (cons x y)))
    :rule-classes :linear)

  (defthm pseudo-term-list-binding-count-of-cdr-weak
    (<= (pseudo-term-list-binding-count (cdr x)) (pseudo-term-list-binding-count x))
    :rule-classes :linear)

  (defthm pseudo-term-list-binding-count-of-cdr
    (implies (consp x)
             (< (pseudo-term-list-binding-count (cdr x)) (pseudo-term-list-binding-count x)))
    :rule-classes :linear)

  (defthm pseudo-term-binding-count-of-car-weak
    (<= (pseudo-term-binding-count (car x)) (pseudo-term-list-binding-count x))
    :rule-classes :linear)

  (defthm pseudo-term-binding-count-of-car
    (implies (consp x)
             (< (pseudo-term-binding-count (car x)) (pseudo-term-list-binding-count x)))
    :rule-classes :linear)

  (defthm pseudo-term-list-binding-count-of-cons
    (< (+ (pseudo-term-binding-count x) (pseudo-term-list-binding-count y)) (pseudo-term-list-binding-count (cons x y)))
    :hints (("goal" :expand ((pseudo-term-list-binding-count (cons x y)))))
    :rule-classes :linear))


                       
