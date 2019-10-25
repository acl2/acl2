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

(include-book "std/util/define" :dir :system)
(include-book "std/util/defaggrify-defrec" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "unify-strict")

(local (std::add-default-post-define-hook :fix))

(std::defaggrify-defrec acl2::congruence-rule)

(defevaluator equiv-ev equiv-ev-list
  ((equal x y) (iff x y) (if x y z) (implies x y) (not x) (typespec-check ts x))
  :namedp t)


(acl2::def-ev-pseudo-term-fty-support equiv-ev equiv-ev-list)

(define equiv-ev-alist ((x pseudo-term-subst-p) a)
  ;; :verify-guards nil
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x) (equiv-ev (cdar x) a))
              (equiv-ev-alist (cdr x) a))
      (equiv-ev-alist (cdr x) a)))
  ///

  (defthm lookup-in-equiv-ev-alist-split
    (equal (assoc k (equiv-ev-alist x a))
           (and (pseudo-var-p k)
                (let ((look (assoc k x)))
                  (and look
                       (cons k (equiv-ev (cdr look) a)))))))

  (local (in-theory (enable pseudo-term-subst-fix))))


(local (defthm not-quote-when-pseudo-fnsym-p
         (implies (pseudo-fnsym-p f)
                  (not (equal 'quote f)))))

(acl2::def-meta-extract equiv-ev equiv-ev-list)

(define equiv-rel-term ((fn pseudo-fnsym-p))
  :returns (equiv pseudo-termp)
  (b* ((fn (pseudo-fnsym-fix fn)))
    (conjoin `((,fn x x)
               (implies (,fn x y)
                        (,fn y x))
               (implies (if (,fn x y)
                            (,fn y z)
                          'nil)
                        (,fn x z)))))
  ///
  (defthmd equiv-rel-term-implies-reflexive
    (implies (and (equiv-ev-theoremp (equiv-rel-term fn))
                  (pseudo-fnsym-p fn))
             (equiv-ev (list fn x x) a))
    :hints (("goal" :use ((:instance equiv-ev-falsify
                           (x `(,fn x x))
                           (a `((x . ,(equiv-ev x a))))))
             :in-theory (enable equiv-ev-of-fncall-args))))

  (defthmd equiv-rel-term-implies-symmetric
    (implies (and (equiv-ev-theoremp (equiv-rel-term fn))
                  (pseudo-fnsym-p fn)
                  (equiv-ev (list fn x y) a))
             (equiv-ev (list fn y x) a))
    :hints (("goal" :use ((:instance equiv-ev-falsify
                           (x `(implies (,fn x y)
                                        (,fn y x)))
                           (a `((x . ,(equiv-ev x a))
                                (y . ,(equiv-ev y a))))))
             :in-theory (enable equiv-ev-of-fncall-args))))

  (defthmd equiv-rel-term-implies-transitive
    (implies (and (equiv-ev-theoremp (equiv-rel-term fn))
                  (pseudo-fnsym-p fn)
                  (equiv-ev (list fn x y) a)
                  (equiv-ev (list fn y z) a))
             (equiv-ev (list fn x z) a))
    :hints (("goal" :use ((:instance equiv-ev-falsify
                           (x `(implies (if (,fn x y)
                                            (,fn y z)
                                          'nil)
                                        (,fn x z)))
                           (a `((x . ,(equiv-ev x a))
                                (y . ,(equiv-ev y a))
                                (z . ,(equiv-ev z a))))))
             :in-theory (enable equiv-ev-of-fncall-args)))))

;; (defsection equiv-relp
;;   (defun-sk equiv-relp (f)
;;     (forall (a)
;;             (and ;; (booleanp (equiv-ev (list f x y) a))
;;              (equiv-ev (pseudo-term-fncall f '(x x)) a)
;;              (implies (equiv-ev (pseudo-term-fncall f '(x y)) a)
;;                       (equiv-ev (pseudo-term-fncall f '(y x)) a))
;;              (implies (and (equiv-ev (pseudo-term-fncall f '(x y)) a)
;;                            (equiv-ev (pseudo-term-fncall f '(y z)) a))
;;                       (equiv-ev (pseudo-term-fncall f '(x z)) a))))
;;     :rewrite :direct)
;;   (in-theory (disable equiv-relp
;;                       equiv-relp-necc))
  
;;   (fty::deffixcong pseudo-fnsym-equiv iff (equiv-relp f) f
;;     :hints (("goal" :use ((:instance equiv-relp-necc
;;                            (f f)
;;                            (a (equiv-relp-witness (pseudo-fnsym-fix f))))
;;                           (:instance equiv-relp-necc
;;                            (f (pseudo-fnsym-fix f))
;;                            (a (equiv-relp-witness f))))
;;              :in-theory (enable equiv-relp))))

;;   (defthm equiv-relp-implies-reflexive
;;     (implies (and (equiv-relp f)
;;                   (pseudo-fnsym-p f))
;;              (equiv-ev (list f x x) a))
;;     :hints (("goal" :use ((:instance equiv-relp-necc
;;                            (a `((x . ,(equiv-ev x a))))))
;;              :in-theory (enable equiv-ev-of-fncall-args
;;                                 ))))

;;   (defthm equiv-relp-implies-symmetric
;;     (implies (and (equiv-relp f)
;;                   (pseudo-fnsym-p f)
;;                   (equiv-ev (list f x y) a))
;;              (equiv-ev (list f y x) a))
;;     :hints (("goal" :use ((:instance equiv-relp-necc
;;                            (a `((x . ,(equiv-ev x a))
;;                                 (y . ,(equiv-ev y a))))))
;;              :in-theory (enable equiv-ev-of-fncall-args))))

;;   (defthm equiv-relp-implies-transitive
;;     (implies (and (equiv-relp f)
;;                   (pseudo-fnsym-p f)
;;                   (equiv-ev (list f x y) a)
;;                   (equiv-ev (list f y z) a))
;;              (equiv-ev (list f x z) a))
;;     :hints (("goal" :use ((:instance equiv-relp-necc
;;                            (a `((x . ,(equiv-ev x a))
;;                                 (y . ,(equiv-ev y a))
;;                                 (z . ,(equiv-ev z a))))))
;;              :in-theory (enable equiv-ev-of-fncall-args)))))
                           



(local (defthm equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (cond ((eql n 0) (not (consp x)))
                               ((zp n) nil)
                               ((consp x) (equal (len (cdr x)) (1- n)))
                               (t nil))))))

(local (in-theory (disable len)))

(local
 (progn
   (defret equiv-ev-of-term-subst-strict
     (equal (equiv-ev (term-subst-strict x a) env)
            (equiv-ev x (equiv-ev-alist a env)))
     :hints (("goal" :use ((:functional-instance base-ev-of-term-subst-strict
                            (base-ev equiv-ev)
                            (base-ev-list equiv-ev-list)
                            (base-ev-alist equiv-ev-alist)))
              :in-theory (enable equiv-ev-alist)))
     :fn term-subst-strict)
   (defret equiv-ev-list-of-termlist-subst-strict
     (equal (equiv-ev-list (termlist-subst-strict x a) env)
            (equiv-ev-list x (equiv-ev-alist a env)))
     :hints (("goal" :use ((:functional-instance base-ev-list-of-termlist-subst-strict
                            (base-ev equiv-ev)
                            (base-ev-list equiv-ev-list)
                            (base-ev-alist equiv-ev-alist)))))
     :fn termlist-subst-strict)))

(local (defthm equal-pseudo-term-fix-forward
         (implies (equal (pseudo-term-fix x) y)
                  (pseudo-term-equiv x y))
         :rule-classes :forward-chaining))

(local (defthm equiv-ev-when-equiv-term-subst-strict
         (implies (equal (pseudo-term-fix y) (term-subst-strict x a))
                  (equal (equiv-ev y env)
                         (equiv-ev x (equiv-ev-alist a env))))
         :hints (("goal" :use ((:instance equiv-ev-of-pseudo-term-fix-x
                                (x y) (a env))
                               (:instance equiv-ev-of-term-subst-strict))
                  :in-theory (disable equiv-ev-of-pseudo-term-fix-x
                                      equiv-ev-of-term-subst-strict
                                      equiv-ev-pseudo-term-equiv-congruence-on-x)))))

(define search-match-in-conjunction ((pat pseudo-termp)
                                     (term pseudo-termp))
  :measure (pseudo-term-count term)
  :hooks ((:fix :hints (("goal" :induct (search-match-in-conjunction pat term)
                         :expand ((:free (pat) (search-match-in-conjunction pat term))
                                  (search-match-in-conjunction pat (pseudo-term-fix term)))))))
                             
  (b* (((mv ok &) (term-unify-strict term pat nil))
       ((when ok) t)
       ((unless (pseudo-term-case term :fncall)) nil)
       ((pseudo-term-fncall term))
       ((unless (and (eq term.fn 'if)
                     (equal (len term.args) 3)
                     (equal (third term.args) ''nil)))
        nil))
    (or (search-match-in-conjunction pat (first term.args))
        (search-match-in-conjunction pat (second term.args))))
  ///
  (defthmd equiv-ev-theoremp-of-conjunction
    (implies (and (pseudo-term-case term :fncall)
                  (equal (pseudo-term-fncall->fn term) 'if)
                  (equal (third (pseudo-term-call->args term)) ''nil))
             (iff (equiv-ev-theoremp term)
                  (and (equiv-ev-theoremp (first (pseudo-term-call->args term)))
                       (equiv-ev-theoremp (second (pseudo-term-call->args term))))))
    :hints (("goal" :use ((:instance equiv-ev-falsify
                           (x term) (a (equiv-ev-falsify (first (pseudo-term-call->args term)))))
                          (:instance equiv-ev-falsify
                           (x term) (a (equiv-ev-falsify (second (pseudo-term-call->args term)))))
                          (:instance equiv-ev-falsify
                           (x (first (pseudo-term-call->args term)))
                           (a (equiv-ev-falsify term)))
                          (:instance equiv-ev-falsify
                           (x (second (pseudo-term-call->args term)))
                           (a (equiv-ev-falsify term))))
             :in-theory (disable pseudo-termp pseudo-term-listp))))

  (defthmd search-match-in-conjunction-correct
    (implies (and (equiv-ev-theoremp term)
                  (search-match-in-conjunction pat term))
             (equiv-ev pat a))
    :hints(("Goal" :in-theory (e/d (search-match-in-conjunction
                                    equiv-ev-theoremp-of-conjunction))
            :induct (search-match-in-conjunction pat term))
           (and stable-under-simplificationp
                '(:use ((:instance equiv-ev-falsify
                         (x term)
                         (a (equiv-ev-alist
                             (mv-nth 1 (term-unify-strict term pat nil))
                             a)))))))))



(define check-equiv-formula ((form pseudo-termp)
                             (e pseudo-fnsym-p))
  (and ;; (search-match-in-conjunction `(booleanp (,e x y)) form)
   (search-match-in-conjunction (pseudo-term-fncall e '(x x)) form)
   (search-match-in-conjunction `(implies ,(pseudo-term-fncall e '(x y))
                                          ,(pseudo-term-fncall e '(y x)))
                                form)
   (search-match-in-conjunction `(implies (if ,(pseudo-term-fncall e '(x y))
                                              ,(pseudo-term-fncall e '(y z))
                                            'nil)
                                          ,(pseudo-term-fncall e '(x z)))
                                form))
  ///

  ;; (local (defthm lemma1
  ;;          (implies (and (pseudo-termp form)
  ;;                        (equiv-ev-theoremp form)
  ;;                        (search-match-in-conjunction `(booleanp (,e x y)) form)
  ;;                        (symbolp e)
  ;;                        (not (equal e 'quote)))
  ;;                   (booleanp (equiv-ev (list e x y) a)))
  ;;          :hints (("goal" :in-theory (e/d (check-equiv-formula
  ;;                                           equiv-ev-of-fncall-args)
  ;;                                          (search-match-in-conjunction-correct))
  ;;                   :use ((:instance search-match-in-conjunction-correct
  ;;                          (term form) (pat `(booleanp (,e x y)))
  ;;                          (a `((x . ,(equiv-ev x a))
  ;;                               (y . ,(equiv-ev y a))
  ;;                               (z . ,(equiv-ev z a))))))))))

  ;; (local (defthm lemma2
  ;;          (implies (and (pseudo-termp form)
  ;;                        (equiv-ev-theoremp form)
  ;;                        (search-match-in-conjunction `(,e x x) form)
  ;;                        (symbolp e)
  ;;                        (not (equal e 'quote)))
  ;;                   (equiv-ev (list e x x) a))
  ;;          :hints (("goal" :in-theory (e/d (check-equiv-formula
  ;;                                           equiv-ev-of-fncall-args)
  ;;                                          (search-match-in-conjunction-correct))
  ;;                   :use ((:instance search-match-in-conjunction-correct
  ;;                          (term form) (pat `(,e x x))
  ;;                          (a `((x . ,(equiv-ev x a))
  ;;                               (y . ,(equiv-ev y a))
  ;;                               (z . ,(equiv-ev z a))))))))))

  ;; (local (defthm lemma3
  ;;          (implies (and (pseudo-termp form)
  ;;                        (equiv-ev-theoremp form)
  ;;                        (search-match-in-conjunction
  ;;                         `(implies (,e x y) (,e y x)) form)
  ;;                        (symbolp e)
  ;;                        (not (equal e 'quote))
  ;;                        (equiv-ev (list e x y) a))
  ;;                   (equiv-ev (list e y x) a))
  ;;          :hints (("goal" :in-theory (e/d (check-equiv-formula
  ;;                                           equiv-ev-of-fncall-args)
  ;;                                          (search-match-in-conjunction-correct))
  ;;                   :use ((:instance search-match-in-conjunction-correct
  ;;                          (term form) (pat `(implies (,e x y) (,e y x)))
  ;;                          (a `((x . ,(equiv-ev x a))
  ;;                               (y . ,(equiv-ev y a))
  ;;                               (z . ,(equiv-ev z a))))))))))

  ;; (local (defthm lemma4
  ;;          (implies (and (pseudo-termp form)
  ;;                        (equiv-ev-theoremp form)
  ;;                        (search-match-in-conjunction
  ;;                         `(implies (if (,e x y) (,e y z) 'nil) (,e x z)) form)
  ;;                        (symbolp e)
  ;;                        (not (equal e 'quote))
  ;;                        (equiv-ev (list e x y) a)
  ;;                        (equiv-ev (list e y z) a))
  ;;                   (equiv-ev (list e x z) a))
  ;;          :hints (("goal" :in-theory (e/d (check-equiv-formula
  ;;                                           equiv-ev-of-fncall-args)
  ;;                                          (search-match-in-conjunction-correct))
  ;;                   :use ((:instance search-match-in-conjunction-correct
  ;;                          (term form) (pat `(implies (if (,e x y) (,e y z) 'nil) (,e x z)))
  ;;                          (a `((x . ,(equiv-ev x a))
  ;;                               (y . ,(equiv-ev y a))
  ;;                               (z . ,(equiv-ev z a))))))))))

  (local (defthm cons-pseudo-fnsym-fix
           (implies (pseudo-term-listp y)
                    (equal (cons (pseudo-fnsym-fix x) y)
                           (pseudo-term-fncall x y)))
           :hints(("Goal" :in-theory (enable pseudo-term-fncall)))))

  (local (in-theory (disable equiv-ev-of-pseudo-term-fncall)))

  (local (defthm search-match-in-conjunction-correct-bind
           (implies (and 
                         (equiv-ev-theoremp term)
                         (bind-free `((a . a))))
                    (iff (search-match-in-conjunction pat term)
                         (and (hide (search-match-in-conjunction pat term))
                              (equiv-ev pat a))))
           :hints(("Goal" :in-theory (enable search-match-in-conjunction-correct)
                   :expand ((:free (x) (hide x)))))))
  
  (defthmd check-equiv-formula-correct
    (implies (and (check-equiv-formula form e)
                  (equiv-ev-theoremp form))
             (equiv-ev (equiv-rel-term e) a))
    :hints(("Goal" :in-theory (enable equiv-rel-term)))))

(local (in-theory (disable w)))

(define check-equiv-rule (rune
                          (e pseudo-fnsym-p)
                          (w plist-worldp))
    (b* ((rule (if (symbolp rune)
                   rune
                 (and (symbol-listp rune)
                      (cadr rune))))
         ((unless rule) nil)
         (form (acl2::meta-extract-formula-w rule w))
         ((unless (pseudo-termp form)) nil))
      (check-equiv-formula form e))
    ///
    (defthmd check-equiv-rule-correct
      (implies (and (check-equiv-rule rune e w)
                    (equiv-ev-meta-extract-global-facts)
                    (equal w (w state)))
               (equiv-ev (equiv-rel-term e) a))
      :hints(("Goal" :in-theory (e/d (check-equiv-formula-correct))))))



(define congruences-find-equiv-rule (congs
                                     (e pseudo-fnsym-p)
                                     (w plist-worldp))
    (b* (((when (atom congs)) nil)
         (cong (car congs))
         ((unless (and (acl2::weak-congruence-rule-p cong)
                       (eq (acl2::congruence-rule->equiv cong)
                           (pseudo-fnsym-fix e))))
          (congruences-find-equiv-rule (cdr congs) e w))
         (rune (acl2::congruence-rule->rune cong)))
      (or (check-equiv-rule rune e w)
          (congruences-find-equiv-rule (cdr congs) e w)))
    ///
    (defthmd congruences-find-equiv-rule-correct
      (implies (and (congruences-find-equiv-rule congs e w)
                    (equiv-ev-meta-extract-global-facts)
                    (equal w (w state)))
               (equiv-ev (equiv-rel-term e) a))
      :hints(("Goal" :in-theory (e/d (check-equiv-rule-correct))))))



(define ensure-equiv-relationp ((e pseudo-fnsym-p)
                                (w plist-worldp))
  (b* ((e (pseudo-fnsym-fix e))
       (coarsenings (getprop e 'acl2::coarsenings nil 'current-acl2-world w))
       ((unless coarsenings) nil)
       ;; shortcut: ACL2 always stores e as a coarsening of itself if it's an
       ;; equivalence relation.  In fact, it should only have coarsenings if it
       ;; is one.  But we don't get to assume that in meta-extract so we look
       ;; for a theorem stating it.
       (congruences (getprop e 'acl2::congruences nil 'current-acl2-world w))
       (equal-congs (cdr (hons-assoc-equal 'equal congruences)))
       (first-arg-congs (and (consp equal-congs) (car equal-congs))))
    (congruences-find-equiv-rule first-arg-congs e w))
  ///
  (defthmd ensure-equiv-relationp-correct
    (implies (and (equiv-ev-meta-extract-global-facts)
                  (ensure-equiv-relationp e (w state)))
             (equiv-ev (equiv-rel-term e) a))
    :hints(("Goal" :in-theory (enable congruences-find-equiv-rule-correct))
           (and stable-under-simplificationp
                '(:in-theory (enable equiv-relp))))
    :otf-flg t)

  (defthmd ensure-equiv-relationp-implies1
    (implies (and (equiv-ev-meta-extract-global-facts)
                  (ensure-equiv-relationp e (w state))
                  (pseudo-fnsym-p e))
             (and (equiv-ev (list e x x) a)
                  (implies (equiv-ev (list e x y) a)
                           (equiv-ev (list e y x) a))
                  (implies (and (equiv-ev (list e x y) a)
                                (equiv-ev (list e y z) a))
                           (equiv-ev (list e x z) a))))
    :hints(("Goal" :use ((:instance ensure-equiv-relationp-correct
                          (a (equiv-ev-falsify (equiv-rel-term e)))))
            :in-theory (e/d (equiv-rel-term-implies-reflexive
                             equiv-rel-term-implies-symmetric
                             equiv-rel-term-implies-transitive)
                            (ensure-equiv-relationp))))
    :otf-flg t)

  (fty::deffixequiv ensure-equiv-relationp)

  (defthmd ensure-equiv-relationp-implies2
    (implies (and (equiv-ev-meta-extract-global-facts)
                  (ensure-equiv-relationp e (w state)))
             (and (equiv-ev (pseudo-term-fncall e (list x x)) a)
                  (implies (equiv-ev (pseudo-term-fncall e (list x y)) a)
                           (equiv-ev (pseudo-term-fncall e (list y x)) a))
                  (implies (and (equiv-ev (pseudo-term-fncall e (list x y)) a)
                                (equiv-ev (pseudo-term-fncall e (list y z)) a))
                           (equiv-ev (pseudo-term-fncall e (list x z)) a))))
    :hints(("Goal" :in-theory (e/d (ensure-equiv-relationp-implies1)
                                   (ensure-equiv-relationp))))
    :otf-flg t))

