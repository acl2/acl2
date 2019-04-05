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

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "bindinglist")
(include-book "clause-processors/generalize" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "clause-processors/join-thms" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/take" :dir :system))
;; (local (include-book "std/alists/alist-equiv" :dir :system))

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(fty::defmap term-refcounts :key-type pseudo-termp :val-type posp :true-listp t)

(defines term-count-references
  (define term-count-references ((x pseudo-termp)
                                 (refcounts term-refcounts-p))
    :returns (new-refcounts term-refcounts-p)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (b* ((refcounts (term-refcounts-fix refcounts)))
      (pseudo-term-case x
        :const refcounts
        :var refcounts
        :call (b* ((x (pseudo-term-fix x))
                   (count (cdr (hons-get x refcounts)))
                   ((when count)
                    (hons-acons x (+ 1 count) refcounts))
                   (refcounts (hons-acons x 1 refcounts)))
                (termlist-count-references x.args refcounts)))))
  (define termlist-count-references ((x pseudo-term-listp)
                                     (refcounts term-refcounts-p))
    :returns (new-refcounts term-refcounts-p)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        (term-refcounts-fix refcounts)
      (termlist-count-references
       (cdr x)
       (term-count-references (car x) refcounts))))
  ///
  (verify-guards term-count-references)

  (defret-mutual term-count-references-vars-of-keys
    (defret term-count-references-vars-of-keys
      (implies (and (not (member v (term-vars x)))
                    (not (member v (termlist-vars (alist-keys (term-refcounts-fix refcounts))))))
               (not (member v (termlist-vars (alist-keys new-refcounts)))))
      :hints ('(:expand (<call>
                         (term-vars x)
                         (:free (x y) (termlist-vars (cons x y))))
                :in-theory (enable alist-keys)))
      :fn term-count-references)
    (defret termlist-count-references-vars-of-keys
      (implies (and (not (member v (termlist-vars x)))
                    (not (member v (termlist-vars (alist-keys (term-refcounts-fix refcounts))))))
               (not (member v (termlist-vars (alist-keys new-refcounts)))))
      :hints ('(:expand (<call>
                         (termlist-vars x))))
      :fn termlist-count-references)))


(defthm no-duplicate-keys-of-fast-alist-fork
  (implies (no-duplicatesp (alist-keys tail))
           (no-duplicatesp (alist-keys (fast-alist-fork x tail))))
  :hints(("Goal" :in-theory (enable fast-alist-fork alist-keys no-duplicatesp))))


(define collect-multiref-terms ((refcounts term-refcounts-p))
  :returns (terms pseudo-term-listp)
  :measure (len (term-refcounts-fix refcounts))
  (b* ((refcounts (term-refcounts-fix refcounts))
       ((when (atom refcounts)) nil)
       ((when (eql (cdar refcounts) 1))
        (collect-multiref-terms (cdr refcounts))))
    (cons (caar refcounts)
          (collect-multiref-terms (cdr refcounts))))
  ///
  (local (defthm consp-car-of-term-refcounts-fix-fwd
           (implies (consp (term-refcounts-fix x))
                    (consp (car (term-refcounts-fix x))))
           :rule-classes :forward-chaining))
  (defret member-collect-multiref-terms
    (implies (not (hons-assoc-equal x (term-refcounts-fix refcounts)))
             (not (member x terms)))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal)
                                   (hons-assoc-equal-of-term-refcounts-fix)))))
  (defret no-duplicatesp-of-collect-multiref-terms
    (implies (no-duplicatesp (alist-keys (term-refcounts-fix refcounts)))
             (no-duplicatesp terms))
    :hints(("Goal" :in-theory (enable alist-keys no-duplicatesp))))

  (defret member-vars-of-collect-multiref-terms
    (implies (not (member v (termlist-vars (alist-keys (term-refcounts-fix refcounts)))))
             (not (member v (termlist-vars terms))))
    :hints(("Goal" :in-theory (enable term-refcounts-fix alist-keys termlist-vars)))))

(fty::defmap letabs-varmap :key-type pseudo-termp :val-type pseudo-var :true-listp t)

(fty::defmap letabs-levels :key-type pseudo-termp :val-type natp :true-listp t)

(defines term-label-letabs-levels
  (define term-label-letabs-levels ((x pseudo-termp)
                                    (varmap letabs-varmap-p)
                                    (levels letabs-levels-p))
    :returns (mv (level natp :rule-classes :type-prescription)
                 (new-levels letabs-levels-p))
    :measure (pseudo-term-count x)
    :verify-guards nil
    (b* ((x (pseudo-term-fix x))
         (levels (letabs-levels-fix levels))
         ((unless (pseudo-term-case x :call)) (mv 0 levels))
         ((pseudo-term-call x))
         (varmap-look (hons-get x varmap))
         ((unless varmap-look)
          (termlist-label-letabs-levels x.args varmap levels))
         (look (cdr (hons-get x levels)))
         ((when look) (mv look levels))
         ((mv max levels) (termlist-label-letabs-levels x.args varmap levels)))
      (mv (+ 1 max) (hons-acons x (+ 1 max) levels))))

  (define termlist-label-letabs-levels ((x pseudo-term-listp)
                                        (varmap letabs-varmap-p)
                                        (levels letabs-levels-p))
    :returns (mv (level natp :rule-classes :type-prescription)
                 (new-levels letabs-levels-p))
    :measure (pseudo-term-list-count x)
    (b* (((when (atom x)) (mv 0 (letabs-levels-fix levels)))
         ((mv first levels) (term-label-letabs-levels (car x) varmap levels))
         ((mv rest levels) (termlist-label-letabs-levels (cdr x) varmap levels)))
      (mv (max first rest) levels)))
  ///
  (verify-guards term-label-letabs-levels))

(fty::defmap letabs-levelmap :key-type natp :val-type pseudo-term-listp :true-listp t)

(define letabs-sort-levels ((levels letabs-levels-p)
                            (levelmap letabs-levelmap-p))
  :returns (new-levelmap letabs-levelmap-p)
  :measure (len (letabs-levels-fix levels))
  (b* ((levels (letabs-levels-fix levels))
       (levelmap (letabs-levelmap-fix levelmap))
       ((when (atom levels)) levelmap)
       ((cons term level) (car levels))
       (levelmap (hons-acons level (cons term (cdr (hons-get level levelmap))) levelmap)))
    (letabs-sort-levels (cdr levels) levelmap)))

(local (defthm assoc-of-nonnil
         (implies k
                  (equal (assoc k x)
                         (hons-assoc-equal k x)))))


;; bozo
(fty::deffixtype alist :pred alistp :fix acl2::alist-fix :equiv alistp-equiv
  :define t :forward t)

(local (in-theory (disable acl2::commutativity-of-append-under-set-equiv)))

(local (defthm intersectp-of-append-2
         (implies (intersectp b x)
                  (intersectp (append a b) x))
         :hints(("Goal" :in-theory (enable intersectp)))))

(local (defthm intersectp-of-append-1
         (implies (intersectp a x)
                  (intersectp (append a b) x))
         :hints(("Goal" :in-theory (enable intersectp)))))

(local (defthm intersectp-single
         (iff (intersectp (list a) x)
              (member a x))
         :hints(("Goal" :in-theory (enable intersectp)))))

;; (local (defthm intersectp-of-append-2-right
;;          (implies (intersectp x b)
;;                   (intersectp x (append a b)))
;;          :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

;; (local (defthm intersectp-of-append-1-right
;;          (implies (intersectp x a)
;;                   (intersectp x (append a b)))
;;          :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))


(defines term-let-abstract
  (define term-let-abstract ((x pseudo-termp)
                             (varmap letabs-varmap-p))
    :returns (new-x pseudo-termp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (b* ((x (pseudo-term-fix x))
         (varmap (letabs-varmap-fix varmap))
         ((unless (pseudo-term-case x :call)) x)
         (varmap-look (hons-get x varmap))
         ((when varmap-look) (pseudo-term-var (cdr varmap-look)))
         ((pseudo-term-call x)))
      (pseudo-term-call x.fn
                        (termlist-let-abstract x.args varmap))))
  (define termlist-let-abstract ((x pseudo-term-listp)
                                 (varmap letabs-varmap-p))
    :returns (new-x pseudo-term-listp)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        nil
      (cons (term-let-abstract (car x) varmap)
            (termlist-let-abstract (cdr x) varmap))))
  ///
  (defret len-of-termlist-let-abstract
    (equal (len new-x) (len x))
    :hints(("Goal" :in-theory (enable len)
            :induct (len x)
            :expand (<call>)))
    :fn termlist-let-abstract)
  (verify-guards term-let-abstract)

  (defun-sk letabs-env-mapped-vars-ok (env a varmap)
    (forall term
            (implies (and (pseudo-termp term)
                          (hons-assoc-equal term varmap))
                     (equal (cdr (hons-assoc-equal
                                  (pseudo-var-fix (cdr (hons-assoc-equal term varmap)))
                                  env))
                            (base-ev term a))))
    :rewrite :direct)

  (in-theory (disable letabs-env-mapped-vars-ok))

  (fty::deffixcong letabs-varmap-equiv equal (letabs-env-mapped-vars-ok env a varmap) varmap
    :hints (("goal" :expand ((:free (varmap) (letabs-env-mapped-vars-ok env a varmap)))
             :use ((:instance letabs-env-mapped-vars-ok-necc
                    (varmap varmap)
                    (term (letabs-env-mapped-vars-ok-witness env a (letabs-varmap-fix varmap))))
                   (:instance letabs-env-mapped-vars-ok-necc
                    (varmap  (letabs-varmap-fix varmap))
                    (term (letabs-env-mapped-vars-ok-witness env a varmap))))
             :in-theory (disable letabs-env-mapped-vars-ok-necc))))

  (fty::deffixcong alistp-equiv equal (letabs-env-mapped-vars-ok env a varmap) a
    :hints (("goal" :expand ((:free (a) (letabs-env-mapped-vars-ok env a varmap)))
             :use ((:instance letabs-env-mapped-vars-ok-necc
                    (a a)
                    (term (letabs-env-mapped-vars-ok-witness env (acl2::alist-fix a) varmap)))
                   (:instance letabs-env-mapped-vars-ok-necc
                    (a (acl2::alist-fix a))
                    (term (letabs-env-mapped-vars-ok-witness env a varmap))))
             :in-theory (disable letabs-env-mapped-vars-ok-necc))))

  ;; (defun-sk letabs-env-unmapped-vars-ok (env a vars)
  ;;   (forall var
  ;;           (implies (and (pseudo-var-p var)
  ;;                         (member var vars))
  ;;                    (equal (cdr (hons-assoc-equal var env))
  ;;                           (cdr (hons-assoc-equal var a)))))
  ;;   :rewrite :direct)

  ;; (in-theory (disable letabs-env-unmapped-vars-ok
  ;;                     letabs-env-unmapped-vars-ok-necc))
  ;; (local (in-theory (enable letabs-env-unmapped-vars-ok-necc)))

  ;; (defret-mutual base-ev-of-term-let-abstract
  ;;   (defret base-ev-of-term-let-abstract
  ;;     (implies (and (letabs-env-mapped-vars-ok env a varmap)
  ;;                   (letabs-env-unmapped-vars-ok env a vars)
  ;;                   (subsetp (term-vars x) vars))
  ;;              (equal (base-ev new-x env)
  ;;                     (base-ev x a)))
  ;;     :hints ('(:expand (<call>
  ;;                        (term-vars x))
  ;;               :in-theory (enable acl2::base-ev-when-pseudo-term-fncall
  ;;                                  acl2::base-ev-of-fncall-args)
  ;;               :do-not-induct t))
  ;;     :fn term-let-abstract)
  ;;   (defret base-ev-list-of-termlist-let-abstract
  ;;     (implies (and (letabs-env-mapped-vars-ok env a varmap)
  ;;                   (letabs-env-unmapped-vars-ok env a vars)
  ;;                   (subsetp (termlist-vars x) vars))
  ;;              (equal (base-ev-list new-x env)
  ;;                     (base-ev-list x a)))
  ;;     :hints ('(:expand (<call>
  ;;                        (termlist-vars x))))
  ;;     :fn termlist-let-abstract))


  (defun-sk letabs-env-unmapped-vars-ok (env a varmap)
    (forall var
            (implies (and (pseudo-var-p var)
                          (not (member var (alist-vals (letabs-varmap-fix varmap)))))
                     (equal (cdr (hons-assoc-equal var env))
                            (cdr (hons-assoc-equal var a)))))
    :rewrite :direct)

  (in-theory (disable letabs-env-unmapped-vars-ok
                      letabs-env-unmapped-vars-ok-necc))
  (local (in-theory (enable letabs-env-unmapped-vars-ok-necc)))

  (fty::deffixcong letabs-varmap-equiv equal (letabs-env-unmapped-vars-ok env a varmap) varmap
    :hints (("goal" :expand ((:free (varmap) (letabs-env-unmapped-vars-ok env a varmap)))
             :use ((:instance letabs-env-unmapped-vars-ok-necc
                    (varmap varmap)
                    (var (letabs-env-unmapped-vars-ok-witness env a (letabs-varmap-fix varmap))))
                   (:instance letabs-env-unmapped-vars-ok-necc
                    (varmap  (letabs-varmap-fix varmap))
                    (var (letabs-env-unmapped-vars-ok-witness env a varmap))))
             :in-theory (disable letabs-env-unmapped-vars-ok-necc))))

  (defret-mutual base-ev-of-term-let-abstract
    (defret base-ev-of-term-let-abstract
      (implies (and (letabs-env-mapped-vars-ok env a varmap)
                    (letabs-env-unmapped-vars-ok env a varmap)
                    (not (intersectp (term-vars x) (alist-vals (letabs-varmap-fix varmap)))))
               (equal (base-ev new-x env)
                      (base-ev x a)))
      :hints ('(:expand (<call>
                         (term-vars x))
                :in-theory (enable acl2::base-ev-when-pseudo-term-fncall
                                   acl2::base-ev-of-fncall-args)
                :do-not-induct t))
      :fn term-let-abstract)
    (defret base-ev-list-of-termlist-let-abstract
      (implies (and (letabs-env-mapped-vars-ok env a varmap)
                    (letabs-env-unmapped-vars-ok env a varmap)
                    (not (intersectp (termlist-vars x) (alist-vals (letabs-varmap-fix varmap)))))
               (equal (base-ev-list new-x env)
                      (base-ev-list x a)))
      :hints ('(:expand (<call>
                         (termlist-vars x))))
      :fn termlist-let-abstract))
  )


(define letabs-terms-get-vars ((terms pseudo-term-listp)
                               (varmap letabs-varmap-p))
  :returns (vars symbol-listp)
  (if (atom terms)
      nil
    (cons (cdr (hons-get (pseudo-term-fix (car terms))
                         (letabs-varmap-fix varmap)))
          (letabs-terms-get-vars (cdr terms) varmap))))


(defthm letabs-varmap-p-of-pairlis$
  (implies (and (pseudo-term-listp keys)
                (pseudo-var-list-p vals)
                (>= (len vals) (len keys)))
           (letabs-varmap-p (pairlis$ keys vals))))





(local (defthm pseudo-var-list-p-of-append
         (implies (and (pseudo-var-list-p x)
                       (pseudo-var-list-p y))
                  (pseudo-var-list-p (append x y)))))

(define letabs-levelmap-vars ((x letabs-levelmap-p))
  :returns (vars pseudo-var-list-p)
  (if (atom x)
      nil
    (append (and (mbt (and (consp (car x))
                           (natp (caar x))))
                 (termlist-vars (cdar x)))
            (letabs-levelmap-vars (cdr x))))
  ///
  (defthm member-termlist-vars-of-lookup-in-letabs-levelmap-vars
    (implies (and (not (member v (letabs-levelmap-vars x)))
                  (natp k))
             (not (member v (termlist-vars (cdr (hons-assoc-equal k x))))))))

;; (local (include-book "std/alists/fast-alist-clean" :dir :system))



(define fal-append ((x alistp) (y alistp))
  :enabled t
  (mbe :logic (append x y)
       :exec (if (endp x)
                 y
               (hons-acons (caar x) (cdar x)
                           (fal-append (cdr x) y)))))

;; (local (defthm letabs-varmap-p-of-append
;;          (implies (And (letabs-varmap-p x)
;;                        (letabs-varmap-p y))
;;                   (letabs-varmap-p (append x y)))))



(local (defthm alistp-of-pairlis$
         (alistp (pairlis$ x y))
         :hints(("Goal" :in-theory (enable pairlis$)))))


(local (defthm intersectp-member
         (implies (and (not (intersectp x y))
                       (member k y))
                  (not (member k x)))
         :hints(("Goal" :in-theory (enable intersectp)))))

(local (defthmd not-intersectp-when-not-intersectp-with-superset
         (implies (and (not (intersectp x z))
                       (subsetp y z))
                  (not (intersectp x y)))
         :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

(local (defthmd intersectp-commutes
         (implies (intersectp a b)
                  (intersectp b a))
         :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

(local (defthmd intersectp-commutes-neg
         (implies (not (intersectp a b))
                  (not (intersectp b a)))
         :hints(("Goal" :in-theory (enable intersectp-commutes)))))

(local (defthm member-alist-vals-when-subsetp
         (implies (and (subsetp y x)
                       (member k (alist-vals y)))
                  (member k (alist-vals x)))
         :hints(("Goal" :in-theory (enable subsetp alist-vals)))))

(local (defthmd subsetp-alist-vals-when-subsetp
         (implies (subsetp y x)
                  (subsetp (alist-vals y) (alist-vals x)))
         :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))


(define letabs-abstract-levels ((level natp)
                                (levelmap letabs-levelmap-p)
                                (full-varmap letabs-varmap-p))
  :returns (mv (bindinglist bindinglist-p)
               (partial-varmap letabs-varmap-p))
  :verify-guards nil

  :prepwork ()
  (b* (((when (zp level)) (mv nil nil))
       (terms (cdr (hons-get (1- level) (letabs-levelmap-fix levelmap))))
       ((mv bindinglist partial-varmap)
        (letabs-abstract-levels (1- level) levelmap full-varmap))
       (abs-terms (termlist-let-abstract terms partial-varmap))
       (term-vars (letabs-terms-get-vars terms full-varmap))
       (found-term-vars (remove-non-pseudo-vars term-vars))
       ((when (atom found-term-vars))
        (mv bindinglist partial-varmap))
       (found-abs-terms (remove-corresp-non-pseudo-vars term-vars abs-terms))
       (found-orig-terms (remove-corresp-non-pseudo-vars term-vars terms))
       (binding (binding found-term-vars
                         found-abs-terms)))
    (mv (cons binding bindinglist)
        (fal-append (pairlis$ found-orig-terms found-term-vars) partial-varmap)))
  ///
  (verify-guards letabs-abstract-levels)

  (local (in-theory (disable (:d letabs-abstract-levels)
                             intersection-equal
                             hons-assoc-equal
                             pairlis$)))

  

  (local (defthm hons-assoc-equal-of-nil
           (equal (hons-assoc-equal k nil) nil)
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))
                                          
  (local
   (defthm remove-corresp-non-pseudo-vars-of-letabs-terms-get-vars
     (implies (pseudo-term-listp terms)
              (equal (remove-corresp-non-pseudo-vars (letabs-terms-get-vars terms varmap) terms)
                     (intersection$ terms (alist-keys (letabs-varmap-fix varmap)))))
     :hints(("Goal" :in-theory (enable remove-corresp-non-pseudo-vars letabs-terms-get-vars
                                       intersection$)))))

  (local (defthm len-remove-non-pseudo-vars-of-letabs-terms-get-vars
           (implies (pseudo-term-listp terms)
                    (equal (len (remove-non-pseudo-vars (letabs-terms-get-vars terms varmap)))
                           (len (intersection$ terms (alist-keys (letabs-varmap-fix varmap))))))
           :hints(("Goal" :in-theory (enable remove-non-pseudo-vars letabs-terms-get-vars
                                             intersection$)))))

  (local (defthm not-member-alist-vals-implies-not-equal-lookup
           (implies (and (not (member v (alist-vals x)))
                         (hons-assoc-equal k x))
                    (not (equal v (cdr (hons-assoc-equal k x)))))
           :hints(("Goal" :in-theory (enable alist-vals hons-assoc-equal)))))

  (local (defthmd lookup-when-no-duplicate-vals
           (implies (and (no-duplicatesp (alist-vals x))
                         (hons-assoc-equal a x)
                         (hons-assoc-equal b x))
                    (equal (equal (cdr (hons-assoc-equal a x))
                                  (cdr (hons-assoc-equal b x)))
                           (equal a b)))
           :hints(("Goal" :in-theory (enable alist-vals hons-assoc-equal)))))

  (local (defthm alist-fix-of-append
           (equal (acl2::alist-fix (append a b))
                  (append (acl2::alist-fix a)
                          (acl2::alist-fix b)))))

  (local (defthm base-ev-bindinglist-of-append
           (equal (base-ev-bindinglist (append bindings (list b)) a)
                  (let ((rest (base-ev-bindinglist bindings a)))
                    (append (pairlis$ (binding->formals b)
                                      (base-ev-list (binding->args b) rest))
                            rest)))
           :hints(("Goal" :in-theory (enable base-ev-bindinglist)))))
                  

  (local (defthm hons-assoc-equal-of-fast-alist-fork
           (equal (hons-assoc-equal k (fast-alist-fork x y))
                  (or (hons-assoc-equal k y)
                      (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (defthm hons-assoc-equal-of-append
           (equal (hons-assoc-equal k (append x y))
                  (or (hons-assoc-equal k x)
                      (hons-assoc-equal k y)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (defthm hons-assoc-equal-of-pairlis$-under-iff
           (implies (equal (len keys) (len vals))
                    (iff (hons-assoc-equal k (pairlis$ keys vals))
                         (member k keys)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal pairlis$)))))

  (local (defthm len-of-base-ev-list
           (equal (len (base-ev-list x a))
                  (len x))
           :hints(("Goal" :in-theory (enable len)))))
  

  (local (defthm lookup-in-pairlis-base-ev-list
           (implies (member k x)
                    (equal (cdr (hons-assoc-equal k (pairlis$ x (base-ev-list y a))))
                           (base-ev (cdr (hons-assoc-equal k (pairlis$ x y))) a)))
           :hints(("Goal" :in-theory (enable pairlis$ hons-assoc-equal)))))

  (local (defthm lookup-in-pair-remove-corresp-non-pseudo-vars-of-terms-get-vars
           (b* ((term-vars (letabs-terms-get-vars terms varmap))
                (keys (intersection$ terms (alist-keys (letabs-varmap-fix varmap))))
                (vals (remove-non-pseudo-vars term-vars)))
             (implies (and (member w keys)
                           (pseudo-term-listp terms))
                      (equal (hons-assoc-equal w (pairlis$ keys vals))
                             (hons-assoc-equal w (letabs-varmap-fix varmap)))))
           :hints(("Goal" :in-theory (e/d (remove-corresp-non-pseudo-vars
                                             remove-non-pseudo-vars
                                             pairlis$ hons-assoc-equal
                                             intersection$)
                                          (pseudo-term-listp
                                           pseudo-termp))
                   :induct (len terms)
                   :expand ((letabs-terms-get-vars terms varmap))))))

  (local (defthm lookup-is-member-of-alist
           (implies (and (hons-assoc-equal k x)
                         (equal val (cdr (hons-assoc-equal k x))))
                    (member (cons k val) x))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (defthm pair-remove-corresp-non-pseudo-vars-of-terms-get-vars-is-subset
           (b* ((term-vars (letabs-terms-get-vars terms varmap))
                (keys (intersection$ terms (alist-keys (letabs-varmap-fix varmap))))
                (vals (remove-non-pseudo-vars term-vars)))
             (implies (pseudo-term-listp terms)
                      (subsetp (pairlis$ keys vals) (letabs-varmap-fix varmap))))
           :hints(("Goal" :in-theory (e/d (remove-corresp-non-pseudo-vars
                                             remove-non-pseudo-vars
                                             pairlis$ hons-assoc-equal
                                             intersection$)
                                          (pseudo-term-listp
                                           pseudo-termp))
                   :induct (len terms)
                   :expand ((letabs-terms-get-vars terms varmap))))))

  (local (defthm subsetp-hons-assoc-equal
           (implies (and (subsetp a b)
                         (no-duplicatesp (alist-keys b))
                         (hons-assoc-equal x a))
                    (equal (hons-assoc-equal x b)
                           (hons-assoc-equal x a)))
           :hints(("Goal" :in-theory (enable subsetp hons-assoc-equal alist-keys)))))

  (local (defthm subsetp-implies-not-lookup
           (implies (and (subsetp a b)
                         (not (hons-assoc-equal x b)))
                    (not (hons-assoc-equal x a)))
           :hints(("Goal" :in-theory (enable subsetp hons-assoc-equal)))))

  (local (defthm subsetp-implies-lookup
           (implies (and (subsetp a b)
                         (hons-assoc-equal x a))
                    (hons-assoc-equal x b))
           :hints(("Goal" :in-theory (enable subsetp hons-assoc-equal)))))

  (local (defthm subsetp-of-fast-alist-fork
           (implies (and (subsetp a x)
                         (subsetp b x))
                    (subsetp (fast-alist-fork a b) x))
           :hints(("Goal" :in-theory (enable fast-alist-fork)))))
                
  (local (defthm intersection-of-nil
           (equal (intersection$ nil x) nil)
           :hints(("Goal" :in-theory (enable intersection$)))))

  (local (defthm pairlis$-of-nil
           (equal (pairlis$ nil x) nil)
           :hints(("Goal" :in-theory (enable pairlis$)))))


  (defret letabs-abstract-levels-partial-varmap-is-subsetp
    (subsetp partial-varmap (letabs-varmap-fix full-varmap))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable hons-assoc-equal
                                subsetp-hons-assoc-equal))))

  (local (defthm equal-pseudo-var-fix-of-lookup-when-no-duplicatesp
           (implies (and (no-duplicatesp (alist-vals (letabs-varmap-fix x)))
                         (hons-assoc-equal a x)
                         (hons-assoc-equal b x)
                         (pseudo-termp a) (pseudo-termp b))
                    (equal (equal (pseudo-var-fix (cdr (hons-assoc-equal a x)))
                                  (pseudo-var-fix (cdr (hons-assoc-equal b x))))
                           (equal a b)))
           :hints (("goal" :use ((:instance lookup-when-no-duplicate-vals
                                  (x (letabs-varmap-fix x))))))))

  (local (defthm lookup-in-pairlis$-termlist-let-abstract
           (implies (member w keys)
                    (equal (hons-assoc-equal w (pairlis$ keys (termlist-let-abstract terms varmap)))
                           (cons w (term-let-abstract (cdr (hons-assoc-equal w (pairlis$ keys terms))) varmap))))
           :hints(("Goal" :in-theory (enable termlist-let-abstract pairlis$ hons-assoc-equal)
                   :induct (pairlis$ keys terms)
                   :expand ((:free (terms) (pairlis$ keys terms))
                            (termlist-let-abstract terms varmap)
                            (term-let-abstract nil varmap))))))

  (local (defthm rassoc-of-assoc-when-no-duplicate-vals
           (implies (and (no-duplicatesp (alist-vals x))
                         (hons-assoc-equal k x))
                    (equal (acl2::hons-rassoc-equal (cdr (hons-assoc-equal k x)) x)
                           (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal alist-vals
                                             hons-assoc-equal)))))

  (local (defthm rassoc-of-assoc-when-no-duplicate-vals-sub-alist
           (implies (and (no-duplicatesp (alist-vals x))
                         (no-duplicatesp (alist-keys x))
                         (subsetp y x)
                         (hons-assoc-equal k y))
                    (equal (acl2::hons-rassoc-equal (cdr (hons-assoc-equal k y)) x)
                           (hons-assoc-equal k y)))
           :hints(("Goal" :use ((:instance rassoc-of-assoc-when-no-duplicate-vals))
                   :in-theory (e/d (subsetp-hons-assoc-equal)
                                   (rassoc-of-assoc-when-no-duplicate-vals))))))

  (local (defthm car-hons-assoc-equal
           (implies (hons-assoc-equal k x)
                    (equal (car (hons-assoc-equal k x)) k))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (defthm rassoc-of-assoc-when-no-duplicate-vals-letabs-varmap-fix
           (implies (and (no-duplicatesp (alist-vals (letabs-varmap-fix x)))
                         (hons-assoc-equal k x)
                         (pseudo-termp k))
                    (equal (acl2::hons-rassoc-equal
                            (pseudo-var-fix (cdr (hons-assoc-equal k x)))
                            (letabs-varmap-fix x))
                           (hons-assoc-equal k (letabs-varmap-fix x))))
           :hints (("goal" :use ((:instance rassoc-of-assoc-when-no-duplicate-vals
                                  (x (letabs-varmap-fix x))))))))

  (local (defthm lookup-in-pairlis$-letabs-terms-get-vars
           (implies (and (member w (letabs-terms-get-vars terms varmap))
                         (no-duplicatesp (alist-vals (letabs-varmap-fix varmap)))
                         (pseudo-term-listp terms)
                         (pseudo-var-p w))
                    (equal (hons-assoc-equal w (pairlis$ (letabs-terms-get-vars terms varmap)
                                                         terms))
                           (cons w (car (acl2::hons-rassoc-equal w (letabs-varmap-fix varmap))))))
           :hints(("Goal" :in-theory (enable letabs-terms-get-vars pairlis$ rassoc
                                             hons-assoc-equal)))))



  (local (defthm pseudo-var-p-when-member-of-pseudo-var-list
           (implies (and (member k x)
                         (pseudo-var-list-p x))
                    (pseudo-var-p k))))


  (local (defthm letabs-env-mapped-vars-ok-when-letabs-varmap-p
           (implies (and (letabs-env-mapped-vars-ok env a varmap)
                         (pseudo-termp term)
                         (hons-assoc-equal term varmap)
                         (letabs-varmap-p varmap))
                    (equal (cdr (hons-assoc-equal
                                 (cdr (hons-assoc-equal term varmap))
                                 env))
                           (base-ev term a)))
           :hints (("goal" :use letabs-env-mapped-vars-ok-necc
                    :in-theory (disable letabs-env-mapped-vars-ok-necc)))))

  (local (Defthm member-remove-non-pseudo-vars
           (iff (member x (remove-non-pseudo-vars y))
                (and (pseudo-var-p x)
                     (member x y)))
           :hints(("Goal" :in-theory (enable remove-non-pseudo-vars)))))

  (local (defthm subsetp-term-vars-of-alist-keys-vars-when-lookup
           (implies (hons-assoc-equal w x)
                    (subsetp-equal (term-vars w) (termlist-vars (alist-keys x))))
           :hints(("Goal" :in-theory (enable alist-keys termlist-vars
                                             hons-assoc-equal)))))

  (local (defthm subsetp-term-vars-of-alist-keys-car-of-rassoc
           (implies (acl2::hons-rassoc-equal w x)
                    (subsetp-equal (term-vars (car (acl2::hons-rassoc-equal w x)))
                                   (termlist-vars (alist-keys x))))
           :hints(("Goal" :in-theory (enable alist-keys termlist-vars
                                             acl2::hons-rassoc-equal)))))

  (local (defthm subsetp-term-vars-of-alist-keys-vars-when-lookup-in-sub-alist
           (implies (and (hons-assoc-equal w x)
                         (subsetp x y))
                    (subsetp-equal (term-vars w) (termlist-vars (alist-keys y))))
           :hints(("Goal" :use ((:instance subsetp-term-vars-of-alist-keys-vars-when-lookup
                                 (x y)))
                   :in-theory (disable subsetp-term-vars-of-alist-keys-vars-when-lookup)))))


  (local (defthm member-of-letabs-terms-get-vars
           (implies (and (pseudo-termp w)
                         (hons-assoc-equal w full-varmap)
                         (no-duplicatesp (alist-vals (letabs-varmap-fix full-varmap))))
                    (iff (MEMBER-EQUAL
                          (PSEUDO-VAR-FIX (CDR (HONS-ASSOC-EQUAL W FULL-VARMAP)))
                          (LETABS-TERMS-GET-VARS terms FULL-VARMAP))
                         (member w (pseudo-term-list-fix terms))))
           :hints(("Goal" :in-theory (enable letabs-terms-get-vars)))))


  (local (defthm pseudo-termp-car-rassoc
           (implies (and (letabs-varmap-p x)
                         (acl2::hons-rassoc-equal k x))
                    (pseudo-termp (car (acl2::hons-rassoc-equal k x))))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal)))))

  (local (defthm hons-assoc-equal-of-car-rassoc
           (implies (acl2::hons-rassoc-equal k x)
                    (hons-assoc-equal (car (acl2::hons-rassoc-equal k x)) x))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal
                                             hons-assoc-equal)))))

  (local (defthm hons-assoc-equal-of-car-rassoc-letabs-varmap-fix
           (implies (acl2::hons-rassoc-equal k (letabs-varmap-fix x))
                    (hons-assoc-equal (car (acl2::hons-rassoc-equal k (letabs-varmap-fix x))) x))
           :hints (("goal" :use ((:instance hons-assoc-equal-of-car-rassoc
                                  (x (letabs-varmap-fix x))))
                    :in-theory (disable hons-assoc-equal-of-car-rassoc)))))

  (local (defthm assoc-of-rassoc-when-no-duplicate-keys
           (implies (and (no-duplicatesp (alist-keys x))
                         (acl2::hons-rassoc-equal k x))
                    (equal (hons-assoc-equal (car (acl2::hons-rassoc-equal k x)) x)
                           (acl2::hons-rassoc-equal k x)))
           :hints(("Goal" :in-theory (enable alist-keys acl2::hons-rassoc-equal
                                             hons-assoc-equal)))))

  (local (defthm cdr-of-hons-rassoc-equal
           (implies (acl2::hons-rassoc-equal k x)
                    (equal (cdr (acl2::hons-rassoc-equal k x)) k))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal)))))


  (local (defthm rassoc-of-cdr-assoc
           (implies (hons-assoc-equal k x)
                    (acl2::hons-rassoc-equal (cdr (hons-assoc-equal k x)) x))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal
                                             hons-assoc-equal)))))

  (local (defthm rassoc-of-cdr-assoc-letabs-varmap-fix
           (implies (and (hons-assoc-equal k x)
                         (pseudo-termp k)) 
                    (acl2::hons-rassoc-equal (pseudo-var-fix (cdr (hons-assoc-equal k x)))
                                             (letabs-varmap-fix x)))
           :hints (("goal" :use ((:instance rassoc-of-cdr-assoc (x (letabs-varmap-fix x))))))))

  (local (defthm rassoc-when-member-letabs-terms-get-vars
           (implies (and (pseudo-var-p w)
                         (member w (letabs-terms-get-vars terms full-varmap)))
                    (acl2::hons-rassoc-equal w (letabs-varmap-fix full-varmap)))
           :hints(("Goal" :in-theory (enable letabs-terms-get-vars)))))

  (local (in-theory (enable letabs-env-unmapped-vars-ok-necc)))

  (local (Defthm member-alist-vals-pseudo-var-fix-of-lookup
           (implies (and (hons-assoc-equal k x)
                         (pseudo-termp k))
                    (member (pseudo-var-fix (cdr (hons-assoc-equal k x)))
                            (alist-vals (letabs-varmap-fix x))))
           :hints(("Goal" :in-theory (enable letabs-varmap-fix
                                             hons-assoc-equal
                                             alist-vals)))))


  (local (defthm not-member-letabs-terms-get-vars-when-not-member-alist-vals
           (implies (and (not (member v (alist-vals (letabs-varmap-fix full-varmap))))
                         (pseudo-var-p v))
                    (not (member v (letabs-terms-get-vars terms full-varmap))))
           :hints(("Goal" :in-theory (enable letabs-terms-get-vars)))))

  (local (Defthm hons-rassoc-equal-of-append
           (equal (acl2::hons-rassoc-equal k (append x y))
                  (or (acl2::hons-rassoc-equal k x)
                      (acl2::hons-rassoc-equal k y)))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal)))))

  (local (defthm intersectp-open-cons-left
           (iff (intersectp (cons a b) x)
                (or (member a x) (intersectp b x)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (defthm intersectp-open-cons-right
           (iff (intersectp x (cons a b))
                (or (member a x) (intersectp x b)))
           :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

  (local (defthm intersectp-open-append-left
           (iff (intersectp (append a b) x)
                (or (intersectp a x) (intersectp b x)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (defthm intersectp-open-append-right
           (iff (intersectp x (append a b))
                (or (intersectp x a) (intersectp x b)))
           :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

           

  (local (defthm not-intersectp-vars-of-lookup-in-letabs-varmap
           (implies (and (not (intersectp (alist-vals x) (termlist-vars (alist-keys x))))
                         (letabs-varmap-p x)
                         (hons-assoc-equal w x))
                    (not (intersectp (term-vars w)
                                     (alist-vals x))))
           :hints(("Goal" :in-theory (enable alist-keys alist-vals hons-assoc-equal
                                             termlist-vars)
                   :induct (len x))
                  (and stable-under-simplificationp
                       '(:in-theory (enable intersectp-commutes))))))

  (local (in-theory (enable subsetp-alist-vals-when-subsetp)))

  (local (defthm member-termlist-vars-of-keys-when-subsetp
           (implies (and (subsetp y x)
                         (member k (termlist-vars (alist-keys y))))
                    (member k (termlist-vars (alist-keys x))))
           :hints(("Goal" :in-theory (enable subsetp alist-keys termlist-vars)))))

  (local (defthm subsetp-termlist-vars-of-keys-when-subsetp
           (implies (subsetp y x)
                    (subsetp (termlist-vars (alist-keys y))
                             (termlist-vars (alist-keys x))))
           :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))

  (local (defthmd not-intersectp-implies-member
           (implies (and (not (intersectp x y))
                         (member k x))
                    (not (member k y)))
           :hints(("Goal" :in-theory (enable intersectp)))))
                    

  (local (defthm not-intersectp-vals-and-key-vars-when-subsetp
           (implies (and (not (intersectp (alist-vals x) (termlist-vars (alist-keys x))))
                         (letabs-varmap-p x)
                         (letabs-varmap-p y)
                         (subsetp y x))
                    (not (intersectp (alist-vals y) (termlist-vars (alist-keys y)))))
           :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)
                   :use ((:instance not-intersectp-implies-member
                          (x (alist-vals x)) (y (termlist-vars (alist-keys x)))
                          (k (acl2::intersectp-witness (alist-vals y) (termlist-vars (alist-keys y))))))))))

  (local (defthm not-intersectp-vars-of-lookup-in-letabs-varmap-subset
           (implies (and (not (intersectp (alist-vals x) (termlist-vars (alist-keys x))))
                         (subsetp y x)
                         (letabs-varmap-p x)
                         (letabs-varmap-p y)
                         (hons-assoc-equal w x))
                    (not (intersectp (term-vars w)
                                     (alist-vals y))))
           :hints (("goal" :in-theory (enable acl2::intersectp-witness-rw)
                    :use ((:instance not-intersectp-implies-member
                           (x (alist-vals x)) (y (termlist-vars (alist-keys x)))
                           (k (acl2::intersectp-witness (term-vars w) (alist-vals y)))))))))


  (local (defthm letabs-varmap-fix-of-fast-alist-fork
           (equal (letabs-varmap-fix (fast-alist-fork x y))
                  (fast-alist-fork (letabs-varmap-fix x) (letabs-varmap-fix y)))
           :hints(("Goal" :in-theory (enable fast-alist-fork letabs-varmap-fix)))))

  (local (Defthm member-alist-vals
           (iff (member k (alist-vals x))
                (acl2::hons-rassoc-equal k x))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal alist-vals)))))

  (local (defthm pseudo-term-listp-of-intersection
           (implies (pseudo-term-listp x)
                    (pseudo-term-listp (intersection$ x y)))
           :hints(("Goal" :in-theory (enable intersection$)))))

   ;; differs from the one in std/alists/fast-alist-clean
  ;; (local (defun hons-remove-assocs (keys x)
  ;;          (if (atom x)
  ;;              nil
  ;;            (if (and (consp (car x))
  ;;                     (not (member (caar x) keys)))
  ;;                (cons (car x) (hons-remove-assocs (cdr x)))
  ;;              (hons-remove-assocs keys (cdr x))))))

  ;; (local
  ;;  #!acl2
  ;;  (defthm hons-remove-assocs-when-consp-alist
  ;;    (implies (consp a)
  ;;             (equal (hons-remove-assocs keys a)
  ;;                    (if (and (consp (car a))
  ;;                             (not (member (caar a) keys)))
  ;;                        (cons (car a)
  ;;                              (hons-remove-assocs keys (cdr a)))
  ;;                      (hons-remove-assocs keys (cdr a)))))
  ;;    :hints(("Goal" :in-theory (enable hons-remove-assocs hons-remove-assoc)))))

  ;; (local (defthm fast-alist-fork-is-hons-remove-assocs
  ;;          (equal (fast-alist-fork x y)
  ;;                 (append (acl2::rev (acl2::hons-remove-assocs (alist-keys y) x)) y))
  ;;          :hints(("Goal" :in-theory (enable fast-alist-fork acl2::hons-remove-assocs acl2::rev
  ;;                                            )))))

  (local (Defthm hons-rassoc-equal-of-pairlis$-under-iff
           (implies (equal (len x) (len y))
                    (iff (acl2::hons-rassoc-equal k (pairlis$ x y))
                         (member k y)))
           :hints(("Goal" :in-theory (enable acl2::hons-rassoc-equal pairlis$)))))

  (local (Defthm letabs-terms-get-vars-of-nil
           (equal (letabs-terms-get-vars nil varmap) nil)
           :hints(("Goal" :in-theory (enable letabs-terms-get-vars)))))

  (defret letabs-abstract-levels-correct
    (implies (and (no-duplicatesp (alist-vals (letabs-varmap-fix full-varmap)))
                  (no-duplicatesp (alist-keys (letabs-varmap-fix full-varmap)))
                  (not (intersectp (alist-vals (letabs-varmap-fix full-varmap))
                                   (termlist-vars (alist-keys (letabs-varmap-fix full-varmap))))))
             (b* ((env (base-ev-bindinglist (acl2::rev bindinglist) a)))
               (and (letabs-env-mapped-vars-ok env a partial-varmap)
                    (letabs-env-unmapped-vars-ok env a partial-varmap))))
    :hints (("goal" :induct <call> :in-theory (enable acl2::rev)
             :expand (<call>))
            (and stable-under-simplificationp
                 `(:expand (,(Car (last clause)))))
            (and stable-under-simplificationp
                 '(:expand ((base-ev-bindinglist nil a))
                   :do-not-induct t
                   :do-not '(generalize))))))


(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (symbol-listp x))))

(local (defthm cdr-last-when-letabs-levelmap-p
         (implies (letabs-levelmap-p x)
                  (equal (cdr (last x)) nil))))

(local (defthm cdr-last-when-term-refcounts-p
         (implies (term-refcounts-p x)
                  (equal (cdr (last x)) nil))))

(local (defthm term-refcounts-p-of-fast-alist-clean
         (implies (term-refcounts-p x)
                  (term-refcounts-p (fast-alist-clean x)))
         :hints(("Goal" :in-theory (enable fast-alist-clean)))))

(local (defthm letabs-levelmap-p-of-fast-alist-clean
         (implies (letabs-levelmap-p x)
                  (letabs-levelmap-p (fast-alist-clean x)))
         :hints(("Goal" :in-theory (enable fast-alist-clean)))))


(local (defthm pseudo-var-list-p-when-symbol-listp
         (implies (and (symbol-listp x)
                       (not (member nil x)))
                  (pseudo-var-list-p x))))


(local (in-theory (disable fast-alist-clean)))

(local (defthm alist-keys-of-cdr-last
         (equal (alist-keys (cdr (last x))) nil)
         :hints(("Goal" :in-theory (enable last)))))

(local (defthm no-duplicate-keys-of-fast-alist-clean
         (no-duplicatesp (alist-keys (fast-alist-clean x)))
         :hints(("Goal" :in-theory (enable fast-alist-clean)))))

(local (defthm alist-vals-of-pairlis$
         (implies (equal (len x) (len y))
                  (equal (alist-vals (pairlis$ x y))
                         (true-list-fix y)))
         :hints(("Goal" :in-theory (enable alist-vals)))))
       

(define let-abstract-term ((x pseudo-termp)
                           (base-var pseudo-var-p))
  :returns (new-x pseudo-termp)
  (b* ((refcounts (fast-alist-clean (term-count-references x nil)))
       (multiref-terms (collect-multiref-terms refcounts))
       (- (fast-alist-free refcounts))
       ;; (- (cw "multiref-terms: ~x0~%" multiref-terms))
       (term-vars (term-vars x))
       (new-vars (acl2::make-n-vars (len multiref-terms)
                                    (pseudo-var-fix base-var)
                                    0
                                    term-vars))
       (varmap (make-fast-alist (pairlis$ multiref-terms new-vars)))
       ;; (- (cw "varmap: ~x0~%x: ~x1~%" varmap x))
       ((mv top-level levels) (term-label-letabs-levels x varmap nil))
       ;; (- (cw "top-level: ~x0~%levels: ~x1~%" top-level levels))
       (levelmap (fast-alist-clean (letabs-sort-levels levels nil)))
       (- (fast-alist-free levels))
       ;; (- (cw "levelmap: ~x0~%" levelmap))
       ((mv bindinglist partial-varmap)
        (letabs-abstract-levels (+ 1 top-level) levelmap varmap))
       (bindinglist (acl2::rev bindinglist))
       ;; (- (cw "bindinglist: ~x0~%partial-varmap: ~x1~%" bindinglist partial-varmap))
       (abs-x  (term-let-abstract x partial-varmap))
       ((acl2::hintcontext :here)))
    (bindinglist-to-lambda-nest-exec bindinglist abs-x))
  ///
  (set-ignore-ok t)

  (local (defthm intersectp-of-make-n-vars-when-subset
           (implies (subsetp vars avoid)
                    (not (intersectp (acl2::make-n-vars n base m avoid) vars)))
           :hints (("goal" :use ((:instance acl2::make-n-vars-not-in-avoid
                                  (n n) (base base) (m m) (avoid-lst avoid)))
                    :in-theory (e/d (acl2::intersectp-witness-rw)
                                    (acl2::make-n-vars-not-in-avoid))))))

  (local (defthm termlist-vars-of-alist-keys-of-fast-alist-fork
           (implies (and (not (member v (termlist-vars (alist-keys x))))
                         (not (member v (termlist-vars (alist-keys y)))))
                    (not (member v (termlist-vars (alist-keys (fast-alist-fork x y))))))
           :hints(("Goal" :in-theory (enable fast-alist-fork alist-keys termlist-vars)))))

  (local (defthm termlist-vars-of-alist-keys-of-fast-alist-clean
           (implies (not (member v (termlist-vars (alist-keys x))))
                    (not (member v (termlist-vars (alist-keys (fast-alist-clean x))))))
           :hints(("Goal" :in-theory (enable fast-alist-clean)))))

  (local (defthm subsetp-multiref-terms
           (subsetp (termlist-vars (collect-multiref-terms (fast-alist-clean (term-count-references x nil))))
                    (term-vars x))
           :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))


  (defret let-abstract-term-correct
    (equal (base-ev new-x a)
           (base-ev x a))
    :hints ((acl2::function-termhint
             let-abstract-term
             (:here (b* ((env (base-ev-bindinglist bindinglist a)))
                      `(:use ((:instance base-ev-of-term-let-abstract
                               (env ,(acl2::hq env))
                               (varmap ,(acl2::hq partial-varmap))
                               (x ,(acl2::hq x)))
                              (:instance not-intersectp-when-not-intersectp-with-superset
                               (x ,(acl2::hq (term-vars x)))
                               (y (alist-vals ,(acl2::hq partial-varmap)))
                               (z (alist-vals ,(acl2::hq varmap))))
                              (:instance subsetp-alist-vals-when-subsetp
                               (y ,(acl2::hq partial-varmap)) (x ,(acl2::hq varmap)))
                              (:instance letabs-abstract-levels-partial-varmap-is-subsetp
                               (full-varmap ,(acl2::hq varmap))
                               (levelmap ,(Acl2::hq levelmap))
                               (level ,(acl2::hq (+ 1 top-level)))))
                        :in-theory (e/d (intersectp-commutes-neg)
                                        (base-ev-of-term-let-abstract
                                         letabs-abstract-levels-partial-varmap-is-subsetp)))))))))
       




(defevaluator letabs-ev letabs-ev-list
  ((if a b c)
   (not a))
  :namedp t)

(local (acl2::def-join-thms letabs-ev))

(defthm letabs-ev-of-let-abstract-term
  (equal (letabs-ev (let-abstract-term x base-var) a)
         (letabs-ev x a))
  :hints (("goal" :use ((:functional-instance let-abstract-term-correct
                         (base-ev letabs-ev)
                         (base-ev-list letabs-ev-list)))
           :in-theory (enable letabs-ev-of-fncall-args
                              letabs-ev-of-bad-fncall
                              letabs-ev-of-nonsymbol-atom))))


(define let-abstract-termlist ((x pseudo-term-listp)
                               (var pseudo-var-p))
  :returns (new-x pseudo-term-listp)
  (if (atom x)
      nil
    (cons (let-abstract-term (car x) var)
          (let-abstract-termlist (cdr x) var)))
  ///
  (defthm base-ev-of-let-abstract-termlist
    (equal (base-ev-list (let-abstract-termlist x var) a)
           (base-ev-list x a)))

  (defthm letabs-ev-of-disjoin-let-abstract-termlist
    (iff (letabs-ev (disjoin (let-abstract-termlist x var)) a)
         (letabs-ev (disjoin x) a))))

(define let-abstract-lits-clause-proc ((clause pseudo-term-listp)
                                       (var))
  (if (pseudo-var-p var)
      (list (let-abstract-termlist clause var))
    (list clause))
  ///
  (defthm let-abstract-lits-clause-proc-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (letabs-ev (conjoin-clauses (let-abstract-lits-clause-proc clause var)) a))
             (letabs-ev (disjoin clause) a))
    :rule-classes :clause-processor))

(define let-abstract-full-clause-proc ((clause pseudo-term-listp)
                                       (var))
  (if (pseudo-var-p var)
      (list (list (let-abstract-term (disjoin clause) var)))
    (list clause))
  ///
  (defthm let-abstract-full-clause-proc-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (letabs-ev (conjoin-clauses (let-abstract-full-clause-proc clause var)) a))
             (letabs-ev (disjoin clause) a))
    :rule-classes :clause-processor))

  
      


      

