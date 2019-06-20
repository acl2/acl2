; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "add-primitives")
(include-book "primitives-stub")
(include-book "bfr-arithmetic")
(include-book "subst-functions")
(include-book "centaur/misc/hons-remove-dups" :dir :system)
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))
;; (def-gl-object-eval fgl-prim
;;   (acl2-numberp
;;    binary-* binary-+
;;    unary-- unary-/ < char-code characterp
;;    code-char complex complex-rationalp
;;    coerce consp denominator imagpart
;;    integerp intern-in-package-of-symbol
;;    numerator rationalp realpart
;;    stringp symbol-name symbol-package-name
;;    symbolp
;;    syntax-bind-fn abort-rewrite

;;    equal not if iff int bool
;;    concrete return-last synp cons car cdr
;;    intcons intcons* endint intcar intcdr int-endp
;;    typespec-check implies fgl-sat-check))




(def-gl-object-eval-inst fgl-object-eval-of-gobj-syntactic-integer-fix)
(def-gl-object-eval-inst fgl-object-eval-when-gobj-syntactic-integerp)
(def-gl-object-eval-inst fgl-object-eval-of-gobj-syntactic-boolean-fix)
(def-gl-object-eval-inst fgl-object-eval-when-gobj-syntactic-booleanp)

(set-state-ok t)
(set-ignore-ok t)

(local (defthm fgl-objectlist-eval-when-consp
         (implies (consp x)
                  (equal (fgl-objectlist-eval x env)
                         (cons (fgl-object-eval (car x) env)
                               (fgl-objectlist-eval (cdr x) env))))))

(local (in-theory (disable member acl2::member-equal-append)))

(local (in-theory (enable kwote-lst
                          fgl-objectlist-eval)))


(def-gl-primitive int (x)
  (b* (((mv ok fix) (gobj-syntactic-integer-fix x))
       ((unless ok) (mv nil nil interp-st)))
    (mv t fix interp-st)))

(local (defthm integerp-of-fgl-object-alist-eval
         (iff (integerp (fgl-object-alist-eval x env))
              (integerp (gl-object-alist-fix x)))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (gl-object-alist-fix x))))))


(local (defthm gl-object-kind-when-booleanp
         (implies (booleanp x)
                  (equal (gl-object-kind x) :g-concrete))
         :hints(("Goal" :in-theory (enable gl-object-kind)))))

(local (defthm fgl-object-eval-when-booleanp
         (implies (booleanp x)
                  (equal (Fgl-object-eval x env) x))
         :hints(("Goal" :in-theory (enable booleanp fgl-object-eval)))))



(def-gl-primitive integerp (x)
  (gl-object-case x
    :g-concrete (mv t (integerp x.val) interp-st)
    :g-integer (mv t t interp-st)
    :g-boolean (mv t nil interp-st)
    :g-cons (mv t nil interp-st)
    :g-map (mv t (integerp x.alist) interp-st)
    :otherwise (mv nil nil interp-st)))


(local (defthm fgl-object-alist-eval-under-iff
         (iff (fgl-object-alist-eval x env)
              (gl-object-alist-fix x))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (gl-object-alist-fix x))))))



(def-gl-primitive endint (x)
  (gl-object-case x
    :g-concrete (mv t (if x.val -1 0) interp-st)
    :g-boolean (mv t (mk-g-integer (list x.bool)) interp-st)
    :g-cons (mv t -1 interp-st)
    :g-integer (mv t -1 interp-st)
    :g-map (mv t (endint (and x.alist t)) interp-st)
    :otherwise (mv nil nil interp-st)))




(def-gl-primitive intcons (car cdr)
  (b* (((mv ok car-fix) (gobj-syntactic-boolean-fix car))
       ((unless ok) (mv nil nil interp-st))
       ((mv ok cdr-fix) (gobj-syntactic-integer-fix cdr))
       ((unless ok) (mv nil nil interp-st)))
    (mv t (mk-g-integer (scons (gobj-syntactic-boolean->bool car-fix)
                               (gobj-syntactic-integer->bits cdr-fix)))
        interp-st)))

(local (defthm logcar-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcar x) 0))
         :hints(("Goal" :in-theory (enable logcar)))))

(local (defthm fgl-object-alist-eval-when-atom
         (implies (atom (gl-object-alist-fix x))
                  (equal (fgl-object-alist-eval x env)
                         (gl-object-alist-fix x)))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (gl-object-alist-fix x))))))

(local (defthm consp-of-fgl-object-alist-eval
         (iff (consp (fgl-object-alist-eval x env))
              (consp (gl-object-alist-fix x)))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (gl-object-alist-fix x))))))

(local (defthm integerp-of-fgl-object-alist-eval
         (iff (integerp (fgl-object-alist-eval x env))
              (integerp (gl-object-alist-fix x)))
         :hints (("goal" :use (fgl-object-alist-eval-when-atom
                               consp-of-fgl-object-alist-eval)
                  :in-theory (disable fgl-object-alist-eval-when-atom
                                      consp-of-fgl-object-alist-eval)))))

(def-gl-primitive intcar (x)
  (gl-object-case x
    :g-concrete (mv t (and (integerp x.val)
                           (intcar x.val))
                    interp-st)
    :g-integer (mv t (mk-g-boolean (car x.bits)) interp-st)
    :g-boolean (mv t nil interp-st)
    :g-cons (mv t nil interp-st)
    :g-map (mv t (and (integerp x.alist)
                      (intcar x.alist))
               interp-st)
    :otherwise (mv nil nil interp-st)))

(local (in-theory (enable int-endp
                          gl-object-bfrlist-when-g-concrete)))

(local (defthm gobj-bfr-list-eval-when-atom-cdr
         (implies (not (consp (cdr bits)))
                  (equal (gobj-bfr-list-eval bits env)
                         (and (consp bits)
                              (list (gobj-bfr-eval (car bits) env)))))
         :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
                           
(def-gl-primitive int-endp (x)
  (gl-object-case x
    :g-concrete (mv t (or (not (integerp x.val))
                          (int-endp x.val))
                    interp-st)
    :g-integer (mv (atom (cdr x.bits))
                   (atom (cdr x.bits))
                   interp-st)
    :g-boolean (mv t t interp-st)
    :g-cons (mv t t interp-st)
    :g-map (mv t (or (not (integerp x.alist))
                     (int-endp x.alist))
               interp-st)
    :otherwise (mv nil nil interp-st)))

(local (defthm logcdr-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcdr x) 0))
         :hints(("Goal" :in-theory (enable logcdr)))))

(local (in-theory (enable gl-object-kind-when-integerp
                          g-concrete->val-when-integerp)))

(local (in-theory (disable logcdr-of-bools->int)))

(def-gl-primitive intcdr (x)
  (gl-object-case x
    :g-concrete (mv t (if (integerp x.val)
                          (intcdr x.val)
                        0)
                    interp-st)
    :g-integer (mv t (mk-g-integer (scdr x.bits)) interp-st)
    :g-boolean (mv t 0 interp-st)
    :g-cons (mv t 0 interp-st)
    :g-map (mv t (if (integerp x.alist)
                     (intcdr x.alist)
                   0)
               interp-st)
    :otherwise (mv nil nil interp-st)))

(local (in-theory (enable bool-fix)))

(def-gl-primitive bool (x)
  (gl-object-case x
    :g-concrete (mv t (bool-fix x.val) interp-st)
    :g-boolean (mv t (gl-object-fix x) interp-st)
    :g-integer (mv t t interp-st)
    :g-cons (mv t t interp-st)
    :g-map (mv t (bool-fix x.alist) interp-st)
    :otherwise (mv nil nil interp-st)))

(def-gl-primitive cons (car cdr)
  (mv t
      (if (and (gl-object-case car :g-concrete)
               (gl-object-case cdr :g-concrete))
          (g-concrete (cons (g-concrete->val car)
                            (g-concrete->val cdr)))
        (g-cons car cdr))
      interp-st))

(set-ignore-ok t)


(def-gl-primitive consp (x)
  (gl-object-case x
    :g-concrete (mv t (consp x.val) interp-st)
    :g-integer (mv t nil interp-st)
    :g-boolean (mv t nil interp-st)
    :g-cons (mv t t interp-st)
    :g-map (mv t (consp x.alist) interp-st)
    :otherwise (mv nil nil interp-st)))

(local (defthm consp-car-when-gl-object-alist-p
         (implies (and (gl-object-alist-p x)
                       (consp x))
                  (consp (car x)))))

(local (defthm fgl-object-alist-eval-when-consp
         (implies (and (consp x)
                       (consp (car x)))
                  (equal (fgl-object-alist-eval x env)
                         (cons (cons (caar x) (fgl-object-eval (cdar x) env))
                               (fgl-object-alist-eval (cdr x) env))))))

(def-gl-primitive car (x)
  (gl-object-case x
    :g-concrete (mv t (g-concrete (mbe :logic (car x.val)
                                       :exec (and (consp x.val) (car x.val))))
                    interp-st)
    :g-boolean (mv t nil interp-st)
    :g-integer (mv t nil interp-st)
    :g-cons (mv t x.car interp-st)
    :g-map (mv t (and (consp x.alist)
                      (g-cons (g-concrete (caar x.alist))
                              (cdar x.alist)))
               interp-st)
    :otherwise (mv nil nil interp-st)))

(def-gl-primitive cdr (x)
  (gl-object-case x
    :g-concrete (mv t (g-concrete (mbe :logic (cdr x.val)
                                       :exec (and (consp x.val) (cdr x.val))))
                    interp-st)
    :g-boolean (mv t nil interp-st)
    :g-integer (mv t nil interp-st)
    :g-cons (mv t x.cdr interp-st)
    :g-map (mv t (and (consp x.alist)
                      (g-map '(:g-map) (cdr x.alist)))
               interp-st)
    :otherwise (mv nil nil interp-st)))
    

;; (defthm integerp-in-terms-of-int
;;   (equal (integerp x)
;;          (equal (int x) x))
;;   :rule-classes nil)





;;   (local (defthmd gl-object-bfrlist-of-get-bvar->term$a-aux
;;            (implies (and (not (member v (bvar-db-bfrlist-aux m bvar-db)))
;;                          (< (nfix n) (nfix m))
;;                          (<= (base-bvar$a bvar-db) (nfix n)))
;;                     (not (member v (gl-object-bfrlist (get-bvar->term$a n bvar-db)))))
;;            :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux)))))

;;   (local (defthm gl-object-bfrlist-of-get-bvar->term$a
;;            (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
;;                          (<= (base-bvar$a bvar-db) (nfix n))
;;                          (< (nfix n) (next-bvar$a bvar-db)))
;;                     (not (member v (gl-object-bfrlist (get-bvar->term$a n bvar-db)))))
;;            :hints (("goal" :in-theory (enable bvar-db-bfrlist)
;;                     :use ((:instance gl-object-bfrlist-of-get-bvar->term$a-aux
;;                            (m (next-bvar$a bvar-db))))))))

;;(local (in-theory (enable gobj-bfr-list-eval-is-bfr-list-eval)))

;; (define int+ (x y)
;;   (+ (ifix x) (ifix y)))



;; (def-gl-formula-checks int+-formula-checks (int+ ifix))

;; (define w-equiv (x y)
;;   :non-executable t
;;   :no-function t
;;   :verify-guards nil
;;   (equal (w x) (w y))
;;   ///
;;   (defequiv w-equiv)
;;   (defcong w-equiv equal (w x) 1)
;;   (defcong w-equiv equal (meta-extract-formula name state) 2
;;     :hints(("Goal" :in-theory (enable meta-extract-formula))))

;;   (defthm ws-equal-forward
;;     (implies (equal (w st) (w state))
;;              (w-equiv st state))
;;     :rule-classes :forward-chaining))

;; (local (in-theory (disable w)))

;; (defthm fgl-ev-of-ifix-call
;;   (implies (and (fgl-ev-meta-extract-global-facts :state st)
;;                 (int+-formula-checks st)
;;                 (equal (w st) (w state)))
;;            (equal (fgl-ev (list 'ifix x) a)
;;                   (ifix (fgl-ev x a))))
;;   :hints(("Goal" :in-theory (e/d (int+
;;                                   int+-formula-checks
;;                                   fgl-ev-of-fncall-args)
;;                                  (fgl-ev-meta-extract-formula))
;;           :use ((:instance fgl-ev-meta-extract-formula
;;                  (st state) (state st)
;;                  (name 'ifix)
;;                  (a (list (cons 'x (fgl-ev x a)))))))))

;; (defthm fgl-ev-of-int+-call
;;   (implies (and (fgl-ev-meta-extract-global-facts :state st)
;;                 (int+-formula-checks st)
;;                 (equal (w st) (w state)))
;;            (equal (fgl-ev (list 'int+ x y) a)
;;                   (int+ (fgl-ev x a)
;;                         (fgl-ev y a))))
;;   :hints(("Goal" :in-theory (e/d (int+
;;                                   int+-formula-checks
;;                                   fgl-ev-of-fncall-args)
;;                                  (fgl-ev-meta-extract-formula))
;;           :use ((:instance fgl-ev-meta-extract-formula
;;                  (st state) (state st)
;;                  (name 'int+)
;;                  (a (list (cons 'x (fgl-ev x a))
;;                           (cons 'y (fgl-ev y a)))))))))

;; (local (defthm fgl-objectlist-eval-of-atom
;;          (implies (not (consp x))
;;                   (equal (fgl-objectlist-eval x env) nil))
;;          :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm bools->int-of-eval-syntactic-integer-bits
;;          (b* (((mv ok xfix) (gobj-syntactic-integer-fix x)))
;;            (implies ok
;;                     (equal (bools->int (gobj-bfr-list-eval (gobj-syntactic-integer->bits xfix)
;;                                                            env))
;;                            (ifix (fgl-object-eval x env)))))
;;          :hints(("Goal" :in-theory (enable gobj-syntactic-integer->bits
;;                                            gobj-syntactic-integer-fix)))))


;; (def-gl-primitive int+ (x y)
;;   (b* (((mv ok xfix) (gobj-syntactic-integer-fix x))
;;        ((unless ok) (mv nil nil interp-st))
;;        ((mv ok yfix) (gobj-syntactic-integer-fix y))
;;        ((unless ok) (mv nil nil interp-st))
;;        (xbits (gobj-syntactic-integer->bits xfix))
;;        (ybits (gobj-syntactic-integer->bits yfix)))
;;     (stobj-let ((logicman (interp-st->logicman interp-st)))
;;                (bits logicman)
;;                (bfr-+-ss nil xbits ybits logicman)
;;                (mv t (mk-g-integer bits) interp-st)))
;;   :formula-check int+-formula-checks
;;   :prepwork ((local (in-theory (enable int+)))))




(local (install-gl-primitives baseprims))




