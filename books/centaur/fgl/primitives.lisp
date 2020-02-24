; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "def-fgl-rewrite")
(include-book "centaur/misc/hons-remove-dups" :dir :system)
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))
;; (def-fgl-object-eval fgl-prim
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

(def-formula-checks primitives-formula-checks
  (if! atom ifix bool-fix$inline mv-nth))

(enable-split-ifs equal)

;; (def-fgl-object-eval-inst fgl-object-eval-of-gobj-syntactic-integer-fix)
;; (def-fgl-object-eval-inst fgl-object-eval-when-gobj-syntactic-integerp)
;; (def-fgl-object-eval-inst fgl-object-eval-of-gobj-syntactic-boolean-fix)
;; (def-fgl-object-eval-inst fgl-object-eval-when-gobj-syntactic-booleanp)

(set-state-ok t)
(set-ignore-ok t)

(local (defthm fgl-objectlist-eval-when-consp
         (implies (consp x)
                  (equal (fgl-objectlist-eval x env)
                         (cons (fgl-object-eval (car x) env)
                               (fgl-objectlist-eval (cdr x) env))))))

(local (in-theory (disable member acl2::member-equal-append)))

(local (in-theory (enable kwote-lst
                          fgl-objectlist-eval
                          fgl-apply)))


(def-fgl-rewrite int-to-ifix
  (equal (int x) (ifix x)))

(enable-split-ifs ifix)
(def-fgl-primitive ifix (x)
  (b* (((mv ok fix) (gobj-syntactic-integer-fix x))
       ((unless ok) (mv nil nil)))
    (mv t fix))
  :returns (mv successp ans)
  :formula-check primitives-formula-checks)

(def-fgl-rewrite ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x) x)))

(local (defthm integerp-of-fgl-object-alist-eval
         (iff (integerp (fgl-object-alist-eval x env))
              (integerp (fgl-object-alist-fix x)))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (fgl-object-alist-fix x))))))


(local (defthm fgl-object-kind-when-booleanp
         (implies (booleanp x)
                  (equal (fgl-object-kind x) :g-concrete))
         :hints(("Goal" :in-theory (enable fgl-object-kind)))))

(local (defthm fgl-object-eval-when-booleanp
         (implies (booleanp x)
                  (equal (Fgl-object-eval x env) x))
         :hints(("Goal" :in-theory (enable booleanp fgl-object-eval)))))


(enable-split-ifs integerp)
(def-fgl-primitive integerp (x)
  (fgl-object-case x
    :g-concrete (mv t (integerp x.val))
    :g-integer (mv t t)
    :g-boolean (mv t nil)
    :g-cons (mv t nil)
    :g-map (mv t (integerp x.alist))
    :g-apply (if (or (and** (eq x.fn 'ifix) (eql (len x.args) 1))
                     (and** (eq x.fn 'intcons) (eql (len x.args) 2))
                     (and** (eq x.fn 'intcdr) (eql (len x.args) 1))
                     (and** (eq x.fn 'endint) (eql (len x.args) 1)))
                 (mv t t)
               (mv nil nil))
    :otherwise (mv nil nil))
  :returns (successp ans)
  :formula-check primitives-formula-checks)



(local (defthm fgl-object-alist-eval-under-iff
         (iff (fgl-object-alist-eval x env)
              (fgl-object-alist-fix x))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (fgl-object-alist-fix x))))))

(local (defthm bool->bit-of-nonnil
         (implies x
                  (equal (bool->bit x) 1))))

(enable-split-ifs endint)
(def-fgl-primitive endint (x)
  (fgl-object-case x
    :g-concrete (mv t (if x.val -1 0))
    :g-boolean (mv t (mk-g-integer (list x.bool)))
    :g-cons (mv t -1)
    :g-integer (mv t -1)
    :g-map (mv t (endint (and x.alist t)))
    :otherwise (mv nil nil))
  :returns (mv successp ans))



(enable-split-ifs intcons)
(def-fgl-primitive intcons (car cdr)
  (b* (((mv ok car-fix) (gobj-syntactic-boolean-fix car))
       ((unless ok) (mv nil nil))
       ((mv ok cdr-fix) (gobj-syntactic-integer-fix cdr))
       ((unless ok) (mv nil nil)))
    (mv t (mk-g-integer (scons (gobj-syntactic-boolean->bool car-fix)
                               (gobj-syntactic-integer->bits cdr-fix)))))
  :returns (mv successp ans))

(def-fgl-rewrite intcons-of-ifix
  (equal (intcons car (ifix cdr))
         (intcons car cdr)))

(local (defthm logcar-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcar x) 0))
         :hints(("Goal" :in-theory (enable logcar)))))

(local (defthm fgl-object-alist-eval-when-atom
         (implies (atom (fgl-object-alist-fix x))
                  (equal (fgl-object-alist-eval x env)
                         (fgl-object-alist-fix x)))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (fgl-object-alist-fix x))))))

(local (defthm consp-of-fgl-object-alist-eval
         (iff (consp (fgl-object-alist-eval x env))
              (consp (fgl-object-alist-fix x)))
         :hints(("Goal" :induct (len x)
                 :in-theory (enable (:i len))
                 :expand ((fgl-object-alist-eval x env)
                          (fgl-object-alist-fix x))))))

(local (defthm integerp-of-fgl-object-alist-eval
         (iff (integerp (fgl-object-alist-eval x env))
              (integerp (fgl-object-alist-fix x)))
         :hints (("goal" :use (fgl-object-alist-eval-when-atom
                               consp-of-fgl-object-alist-eval)
                  :in-theory (disable fgl-object-alist-eval-when-atom
                                      consp-of-fgl-object-alist-eval)))))

(local (defthm bool->bit-equal-1
         (equal (equal (bool->bit x) 1)
                (not (not x)))))

(enable-split-ifs intcar)
(def-fgl-primitive intcar (x)
  (fgl-object-case x
    :g-concrete (mv t (and (integerp x.val)
                           (intcar x.val)))
    :g-integer (mv t (mk-g-boolean (car x.bits)))
    :g-boolean (mv t nil)
    :g-cons (mv t nil)
    :g-map (mv t (and (integerp x.alist)
                      (intcar x.alist)))
    :otherwise (mv nil nil))
  :returns (mv successp ans))

(def-fgl-rewrite intcar-of-ifix
  (equal (intcar (ifix x)) (intcar x)))

(local (in-theory (enable int-endp
                          fgl-object-bfrlist-when-g-concrete)))

(local (defthm gobj-bfr-list-eval-when-atom-cdr
         (implies (not (consp (cdr bits)))
                  (equal (gobj-bfr-list-eval bits env)
                         (and (consp bits)
                              (list (gobj-bfr-eval (car bits) env)))))
         :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
                 
(enable-split-ifs int-endp)          
(def-fgl-primitive int-endp (x)
  (fgl-object-case x
    :g-concrete (mv t (or (not (integerp x.val))
                          (int-endp x.val)))
    :g-integer (mv (atom (cdr x.bits))
                   (atom (cdr x.bits)))
    :g-boolean (mv t t)
    :g-cons (mv t t)
    :g-map (mv t (or (not (integerp x.alist))
                     (int-endp x.alist)))
    :otherwise (mv nil nil))
  :returns (mv successp ans))

(def-fgl-rewrite int-endp-of-ifix
  (equal (int-endp (ifix x)) (int-endp x)))

(local (defthm logcdr-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcdr x) 0))
         :hints(("Goal" :in-theory (enable logcdr)))))

(local (in-theory (enable fgl-object-kind-when-integerp
                          g-concrete->val-when-integerp)))

(local (in-theory (disable logcdr-of-bools->int)))

(enable-split-ifs intcdr)
(def-fgl-primitive intcdr (x)
  (fgl-object-case x
    :g-concrete (mv t (if (integerp x.val)
                          (intcdr x.val)
                        0))
    :g-integer (mv t (mk-g-integer (scdr x.bits)))
    :g-boolean (mv t 0)
    :g-cons (mv t 0)
    :g-map (mv t (if (integerp x.alist)
                     (intcdr x.alist)
                   0))
    :otherwise (mv nil nil))
  :returns (mv successp ans))

(def-fgl-rewrite intcdr-of-ifix
  (equal (intcdr (ifix x)) (intcdr x)))

(local (in-theory (enable bool-fix)))

(def-fgl-rewrite bool-is-bool-fix
  (equal (bool x)
         (bool-fix x)))

(enable-split-ifs bool-fix$inline)
(def-fgl-primitive bool-fix$inline (x)
  (fgl-object-case x
    :g-concrete (mv t (bool-fix x.val) interp-st)
    :g-boolean (mv t (fgl-object-fix x) interp-st)
    :g-integer (mv t t interp-st)
    :g-cons (mv t t interp-st)
    :g-map (mv t (bool-fix x.alist) interp-st)
    :otherwise (mv nil nil interp-st))
  :returns (mv successp ans interp-st)
  :formula-check primitives-formula-checks)

(def-fgl-primitive cons (car cdr)
  (if (and (fgl-object-case car :g-concrete)
           (fgl-object-case cdr :g-concrete))
      (g-concrete (cons (g-concrete->val car)
                        (g-concrete->val cdr)))
    (g-cons car cdr))
  :returns ans)

(set-ignore-ok t)

(enable-split-ifs consp)
(def-fgl-primitive consp (x)
  (fgl-object-case x
    :g-concrete (mv t (consp x.val) interp-st)
    :g-integer (mv t nil interp-st)
    :g-boolean (mv t nil interp-st)
    :g-cons (mv t t interp-st)
    :g-map (mv t (consp x.alist) interp-st)
    :otherwise (mv nil nil interp-st))
  :returns (mv successp ans interp-st))

(enable-split-ifs atom)
(def-fgl-primitive atom (x)
  (fgl-object-case x
    :g-concrete (mv t (atom x.val) interp-st)
    :g-integer (mv t t interp-st)
    :g-boolean (mv t t interp-st)
    :g-cons (mv t nil interp-st)
    :g-map (mv t (atom x.alist) interp-st)
    :otherwise (mv nil nil interp-st))
  :returns (mv successp ans interp-st)
  :formula-check primitives-formula-checks)

(local (defthm consp-car-when-fgl-object-alist-p
         (implies (and (fgl-object-alist-p x)
                       (consp x))
                  (consp (car x)))))

(local (defthm fgl-object-alist-eval-when-consp
         (implies (and (consp x)
                       (consp (car x)))
                  (equal (fgl-object-alist-eval x env)
                         (cons (cons (caar x) (fgl-object-eval (cdar x) env))
                               (fgl-object-alist-eval (cdr x) env))))))

(enable-split-ifs car)
(def-fgl-primitive car (x)
  (fgl-object-case x
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
    :otherwise (mv nil nil interp-st))
  :returns (mv successp ans interp-st))

(enable-split-ifs cdr)
(def-fgl-primitive cdr (x)
  (fgl-object-case x
    :g-concrete (mv t (g-concrete (mbe :logic (cdr x.val)
                                       :exec (and (consp x.val) (cdr x.val))))
                    interp-st)
    :g-boolean (mv t nil interp-st)
    :g-integer (mv t nil interp-st)
    :g-cons (mv t x.cdr interp-st)
    :g-map (mv t (and (consp x.alist)
                      (g-map '(:g-map) (cdr x.alist)))
               interp-st)
    :otherwise (mv nil nil interp-st))
  :returns (mv successp ans interp-st))


(encapsulate nil
  (local (defthm fgl-object-eval-under-iff-when-concrete-syntactic-boolean-fix
           (b* (((mv ok fix) (gobj-syntactic-boolean-fix x)))
             (implies (and ok
                           (fgl-object-case fix :g-concrete))
                      (iff (fgl-object-eval x env)
                           (g-concrete->val fix))))
           :hints(("Goal" :in-theory (enable fgl-object-eval gobj-syntactic-boolean-fix)))))

  (local (in-theory (enable fgl-object-eval-under-iff-when-concrete-syntactic-boolean-fix)))

  (local (add-default-hints
          '((and stable-under-simplificationp
                 '(:in-theory (enable if!))))))

  (local (in-theory (disable acl2::booleanp-of-car-when-boolean-listp
                             acl2::integerp-of-car-when-integer-listp
                             bfr-listp$-when-subsetp-equal
                             equal-of-booleans-rewrite)))
         

  (def-fgl-primitive if! (x y z)
    (b* (((mv ok x-fix) (gobj-syntactic-boolean-fix x))
         ((unless ok) (g-ite x y z))
         ((when (fgl-object-case x-fix :g-concrete))
          (if (g-concrete->val x-fix) y z)))
      (g-ite x-fix y z))
    :returns ans
    :formula-check primitives-formula-checks))


;; (defthm integerp-in-terms-of-int
;;   (equal (integerp x)
;;          (equal (int x) x))
;;   :rule-classes nil)





;;   (local (defthmd fgl-object-bfrlist-of-get-bvar->term$a-aux
;;            (implies (and (not (member v (bvar-db-bfrlist-aux m bvar-db)))
;;                          (< (nfix n) (nfix m))
;;                          (<= (base-bvar$a bvar-db) (nfix n)))
;;                     (not (member v (fgl-object-bfrlist (get-bvar->term$a n bvar-db)))))
;;            :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux)))))

;;   (local (defthm fgl-object-bfrlist-of-get-bvar->term$a
;;            (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
;;                          (<= (base-bvar$a bvar-db) (nfix n))
;;                          (< (nfix n) (next-bvar$a bvar-db)))
;;                     (not (member v (fgl-object-bfrlist (get-bvar->term$a n bvar-db)))))
;;            :hints (("goal" :in-theory (enable bvar-db-bfrlist)
;;                     :use ((:instance fgl-object-bfrlist-of-get-bvar->term$a-aux
;;                            (m (next-bvar$a bvar-db))))))))

;;(local (in-theory (enable gobj-bfr-list-eval-is-bfr-list-eval)))

;; (define int+ (x y)
;;   (+ (ifix x) (ifix y)))



;; (def-fgl-formula-checks int+-formula-checks (int+ ifix))

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


;; (def-fgl-primitive int+ (x y)
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

(define fgl-object-mv-nth ((n natp) (x fgl-object-p))
  :returns (mv ok (nth fgl-object-p))
  (fgl-object-case x
    :g-concrete (mv t (g-concrete (ec-call (nth n x.val))))
    :g-cons (b* (((when (zp n)) (mv t x.car)))
              (fgl-object-mv-nth (1- n) x.cdr))
    :g-boolean (mv t nil)
    :g-integer (mv t nil)
    :otherwise (mv nil nil))
  ///
  (local (defthm mv-nth-is-nth
           (equal (mv-nth n x) (nth n x))
           :hints(("Goal" :in-theory (enable mv-nth nth)))))
  (defret fgl-object-mv-nth-correct
    (implies ok
             (equal (fgl-object-eval nth env)
                    (mv-nth n (fgl-object-eval x env))))
    :hints(("Goal" :in-theory (enable mv-nth))))

  (defret bfr-listp-of-<fn>
    (implies (bfr-listp (fgl-object-bfrlist x))
             (bfr-listp (fgl-object-bfrlist nth)))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))
    
(local (in-theory (enable bfr-listp-when-not-member-witness)))

(local (defthm mv-nth-of-nfix
         (equal (mv-nth (nfix n) x)
                (mv-nth n x))
         :hints(("Goal" :in-theory (enable mv-nth)))))

(def-fgl-primitive mv-nth (n x)
  (b* (((unless (fgl-object-case n :g-concrete))
        (mv nil nil interp-st))
       (n (nfix (g-concrete->val n)))
       ((mv ok ans) (fgl-object-mv-nth n x)))
    (mv ok ans interp-st))
  :returns (mv successp ans interp-st)
  :formula-check primitives-formula-checks)
    
       


(local (install-fgl-metafns baseprims))




