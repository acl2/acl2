; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

; (in-package "FGL")
(include-book "build/ifdef" :dir :system)
(include-book "bfr")
(include-book "arith-base")
(include-book "std/util/termhints" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "std/util/defretgen" :dir :system)

(local (in-theory (disable (tau-system))))

(ifdef "THMS_ONLY"
  (include-book "unify-defs")
  :endif)

(ifndef "DEFS_ONLY"
  (include-book "logicman")
  (include-book "centaur/meta/term-vars" :dir :system)
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  :endif)

(local
 (ifndef "DEFS_ONLY"
   (defthm assoc-when-nonnil
     (implies k
              (equal (assoc k x)
                     (hons-assoc-equal k x))))

   (local (defthm assoc-when-alistp
             (implies (alistp x)
                      (equal (assoc k x)
                             (hons-assoc-equal k x)))))
   :endif))

(ifndef "DEFS_ONLY"
  (cmr::defthm-term-vars-flag
    (defthm fgl-ev-of-acons-when-all-vars-bound
      (implies (and (subsetp (term-vars x) (alist-keys a))
                    (not (assoc k a)))
               (equal (fgl-ev x (cons (cons k v) a))
                      (fgl-ev x a)))
      :hints ('(:expand ((term-vars x)))
              (and stable-under-simplificationp
                   '(:in-theory (enable fgl-ev-of-fncall-args
                                        fgl-ev-of-nonsymbol-atom)
                     :cases ((pseudo-term-case x :fncall)))))
      :flag term-vars)
    (defthm fgl-ev-list-of-acons-when-all-vars-bound
      (implies (and (subsetp (termlist-vars x) (alist-keys a))
                    (not (assoc k a)))
               (equal (fgl-ev-list x (cons (cons k v) a))
                      (fgl-ev-list x a)))
      :hints ('(:expand ((termlist-vars x))))
      :flag termlist-vars))

  :endif)

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable logcar logcdr)))


(ifndef "DEFS_ONLY"
  (defsection fgl-object-bindings-eval
    (local (in-theory (enable fgl-object-bindings-fix
                              fgl-object-bindings-eval)))

    (defthm lookup-in-fgl-object-bindings-eval
      (equal (hons-assoc-equal k (fgl-object-bindings-eval x env))
             (b* ((look (hons-assoc-equal k (fgl-object-bindings-fix x))))
               (and look
                    (cons k (fgl-object-eval (cdr look) env)))))
      :hints(("Goal" :in-theory (enable hons-assoc-equal))))



    (local (defthm alistp-when-fgl-object-bindings-p-rw
             (implies (fgl-object-bindings-p x)
                      (alistp x))
             :hints(("Goal" :in-theory (enable fgl-object-bindings-p)))))

    (local (defthm alistp-when-symbol-alistp
             (implies (symbol-alistp x)
                      (alistp x))
             :hints(("Goal" :in-theory (enable symbol-alistp)))))

    (defthm alist-keys-of-fgl-object-bindings-eval
      (equal (alist-keys (fgl-object-bindings-eval x env))
             (alist-keys (fgl-object-bindings-fix x)))))
  :endif)

(acl2::process-ifdefs
 (define fgl-unify-concrete ((pat pseudo-termp)
                              (x) ;; value
                              (alist fgl-object-bindings-p))
   :returns (mv flag
                (new-alist fgl-object-bindings-p))
   :verify-guards nil
   :measure (pseudo-term-count pat)
   (b* ((alist (fgl-object-bindings-fix alist)))
     (pseudo-term-case pat
       :null (if (eq x nil)
                 (mv t alist)
               (mv nil nil))
       :var (b* ((pair (hons-assoc-equal pat.name alist))
                 ((unless pair)
                  (mv t (cons (cons pat.name (g-concrete x)) alist)))
                 (obj (cdr pair)))
              (fgl-object-case obj
                :g-concrete (if (equal obj.val x)
                                (mv t alist)
                              (mv nil nil))
                :otherwise (mv nil nil)))
       :quote (if (hons-equal pat.val x)
                  (mv t alist)
                (mv nil nil))
       :fncall
       (b* ((fn pat.fn)
            ((when (eq fn 'concrete))
             (b* (((unless (int= (len pat.args) 1)) (mv nil nil)))
               (fgl-unify-concrete (first pat.args) x alist)))
            ((when (or (eq fn 'intcons)
                       (eq fn 'intcons*)))
             (b* (((unless (int= (len pat.args) 2)) (mv nil nil))
                  ((unless (integerp x)) (mv nil nil))
                  ((when (and (or (eql x -1) (eql x 0))
                              (eq fn 'intcons)))
                   (mv nil nil))
                  (bitvar (first pat.args))
                  ((unless (pseudo-term-case bitvar :var))
                   (mv nil nil))
                  ((mv ok alist) (fgl-unify-concrete bitvar (acl2::bit->bool (logcar x)) alist))
                  ((unless ok) (mv nil nil)))
               (fgl-unify-concrete (second pat.args) (logcdr x) alist)))
            ((when (eq fn 'endint))
             (b* (((unless (int= (len pat.args) 1)) (mv nil nil))
                  ((unless (or (eql x -1) (eql x 0))) (mv nil nil))
                  (bitvar (first pat.args))
                  ((unless (pseudo-term-case bitvar :var))
                   (mv nil nil)))
               (fgl-unify-concrete bitvar (acl2::bit->bool (logcar x)) alist)))
            ((when (eq fn 'int))
             (b* (((unless (int= (len pat.args) 1)) (mv nil nil))
                  ((unless (integerp x)) (mv nil nil)))
               (fgl-unify-concrete (first pat.args) x alist)))
            ((when (eq fn 'bool))
             (b* (((unless (int= (len pat.args) 1)) (mv nil nil))
                  ((unless (booleanp x)) (mv nil nil)))
               (fgl-unify-concrete (first pat.args) x alist)))
            ((when (eq fn 'cons))
             (b* (((unless (int= (len pat.args) 2)) (mv nil nil))
                  ((unless (consp x)) (mv nil nil))
                  ((mv car-ok alist)
                   (fgl-unify-concrete (first pat.args) (car x) alist))
                  ((unless car-ok) (mv nil nil)))
               (fgl-unify-concrete (second pat.args) (cdr x) alist))))
         (mv nil nil))
       :otherwise (mv nil nil)))
   ///
   (local (in-theory (disable symbol-listp
                              (:d fgl-unify-concrete)
                              len
                              not
                              unsigned-byte-p
                              equal-of-booleans-rewrite
                              acl2::consp-when-member-equal-of-atom-listp
                              acl2::symbolp-of-car-when-symbol-listp
                              fgl-object-bindings-bfrlist
                              member-equal
                              acl2::consp-of-car-when-alistp)))

   (verify-guards fgl-unify-concrete)
))
   ;; (defret bfrlist-of-<fn>
   ;;   (implies (not (member b (fgl-object-bindings-bfrlist alist)))
   ;;            (not (member b (fgl-object-bindings-bfrlist new-alist))))
   ;;   :hints(("Goal" :induct <call>)
   ;;          (acl2::use-termhint
   ;;           `(:expand ((fgl-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist))
   ;;                      (fgl-object-bindings-bfrlist ,(acl2::hq new-alist)))))))

   ;; (ifndef "DEFS_ONLY"
   ;;   (local (defthm equal-of-len
   ;;            (implies (syntaxp (quotep n))
   ;;                     (equal (Equal (len x) n)
   ;;                            (cond ((eql n 0) (atom x))
   ;;                                  ((zp n) nil)
   ;;                                  (t (and (consp x)
   ;;                                          (equal (len (cdr x)) (1- n)))))))
   ;;            :hints(("Goal" :in-theory (enable len)))))

   ;;   (defret <fn>-alist-lookup-when-present
   ;;     (implies (and (hons-assoc-equal k (fgl-object-bindings-fix alist))
   ;;                   flag)
   ;;              (equal (hons-assoc-equal k new-alist)
   ;;                     (hons-assoc-equal k (fgl-object-bindings-fix alist))))
   ;;     :hints (("goal" :induct <call>)
   ;;             (acl2::use-termhint
   ;;              `(:expand ((fgl-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

   ;;   (defret <fn>-preserves-all-keys-bound
   ;;     (implies (and (subsetp keys (alist-keys (fgl-object-bindings-fix alist)))
   ;;                   flag)
   ;;              (subsetp keys (alist-keys new-alist)))
   ;;     :hints (("goal" :induct <call>)
   ;;             (acl2::use-termhint
   ;;              `(:expand ((fgl-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

   ;;   (local (defthm termlist-vars-when-consp
   ;;            (implies (consp x)
   ;;                     (equal (termlist-vars x)
   ;;                            (union-eq (termlist-vars (cdr x))
   ;;                                      (term-vars (car x)))))
   ;;            :hints (("goal" :expand ((termlist-vars x))))))

   ;;   (defret all-keys-bound-of-<fn>
   ;;     (implies flag
   ;;              (subsetp (term-vars pat) (alist-keys new-alist)))
   ;;     :hints (("goal" :induct <call>)
   ;;             (acl2::use-termhint
   ;;              `(:expand ((fgl-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist))
   ;;                         (term-vars pat)
   ;;                         ;; (termlist-vars (cdr pat))
   ;;                         ;; (termlist-vars (cddr pat))
   ;;                         ;; (termlist-vars (cdddr pat))
   ;;                         )))))

   ;;   (local (defret var-lookup-of-<fn>
   ;;            (implies (and flag (pseudo-term-case pat :var))
   ;;                     (hons-assoc-equal (acl2::pseudo-term-var->name pat) new-alist))
   ;;            :hints (("goal" :use ((:instance all-keys-bound-of-fgl-unify-concrete))
   ;;                     :in-theory (e/d (term-vars)
   ;;                                     (all-keys-bound-of-fgl-unify-concrete))))))

   ;;   (defret <fn>-preserves-eval-when-all-keys-bound
   ;;     (implies (and flag
   ;;                   (subsetp (term-vars term)
   ;;                            (alist-keys (fgl-object-bindings-fix alist))))
   ;;              (equal (fgl-ev term (fgl-object-bindings-eval new-alist env))
   ;;                     (fgl-ev term (fgl-object-bindings-eval alist env))))
   ;;     :hints (("goal" :induct <call>)
   ;;             (acl2::use-termhint
   ;;              `(:expand ((fgl-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist))
   ;;                         (:free (a b) (fgl-object-bindings-eval (cons a b) env)))))))

   ;;   (defret <fn>-correct
   ;;     (implies flag
   ;;              (equal (fgl-ev pat (fgl-object-bindings-eval new-alist env))
   ;;                     x))
   ;;     :hints (("Goal" :induct <call>)
   ;;             (acl2::use-termhint
   ;;              `(:expand ((fgl-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

   ;;   (defret fgl-object-bindings-bfrlist-of-<fn>
   ;;     (equal (fgl-object-bindings-bfrlist new-alist)
   ;;            (and flag (fgl-object-bindings-bfrlist alist)))
   ;;     :hints (("Goal" :induct <call>)
   ;;             (acl2::use-termhint
   ;;              `(:expand ((fgl-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

   ;;   :endif)))

(defthm bfrlist-of-mk-g-integer
  (implies (not (member v x))
           (not (member v (fgl-object-bfrlist (mk-g-integer x)))))
  :hints(("Goal" :in-theory (enable mk-g-integer))))

(defthm bfrlist-of-mk-g-boolean
  (implies (not (equal v x))
           (not (member v (fgl-object-bfrlist (mk-g-boolean x)))))
  :hints(("Goal" :in-theory (enable mk-g-boolean))))

(defthm bfrlist-of-mk-g-boolean-nonboolean
  (and (not (member nil (fgl-object-bfrlist (mk-g-boolean x))))
       (not (member t (fgl-object-bfrlist (mk-g-boolean x)))))
  :hints(("Goal" :in-theory (enable mk-g-boolean))))

(acl2::process-ifdefs
 (define gobj-syntactic-boolean-negate ((x fgl-object-p)
                                        &optional
                                        ((bfrstate bfrstate-p) 'bfrstate))
   :guard (and (gobj-syntactic-booleanp x)
               (bfr-listp (fgl-object-bfrlist x) bfrstate))
   :guard-hints (("goal" :in-theory (enable gobj-syntactic-booleanp)))
   :returns (neg fgl-object-p)
   (fgl-object-case x
     :g-boolean (g-boolean (bfr-negate x.bool))
     :otherwise (g-concrete (not (g-concrete->val x))))
   ///
   (defret bfr-listp-of-<fn>
     (bfr-listp (fgl-object-bfrlist neg)))

   (ifndef "DEFS_ONLY"
     (defret eval-of-<fn>
       (implies (and (equal bfrstate (logicman->bfrstate))
                     (gobj-syntactic-booleanp x))
                (equal (fgl-object-eval neg env)
                       (not (fgl-object-eval x env))))
       :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp))))
     :endif)))


(local (defthmd equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (cond ((eql n 0) (not (consp x)))
                               ((zp n) nil)
                               ((consp x) (equal (len (cdr x)) (1- n)))
                               (t nil))))))

(local (in-theory (disable pseudo-termp
                           pseudo-term-listp
                           acl2::pseudo-termp-opener)))


(ifndef "DEFS_ONLY"
        (define fgl-bindings-extension-p ((x fgl-object-bindings-p)
                                          (y fgl-object-bindings-p))
          (or (fgl-object-bindings-equiv x y)
              (and (consp x)
                   (if (mbt (and (consp (car x))
                                 (pseudo-var-p (caar x))))
                       (not (hons-assoc-equal (caar x) (cdr x)))
                     t)
                   (fgl-bindings-extension-p (cdr x) y)))
          ///

          (deffixequiv fgl-bindings-extension-p
            :hints(("Goal" :in-theory (enable fgl-object-bindings-fix))))

          (defthm fgl-bindings-extension-p-transitive
            (implies (and (fgl-bindings-extension-p x y)
                          (fgl-bindings-extension-p y z))
                     (fgl-bindings-extension-p x z))
            :hints (("Goal" :induct (fgl-bindings-extension-p x y))))

          (defthm fgl-bindings-extension-p-self
            (fgl-bindings-extension-p x x)
            :hints (("goal" :expand ((fgl-bindings-extension-p x x)))))

          (defthm fgl-bindings-extension-p-of-cons
            (equal (fgl-bindings-extension-p (cons pair x) y)
                   (or (fgl-object-bindings-equiv (cons pair x) y)
                       (and (or (not (and (consp pair)
                                          (pseudo-var-p (car pair))))
                                (not (hons-assoc-equal (car pair) x)))
                            (fgl-bindings-extension-p x y))))))
        :endif)


(acl2::process-ifdefs
 (with-output :off (prove)
   (defines fgl-unify-term/gobj
     :prepwork
     ((local (in-theory (disable symbol-listp
                                 member-equal
                                 len
                                 equal-of-booleans-rewrite
                                 not
                                 acl2::consp-when-member-equal-of-atom-listp
                                 acl2::consp-of-car-when-alistp
                                 acl2::subsetp-member)))
      (local (defthm and*-rem-second-boolean
               (implies (booleanp a)
                        (equal (and* a t) a))
               :hints(("Goal" :in-theory (enable and*))))))
     (define fgl-unify-term/gobj ((pat pseudo-termp)
                                  (x fgl-object-p)
                                   (alist fgl-object-bindings-p)
                                   &optional ((bfrstate bfrstate-p) 'bfrstate))
       :guard (bfr-listp (fgl-object-bfrlist x) bfrstate)
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       :measure (two-nats-measure (pseudo-term-count pat) 1)
       :hints ((and stable-under-simplificationp
                    '(:expand ((pseudo-term-count pat)
                               (pseudo-term-list-count (pseudo-term-call->args pat))
                               (pseudo-term-list-count (cdr (pseudo-term-call->args pat))))
                      :in-theory (enable equal-of-len))))
       :ruler-extenders :all
       :measure-debug t
       :verify-guards nil
       (b* ((alist (fgl-object-bindings-fix alist))
            (x (fgl-object-fix x))
            (x.kind (fgl-object-kind x))
            ((when (fgl-object-kind-eq x.kind :g-concrete))
             (fgl-unify-concrete pat (g-concrete->val x) alist))
            ((when (fgl-object-kind-eq x.kind :g-map))
             (fgl-unify-term/gobj-map pat (g-map->alist x) alist)))
         (pseudo-term-case pat
           :const (mv nil nil) ;; only matches when concrete, taken care of above.
           :var (let ((pair (hons-assoc-equal pat.name alist)))
                  (if pair
                      (if (hons-equal x (cdr pair))
                          (mv t alist)
                        (mv nil nil))
                    (mv t (cons (cons pat.name x) alist))))

           :fncall (b* ((fn pat.fn)
                        ((when (and** (eq fn 'if)
                                      (eql (len pat.args) 3)
                                      (fgl-object-kind-eq x.kind :g-ite)))
                         (b* (((g-ite x)))
                           (fgl-unify-term/gobj-if
                            (first pat.args) (second pat.args) (third pat.args)
                            x.test x.then x.else alist)))

                        ((when (and** (or** (eq fn 'intcons)
                                            (eq fn 'intcons*))
                                      (int= (len pat.args) 2)
                                      (fgl-object-kind-eq x.kind :g-integer)))
                         (b* ((bits (g-integer->bits x))
                              ((mv first rest end) (first/rest/end bits))
                              ((when (and end (not (eq fn 'intcons*))))
                               (mv nil nil))
                              ((mv car-ok alist)
                               (fgl-unify-term/gobj (first pat.args)
                                                     (mk-g-boolean first)
                                                     alist))
                              ((unless car-ok) (mv nil nil)))
                           (fgl-unify-term/gobj (second pat.args)
                                                 (mk-g-integer rest)
                                                 alist)))
                        ((when (and** (eq fn 'endint)
                                      (int= (len pat.args) 1)
                                      (fgl-object-kind-eq x.kind :g-integer)))
                         (b* ((bits (g-integer->bits x))
                              ((unless (s-endp bits)) (mv nil nil)))
                           (fgl-unify-term/gobj (first pat.args) (mk-g-boolean (car bits)) alist)))

                        ((when (and** (eq fn 'int)
                                      (int= (len pat.args) 1)
                                      (fgl-object-kind-eq x.kind :g-integer)))
                         (fgl-unify-term/gobj (first pat.args) x alist))

                        ((when (and** (eq fn 'bool)
                                      (int= (len pat.args) 1)
                                      (fgl-object-kind-eq x.kind :g-boolean)))
                         (fgl-unify-term/gobj (first pat.args) x alist))

                        ((when (fgl-object-kind-eq x.kind :g-apply))
                         (b* (((g-apply x)))
                           (fgl-unify-term/gobj-fn/args
                            pat.fn pat.args x.fn x.args alist)))
                        ((when (fgl-object-kind-eq x.kind :g-cons))
                         (b* (((g-cons x))
                              ((unless (and (eq fn 'cons)
                                            (int= (len pat.args) 2)))
                               (mv nil nil))
                              ((mv car-ok alist) (fgl-unify-term/gobj (first pat.args) x.car alist))
                              ((unless car-ok) (mv nil nil)))
                           (fgl-unify-term/gobj (second pat.args) x.cdr alist))))
                     (mv nil nil))
           ;; don't support unifying with lambdas
           :otherwise (mv nil nil))))

     (define fgl-unify-term/gobj-map ((pat pseudo-termp)
                                      (x fgl-object-alist-p)
                                      (alist fgl-object-bindings-p)
                                      &optional ((bfrstate bfrstate-p) 'bfrstate))
       :guard (bfr-listp (fgl-object-alist-bfrlist x) bfrstate)
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       :measure (two-nats-measure (pseudo-term-count pat) 0)
       (b* ((x (fgl-object-alist-fix x))
            ((when (atom x))
             (fgl-unify-concrete pat x alist))
            (alist (fgl-object-bindings-fix alist)))
         (pseudo-term-case pat
           :var (b* ((pair (hons-assoc-equal pat.name alist))
                     ((unless pair)
                      (mv t (cons (cons pat.name (g-map '(:g-map) x)) alist)))
                     (obj (cdr pair))
                     ((unless (fgl-object-case obj
                                :g-map
                                (hons-equal x obj.alist)
                                :otherwise nil))
                      (mv nil nil)))
                  (mv t alist))
           :fncall
           (b* (((unless (and (eq pat.fn 'cons)
                              (eql (len pat.args) 2)))
                 (mv nil nil))
                ((list pair-pat rest-pat) pat.args)
                ((cons (cons x-key val-obj) rest-alist) x)
                ((mv ok alist)
                 (fgl-unify-term/gobj-map-pair pair-pat x-key val-obj alist))
                ((unless ok) (mv nil nil)))
             (fgl-unify-term/gobj-map rest-pat rest-alist alist))
           :otherwise (mv nil nil))))

     (define fgl-unify-term/gobj-map-pair ((pat pseudo-termp)
                                           (x-key)
                                           (val-obj fgl-object-p)
                                           (alist fgl-object-bindings-p)
                                           &optional ((bfrstate bfrstate-p) 'bfrstate))
       :measure (two-nats-measure (pseudo-term-count pat) 1)
       :guard (bfr-listp (fgl-object-bfrlist val-obj))
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       (b* ((alist (fgl-object-bindings-fix alist)))
         (pseudo-term-case pat
           :const (b* (((unless (consp pat.val)) (mv nil nil))
                       ((cons key val) pat.val)
                       ((unless (and (hons-equal key x-key)
                                     (fgl-object-case val-obj
                                       :g-concrete (hons-equal val-obj.val val)
                                       :otherwise nil)))
                        (mv nil nil)))
                    (mv t alist))
           :var (b* ((pair (hons-assoc-equal pat.name alist))
                     (pair-obj (g-cons (g-concrete x-key) val-obj))
                     ((unless pair)
                      (mv t (cons (cons pat.name pair-obj)
                                  alist)))
                     (obj (cdr pair))
                     ((unless (hons-equal obj pair-obj))
                      (mv nil nil)))
                  (mv t alist))
           :fncall (b* (((unless (and (eq pat.fn 'cons)
                                      (eql (len pat.args) 2)))
                         (mv nil nil))
                        ((list key-pat val-pat) pat.args)
                        ((mv ok alist) (fgl-unify-concrete key-pat x-key alist))
                        ((unless ok) (mv nil nil)))
                     (fgl-unify-term/gobj val-pat val-obj alist))
           :otherwise (mv nil nil))))


     (define fgl-unify-term/gobj-fn/args ((pat-fn pseudo-fnsym-p)
                                          (pat-args pseudo-term-listp)
                                          (x-fn pseudo-fnsym-p)
                                          (x-args fgl-objectlist-p)
                                          (alist fgl-object-bindings-p)
                                          &optional ((bfrstate bfrstate-p) 'bfrstate))
       :measure (two-nats-measure (pseudo-term-list-count pat-args) 1)
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       :guard (bfr-listp (fgl-objectlist-bfrlist x-args) bfrstate)
       (b* ((pat-fn (pseudo-fnsym-fix pat-fn))
            (pat-args (pseudo-term-list-fix pat-args))
            (x-args (fgl-objectlist-fix x-args)))
         (if (eq (pseudo-fnsym-fix x-fn) pat-fn)
             (cond ((eq pat-fn 'equal)
                    ;; Special case for EQUAL -- try both ways!
                    (b* (((unless (eql (len pat-args) 2))
                          (mv nil nil))
                         ((mv ok alist1) (fgl-unify-term/gobj-commutative-args
                                          (first pat-args) (second pat-args)
                                          (first x-args) (second x-args)
                                          alist))
                         ((when ok) (mv ok alist1)))
                      (fgl-unify-term/gobj-commutative-args
                       (first pat-args) (second pat-args)
                       (second x-args) (first x-args)
                       alist)))
                   ((eq pat-fn 'if)
                    (b* (((unless (and (eql (len pat-args) 3)
                                       (eql (len x-args) 3)))
                          (mv nil nil)))
                      (fgl-unify-term/gobj-if
                       (first pat-args) (second pat-args) (third pat-args)
                       (first x-args) (second x-args) (third x-args)
                       alist)))
                   (t (fgl-unify-term/gobj-list pat-args x-args alist)))
           (mv nil nil))))


     (define fgl-unify-term/gobj-if ((pat-test pseudo-termp)
                                      (pat-then pseudo-termp)
                                      (pat-else pseudo-termp)
                                      (x-test fgl-object-p)
                                      (x-then fgl-object-p)
                                      (x-else fgl-object-p)
                                      (alist fgl-object-bindings-p)
                                      &optional ((bfrstate bfrstate-p) 'bfrstate))
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       :measure (two-nats-measure
                 (+ (pseudo-term-count pat-test)
                    (pseudo-term-count pat-then)
                    (pseudo-term-count pat-else))
                 1)
       :guard (and (bfr-listp (fgl-object-bfrlist x-test))
                   (bfr-listp (fgl-object-bfrlist x-then))
                   (bfr-listp (fgl-object-bfrlist x-else)))

       (b* (((mv ok alist1)
             (fgl-unify-term/gobj-if1 pat-test pat-then pat-else
                                     x-test x-then x-else alist))
            ((when ok) (mv ok alist1))
            ((mv bool-ok bool-fix) (gobj-syntactic-boolean-fix x-test))
            ((unless bool-ok) (mv nil nil))
            (neg-test (gobj-syntactic-boolean-negate bool-fix)))
         (fgl-unify-term/gobj-if1 pat-test pat-then pat-else
                                  neg-test x-else x-then alist)))

     (define fgl-unify-term/gobj-if1 ((pat-test pseudo-termp)
                                      (pat-then pseudo-termp)
                                      (pat-else pseudo-termp)
                                      (x-test fgl-object-p)
                                      (x-then fgl-object-p)
                                      (x-else fgl-object-p)
                                      (alist fgl-object-bindings-p)
                                      &optional ((bfrstate bfrstate-p) 'bfrstate))
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       :measure (two-nats-measure
                 (+ (pseudo-term-count pat-test)
                    (pseudo-term-count pat-then)
                    (pseudo-term-count pat-else))
                 0)
       :guard (and (bfr-listp (fgl-object-bfrlist x-test))
                   (bfr-listp (fgl-object-bfrlist x-then))
                   (bfr-listp (fgl-object-bfrlist x-else)))

       (b* (((mv ok alist) (fgl-unify-term/gobj pat-test x-test alist))
            ((unless ok) (mv nil nil))
            ((mv ok alist) (fgl-unify-term/gobj pat-then x-then alist))
            ((unless ok) (mv nil nil)))
         (fgl-unify-term/gobj pat-else x-else alist)))

     (define fgl-unify-term/gobj-commutative-args ((pat1 pseudo-termp)
                                                    (pat2 pseudo-termp)
                                                    (x1 fgl-object-p)
                                                    (x2 fgl-object-p)
                                                    (alist fgl-object-bindings-p)
                                                    &optional ((bfrstate bfrstate-p) 'bfrstate))
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       :measure (two-nats-measure (+ (pseudo-term-count pat1)
                                     (pseudo-term-count pat2))
                                  0)
       :guard (and (bfr-listp (fgl-object-bfrlist x1))
                   (bfr-listp (fgl-object-bfrlist x2)))
       (b* (((mv ok alist) (fgl-unify-term/gobj pat1 x1 alist))
            ((unless ok) (mv nil nil)))
         (fgl-unify-term/gobj pat2 x2 alist)))


     (define fgl-unify-term/gobj-list ((pat pseudo-term-listp)
                                        (x fgl-objectlist-p)
                                        (alist fgl-object-bindings-p)
                                        &optional ((bfrstate bfrstate-p) 'bfrstate))
       :returns (mv flag
                    (new-alist fgl-object-bindings-p))
       :guard (bfr-listp (fgl-objectlist-bfrlist x))
       :measure (two-nats-measure (pseudo-term-list-count pat)
                                  0)
       (b* (((when (atom pat))
             (if (mbe :logic (atom x) :exec (eq x nil))
                 (mv t (fgl-object-bindings-fix alist))
               (mv nil nil)))
            ((when (atom x)) (mv nil nil))
            ((mv ok alist)
             (fgl-unify-term/gobj (car pat) (car x) alist))
            ((unless ok) (mv nil nil)))
         (fgl-unify-term/gobj-list (cdr pat) (cdr x) alist)))
     ///
     (local
      (make-event
       `(in-theory (disable . ,(getpropc 'fgl-unify-term/gobj-fn 'acl2::recursivep
                                         nil (w state))))))

     (local (defthm member-scdr
              (implies (not (member k x))
                       (not (member k (scdr x))))
              :hints(("Goal" :in-theory (enable scdr)))))

     (verify-guards fgl-unify-term/gobj-fn
       :hints (("goal" :expand ((fgl-object-bfrlist x)
                                (fgl-objectlist-bfrlist (g-apply->args x)))
                :in-theory (enable bfr-listp-when-not-member-witness))))

     (local (defthm not-member-of-scdr
              (implies (not (member b x))
                       (not (member b (scdr x))))
              :hints(("Goal" :in-theory (enable scdr)))))


     (fty::deffixequiv-mutual fgl-unify-term/gobj)

     (local (in-theory (enable bfr-listp-when-not-member-witness)))

     (std::def-retgen-fnset fgl-unify-fnset (fgl-unify-concrete fgl-unify-term/gobj))

     (std::defretgen bfr-listp-of-<fn>
       :formal-hyps
       (((fgl-object-bindings-p alist)    (bfr-listp (fgl-object-bindings-bfrlist alist)))
        ((fgl-object-p x)                 (bfr-listp (fgl-object-bfrlist x)))
        ((fgl-objectlist-p x)             (bfr-listp (fgl-objectlist-bfrlist x)))
        ((fgl-object-alist-p x)           (bfr-listp (fgl-object-alist-bfrlist x))))
       :rules ((t (:add-concl (bfr-listp (fgl-object-bindings-bfrlist new-alist))))
               (:mutrec
                (:add-keyword
                 :hints ('(:expand ((:free (x-key) <call>))))))
               (:recursive
                (:add-keyword
                 :hints (("goal" :induct <call>
                          :in-theory (enable (:i <fn>))
                          :expand ((:free (x) <call>)))))))
       :functions fgl-unify-fnset)


     (ifndef "DEFS_ONLY"


       (std::defretgen <fn>-alist-lookup-when-present
         :rules
         ((t (:add-hyp (and (hons-assoc-equal k (fgl-object-bindings-fix alist))
                            flag))
             (:add-concl (equal (hons-assoc-equal k new-alist)
                                (hons-assoc-equal k (fgl-object-bindings-fix alist)))))
          (:mutrec
           (:add-keyword
            :hints ('(:expand ((:free (x-key) <call>))))))
          (:recursive
           (:add-keyword
            :hints (("goal" :induct <call>
                     :in-theory (enable (:i <fn>))
                     :expand ((:free (x) <call>)))))))
       :functions fgl-unify-fnset)


       (std::defretgen <fn>-fgl-bindings-extension-p
         :rules
         ((t (:add-hyp (and (fgl-bindings-extension-p alist base)
                            flag))
             (:add-concl (fgl-bindings-extension-p new-alist base)))
          (:mutrec
           (:add-keyword
            :hints ('(:expand ((:free (x-key) <call>))))))
          (:recursive
           (:add-keyword
            :hints (("goal" :induct <call>
                     :in-theory (enable (:i <fn>))
                     :expand ((:free (x) <call>)))))))
         :functions fgl-unify-fnset)

       (defthm fgl-bindings-extension-p-of-fgl-unify-term/gobj-top
         (b* (((mv flag new-alist) (fgl-unify-term/gobj pat x alist)))
           (implies flag
                    (fgl-bindings-extension-p new-alist alist))))


       (std::defretgen <fn>-preserves-all-keys-bound
         :rules
         ((t (:add-hyp (and (subsetp keys (alist-keys (fgl-object-bindings-fix alist)))
                            flag))
             (:add-concl (subsetp keys (alist-keys new-alist))))
          (:mutrec
           (:add-keyword
            :hints ('(:expand ((:free (x-key) <call>))))))
          (:recursive
           (:add-keyword
            :hints (("goal" :induct <call>
                     :in-theory (enable (:i <fn>))
                     :expand ((:free (x) <call>)))))))
       :functions fgl-unify-fnset)

       (local (defthm termlist-vars-when-consp
                (implies (consp x)
                         (equal (termlist-vars x)
                                (union-eq (termlist-vars (cdr x))
                                          (term-vars (car x)))))
                :hints (("goal" :expand ((termlist-vars x))))))

       ;; (local
       ;;  (defthmd equal-of-len
       ;;    (implies (syntaxp (quotep n))
       ;;             (equal (Equal (len x) n)
       ;;                    (cond ((eql n 0) (atom x))
       ;;                          ((zp n) nil)
       ;;                          (t (and (consp x)
       ;;                                  (equal (len (cdr x)) (1- n)))))))
       ;;    :hints(("Goal" :in-theory (enable len)))))
       (local (in-theory (enable equal-of-len)))



       (std::defretgen all-keys-bound-of-<fn>
         :rules
         ((t (:add-hyp flag)
             (:each-formal :type pseudo-termp :var pat
              :action (:add-concl (subsetp (term-vars pat) (alist-keys new-alist))))
             (:each-formal :type pseudo-term-listp :var pat
              :action (:add-concl (subsetp (termlist-vars pat) (alist-keys new-alist)))))
          (:mutrec
           (:add-keyword
            :hints ('(:expand ((:free (x-key) <call>)))
                    (and stable-under-simplificationp
                         '(:expand ((term-vars pat)))))))
          (:recursive
           (:add-keyword
            :hints (("goal" :induct <call>
                     :in-theory (enable (:i <fn>))
                     :expand ((:free (x) <call>)
                              (term-vars pat)))))))
         :functions fgl-unify-fnset)

       (std::defretgen <fn>-preserves-eval-when-all-keys-bound
         :rules
         ((t (:add-hyp
              (and flag
                   (subsetp (term-vars term)
                            (alist-keys (fgl-object-bindings-fix alist)))))
             (:add-concl
              (equal (fgl-ev term (fgl-object-bindings-eval new-alist env))
                     (fgl-ev term (fgl-object-bindings-eval alist env)))))
          (:mutrec
           (:add-keyword
            :hints ('(:expand ((:free (x-key) <call>)
                               (:free (a b)
                                (fgl-object-bindings-eval (cons a b) env)))))))
          (:recursive
           (:add-keyword
            :hints (("goal" :induct <call>
                     :in-theory (enable (:i <fn>))
                     :expand ((:free (x) <call>)
                              (:free (a b)
                               (fgl-object-bindings-eval (cons a b) env))))))))
       :functions fgl-unify-fnset)


       ;; (local (defthm not-of-g-object-fix
       ;;          (implies (not (fgl-object-fix x))
       ;;                   (fgl-object-equiv x nil))
       ;;          :rule-classes :forward-chaining))

       (local (defthm logcons-bit-minus
                (implies (bitp b)
                         (equal (logcons b (- b))
                                (- b)))
                :hints(("Goal" :in-theory (enable bitp)))))

       (local (defthm not-quote-when-equal-fn
                (implies (equal fn (acl2::pseudo-term-fncall->fn x))
                         (not (equal fn 'quote)))))

       (local (defthm gobj-bfr-list-eval-when-not-s-endp
                (implies (not (s-endp bits))
                         (equal (bools->int (gobj-bfr-list-eval bits env))
                                (logcons (bool->bit (gobj-bfr-eval (car bits) env))
                                         (bools->int (gobj-bfr-list-eval (scdr bits) env)))))
                :hints(("Goal" :in-theory (enable scdr s-endp bools->int)
                        :expand ((gobj-bfr-list-eval bits env))))))

       (local (defthm gobj-bfr-list-eval-when-s-endp
                (implies (s-endp bits)
                         (equal (bools->int (gobj-bfr-list-eval bits env))
                                (- (bool->bit (gobj-bfr-eval (car bits) env)))))
                :hints(("Goal" :in-theory (enable scdr s-endp bools->int)
                        :expand ((gobj-bfr-list-eval bits env))))))

       (local
        (progn
          (defthm fgl-object-eval-when-gobj-syntactic-booleanp
            (implies (gobj-syntactic-booleanp x)
                     (equal (fgl-object-eval x env)
                            (gobj-bfr-eval (gobj-syntactic-boolean->bool x) env)))
            :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp
                                              gobj-syntactic-boolean->bool
                                              booleanp))))

          (defret fgl-object-eval-of-gobj-syntactic-boolean-fix
            (implies okp
                     (equal (gobj-bfr-eval (gobj-syntactic-boolean->bool new-x) env)
                            (bool-fix (fgl-object-eval x env))))
            :hints(("Goal" :in-theory (enable gobj-syntactic-boolean->bool
                                              gobj-syntactic-boolean-fix
                                              gobj-syntactic-booleanp)))
            :fn gobj-syntactic-boolean-fix)))

       ;; (local (defthm fgl-objectlist-eval-when-consp
       ;;          (implies (consp x)
       ;;                   (equal (fgl-objectlist-eval x env)
       ;;                          (cons (fgl-object-eval (car x) env)
       ;;                                (fgl-objectlist-eval (cdr x) env))))
       ;;          :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

       (local (defthm ev-car-of-kwote-lst
                (equal (fgl-ev (car (kwote-lst x)) a)
                       (car x))
                :hints(("Goal" :in-theory (enable kwote-lst)))))

       (local (defthm cdr-of-kwote-lst
                (equal (cdr (kwote-lst x))
                       (kwote-lst (cdr x)))
                :hints(("Goal" :in-theory (enable kwote-lst)))))

       (local (defthm car-of-fgl-objectlist-eval
                (equal (car (fgl-objectlist-eval x env))
                       (fgl-object-eval (car x) env))
                :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

       (local (defthm cdr-of-fgl-objectlist-eval
                (equal (cdr (fgl-objectlist-eval x env))
                       (fgl-objectlist-eval (cdr x) env))
                :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

       (local (defthm fgl-object-alist-eval-when-atom
                (implies (not (consp (fgl-object-alist-fix x)))
                         (equal (fgl-object-alist-eval x env)
                                (fgl-object-alist-fix x)))
                :hints (("goal" :in-theory (enable len)
                         :expand ((fgl-object-alist-eval x env)
                                  (fgl-object-alist-fix x))
                         :induct (len x)))))

       (local (in-theory (disable kwote-lst)))

       (local (defthmd fgl-object-alist-eval-in-terms-of-fix
                (equal (fgl-object-alist-eval x env)
                       (let ((x (fgl-object-alist-fix x)))
                         (if (atom x)
                             x
                           (cons (cons (caar x)
                                       (fgl-object-eval (cdar x) env))
                                 (fgl-object-alist-eval (cdr x) env)))))
                :hints (("goal" :in-theory (enable len)
                         :expand ((fgl-object-alist-eval x env)
                                  (fgl-object-alist-fix x))
                         :induct (len x)))
                :rule-classes :definition))


       (std::defretgen <fn>-correct
         :rules
         ((t (:add-hyp (and flag
                            (equal bfrstate (logicman->bfrstate))))
             (:add-bindings
              ((ev-alist (fgl-object-bindings-eval new-alist env)))))
          ((:fnname fgl-unify-term/gobj)
           (:add-concl
            (equal (fgl-ev pat ev-alist)
                   (fgl-object-eval x env))))
          ((:fnname fgl-unify-term/gobj-map)
           (:add-concl
            (equal (fgl-ev pat ev-alist)
                   (fgl-object-alist-eval x env))))
          ((:fnname fgl-unify-term/gobj-map-pair)
           (:add-concl
            (equal (fgl-ev pat ev-alist)
                   (cons x-key (fgl-object-eval val-obj env)))))
          ((:fnname fgl-unify-term/gobj-commutative-args)
           (:add-concl
            (equal (equal (fgl-ev pat1 ev-alist)
                          (fgl-ev pat2 ev-alist))
                   (equal (fgl-object-eval x1 env)
                          (fgl-object-eval x2 env)))))
          ((or (:fnname fgl-unify-term/gobj-if)
               (:fnname fgl-unify-term/gobj-if1))
           (:add-concl
            (equal (if (fgl-ev pat-test ev-alist)
                       (fgl-ev pat-then ev-alist)
                     (fgl-ev pat-else ev-alist))
                   (if (fgl-object-eval x-test env)
                       (fgl-object-eval x-then env)
                     (fgl-object-eval x-else env)))))
          ((:fnname fgl-unify-term/gobj-list)
           (:add-concl
            (equal (fgl-ev-list pat ev-alist)
                   (fgl-objectlist-eval x env))))
          ((:fnname fgl-unify-term/gobj-fn/args)
           (:add-concl
            (equal (fgl-ev (pseudo-term-fncall pat-fn pat-args)
                           ev-alist)
                   (fgl-ev (pseudo-term-fncall
                            x-fn
                            (kwote-lst (fgl-objectlist-eval x-args env)))
                           nil))))
          ((:fnname fgl-unify-concrete)
           (:add-concl
            (equal (fgl-ev pat ev-alist)
                   x)))
          ((and :mutrec
                (not (:fnname fgl-unify-term/gobj)))
           (:add-keyword :hints ('(:expand ((:free (x-key) <call>)
                                            (fgl-objectlist-eval x env)
                                            (fgl-objectlist-eval x-args env)
                                            (:with fgl-object-alist-eval-in-terms-of-fix
                                             (fgl-object-alist-eval x env)))
                                   :in-theory (enable kwote-lst
                                                      fgl-ev-of-fncall-args)))))
          (:recursive
           (:add-keyword
            :hints (("goal" :induct <call>
                     :in-theory (enable (:i <fn>))
                     :expand ((:free (x) <call>)
                              (:free (a b)
                               (fgl-object-bindings-eval (cons a b) env)))))))

          ((:fnname fgl-unify-term/gobj)
           (:add-keyword
            :hints ('(:expand (<call>
                               (fgl-unify-term/gobj nil x alist))
                      :in-theory (enable fgl-apply
                                         ;; fgl-ev-of-fncall-args
                                         ))
                    (and stable-under-simplificationp
                         '(:expand ((fgl-object-eval x env))
                           :do-not-induct t))
                    (acl2::use-termhint
                     (b* (((when (fgl-object-case x :g-concrete)) nil))
                       (pseudo-term-case pat
                         :const nil
                         :var nil
                         :lambda nil
                         :fncall
                         (b* ((fn pat.fn)
                              ((when (and** (eq fn 'if)
                                            (eql (len pat.args) 3)
                                            (fgl-object-case x :g-ite)))
                               (b* ((bits (g-integer->bits x))
                                    ((unless (atom (cdr bits))) nil))
                                 `(:in-theory (enable equal-of-len)
                                   :expand (;;(gobj-bfr-list-eval ,(acl2::hq bits) env)
                                            ;; (:free (a b) (bools->int (cons a b)))
                                            (gobj-bfr-list-eval nil env)))))
                              ((when (and** (or** (eq fn 'intcons)
                                                  (eq fn 'intcons*))
                                            (int= (len pat.args) 2)
                                            (fgl-object-case x :g-integer)))
                               (b* ((bits (g-integer->bits x))
                                    ((mv first rest end) (first/rest/end bits))
                                    ((when (and end (not (eq fn 'intcons*))))
                                     nil))
                                 `(:in-theory (enable equal-of-len or*)
                                   :expand (;; (gobj-bfr-list-eval ,(acl2::hq bits) env)
                                            ;; (:free (a b) (bools->int (cons a b)))
                                            (gobj-bfr-list-eval nil env)))))
                              ((when (and** (eq fn 'endint)
                                            (int= (len pat.args) 1)
                                            (fgl-object-case x :g-integer)))
                               (b* ((bits (g-integer->bits x))
                                    ((mv first rest end) (first/rest/end bits)))
                                 `(:in-theory (enable equal-of-len)
                                   :expand (;; (gobj-bfr-list-eval ,(acl2::hq bits) env)
                                            ;; (:free (a b) (bools->int (cons a b)))
                                            ))))
                              ((when (and (fgl-object-case x :g-apply)
                                          (equal fn (g-apply->fn x))))
                               '(:in-theory (enable fgl-ev-of-fncall-args))))
                           nil))))))))
       :functions fgl-unify-fnset)
       :endif))))
