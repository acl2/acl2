; GL - A Symbolic Simulation Framework for ACL2
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

(ifdef "THMS_ONLY"
  (include-book "glcp-unify-defs")
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
  (defsection fgl-object-alist-eval
    (local (in-theory (enable gl-object-alist-fix
                              fgl-object-alist-eval)))

    (defthm lookup-in-fgl-object-alist-eval
      (equal (hons-assoc-equal k (fgl-object-alist-eval x env))
             (b* ((look (hons-assoc-equal k (gl-object-alist-fix x))))
               (and look
                    (cons k (fgl-object-eval (cdr look) env)))))
      :hints(("Goal" :in-theory (enable hons-assoc-equal))))

    

    (local (defthm alistp-when-gl-object-alist-p-rw
             (implies (gl-object-alist-p x)
                      (alistp x))
             :hints(("Goal" :in-theory (enable gl-object-alist-p)))))

    (local (defthm alistp-when-symbol-alistp
             (implies (symbol-alistp x)
                      (alistp x))
             :hints(("Goal" :in-theory (enable symbol-alistp)))))
    
    (defthm alist-keys-of-fgl-object-alist-eval
      (equal (alist-keys (fgl-object-alist-eval x env))
             (alist-keys (gl-object-alist-fix x)))))
  :endif)

(acl2::process-ifdefs
 (define glcp-unify-concrete ((pat pseudo-termp)
                              (x) ;; value
                              (alist gl-object-alist-p))
   :returns (mv flag
                (new-alist gl-object-alist-p))
   :verify-guards nil
   :measure (pseudo-term-count pat)
   (b* ((alist (gl-object-alist-fix alist)))
     (pseudo-term-case pat
       :null (if (eq x nil)
                 (mv t alist)
               (mv nil nil))
       :var (b* ((pair (hons-assoc-equal pat.name alist))
                 ((unless pair)
                  (mv t (cons (cons pat.name (g-concrete x)) alist)))
                 (obj (cdr pair)))
              (gl-object-case obj
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
               (glcp-unify-concrete (first pat.args) x alist)))
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
                  ((mv ok alist) (glcp-unify-concrete bitvar (acl2::bit->bool (logcar x)) alist))
                  ((unless ok) (mv nil nil)))
               (glcp-unify-concrete (second pat.args) (logcdr x) alist)))
            ((when (eq fn 'endint))
             (b* (((unless (int= (len pat.args) 1)) (mv nil nil))
                  ((unless (or (eql x -1) (eql x 0))) (mv nil nil))
                  (bitvar (first pat.args))
                  ((unless (pseudo-term-case bitvar :var))
                   (mv nil nil)))
               (glcp-unify-concrete bitvar (acl2::bit->bool (logcar x)) alist)))
            ((when (eq fn 'int))
             (b* (((unless (int= (len pat.args) 1)) (mv nil nil))
                  ((unless (integerp x)) (mv nil nil)))
               (glcp-unify-concrete (first pat.args) x alist)))
            ((when (eq fn 'bool))
             (b* (((unless (int= (len pat.args) 1)) (mv nil nil))
                  ((unless (booleanp x)) (mv nil nil)))
               (glcp-unify-concrete (first pat.args) x alist)))
            ((when (eq fn 'cons))
             (b* (((unless (int= (len pat.args) 2)) (mv nil nil))
                  ((unless (consp x)) (mv nil nil))
                  ((mv car-ok alist)
                   (glcp-unify-concrete (first pat.args) (car x) alist))
                  ((unless car-ok) (mv nil nil)))
               (glcp-unify-concrete (second pat.args) (cdr x) alist))))
         (mv nil nil))
       :otherwise (mv nil nil)))
   ///
   (local (in-theory (disable symbol-listp
                              (:d glcp-unify-concrete)
                              len
                              not
                              unsigned-byte-p
                              equal-of-booleans-rewrite
                              acl2::consp-when-member-equal-of-atom-listp
                              acl2::symbolp-of-car-when-symbol-listp
                              gl-object-alist-bfrlist
                              member-equal
                              acl2::consp-of-car-when-alistp)))

   (ifndef "DEFS_ONLY"
     (local (in-theory (disable acl2::consp-of-node-list-fix-x-normalize-const))) 
     :endif)

   (verify-guards glcp-unify-concrete)

   (defret bfrlist-of-<fn>
     (implies (not (member b (gl-object-alist-bfrlist alist)))
              (not (member b (gl-object-alist-bfrlist new-alist))))
     :hints(("Goal" :induct <call>)
            (acl2::use-termhint
             `(:expand ((glcp-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist))
                        (gl-object-alist-bfrlist ,(acl2::hq new-alist)))))))

   (ifndef "DEFS_ONLY"
     (local (defthm equal-of-len
              (implies (syntaxp (quotep n))
                       (equal (Equal (len x) n)
                              (cond ((eql n 0) (atom x))
                                    ((zp n) nil)
                                    (t (and (consp x)
                                            (equal (len (cdr x)) (1- n)))))))
              :hints(("Goal" :in-theory (enable len)))))

     (defret <fn>-alist-lookup-when-present
       (implies (and (hons-assoc-equal k (gl-object-alist-fix alist))
                     flag)
                (equal (hons-assoc-equal k new-alist)
                       (hons-assoc-equal k (gl-object-alist-fix alist))))
       :hints (("goal" :induct <call>)
               (acl2::use-termhint
                `(:expand ((glcp-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

     (defret <fn>-preserves-all-keys-bound
       (implies (and (subsetp keys (alist-keys (gl-object-alist-fix alist)))
                     flag)
                (subsetp keys (alist-keys new-alist)))
       :hints (("goal" :induct <call>)
               (acl2::use-termhint
                `(:expand ((glcp-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

     (local (defthm termlist-vars-when-consp
              (implies (consp x)
                       (equal (termlist-vars x)
                              (union-eq (termlist-vars (cdr x))
                                        (term-vars (car x)))))
              :hints (("goal" :expand ((termlist-vars x))))))

     (defret all-keys-bound-of-<fn>
       (implies flag
                (subsetp (term-vars pat) (alist-keys new-alist)))
       :hints (("goal" :induct <call>)
               (acl2::use-termhint
                `(:expand ((glcp-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist))
                           (term-vars pat)
                           ;; (termlist-vars (cdr pat))
                           ;; (termlist-vars (cddr pat))
                           ;; (termlist-vars (cdddr pat))
                           )))))

     (local (defret var-lookup-of-<fn>
              (implies (and flag (pseudo-term-case pat :var))
                       (hons-assoc-equal (acl2::pseudo-term-var->name pat) new-alist))
              :hints (("goal" :use ((:instance all-keys-bound-of-glcp-unify-concrete))
                       :in-theory (e/d (term-vars)
                                       (all-keys-bound-of-glcp-unify-concrete))))))

     (defret <fn>-preserves-eval-when-all-keys-bound
       (implies (and flag
                     (subsetp (term-vars term)
                              (alist-keys (gl-object-alist-fix alist))))
                (equal (fgl-ev term (fgl-object-alist-eval new-alist env))
                       (fgl-ev term (fgl-object-alist-eval alist env))))
       :hints (("goal" :induct <call>)
               (acl2::use-termhint
                `(:expand ((glcp-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist))
                           (:free (a b) (fgl-object-alist-eval (cons a b) env)))))))

     (defret <fn>-correct
       (implies flag
                (equal (fgl-ev pat (fgl-object-alist-eval new-alist env))
                       x))
       :hints (("Goal" :induct <call>)
               (acl2::use-termhint
                `(:expand ((glcp-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

     (defret gl-object-alist-bfrlist-of-<fn>
       (equal (gl-object-alist-bfrlist new-alist)
              (and flag (gl-object-alist-bfrlist alist)))
       :hints (("Goal" :induct <call>)
               (acl2::use-termhint
                `(:expand ((glcp-unify-concrete ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))))))

     :endif)))

;; (local (defthm true-list-fix-of-boolean-list-fix
;;          (equal (acl2::true-list-fix (acl2::boolean-list-fix x))
;;                 (acl2::boolean-list-fix x))))

;; (local (defthm boolean-list-fix-of-true-list-fix
;;          (equal (acl2::boolean-list-fix (acl2::true-list-fix x))
;;                 (acl2::boolean-list-fix x))
;;          :hints(("Goal" :in-theory (enable acl2::boolean-list-fix)))))

;; (defrefinement acl2::list-equiv acl2::boolean-list-equiv
;;   :hints(("Goal" :in-theory (e/d (acl2::list-equiv)
;;                                  (boolean-list-fix-of-true-list-fix))
;;           :use ((:instance boolean-list-fix-of-true-list-fix)
;;                 (:instance boolean-list-fix-of-true-list-fix (x y))))))

(defthm bfrlist-of-mk-g-integer
  (implies (not (member v x))
           (not (member v (gl-object-bfrlist (mk-g-integer x)))))
  :hints(("Goal" :in-theory (enable mk-g-integer))))

(defthm bfrlist-of-mk-g-boolean
  (implies (not (equal v x))
           (not (member v (gl-object-bfrlist (mk-g-boolean x)))))
  :hints(("Goal" :in-theory (enable mk-g-boolean))))

(defthm bfrlist-of-mk-g-boolean-nonboolean
  (and (not (member nil (gl-object-bfrlist (mk-g-boolean x))))
       (not (member t (gl-object-bfrlist (mk-g-boolean x)))))
  :hints(("Goal" :in-theory (enable mk-g-boolean))))

(acl2::process-ifdefs
 (with-output :off (prove)
   (defines glcp-unify-term/gobj
     :prepwork
     ((local (in-theory (disable symbol-listp
                                 member-equal
                                 len
                                 equal-of-booleans-rewrite
                                 not
                                 acl2::consp-when-member-equal-of-atom-listp
                                 acl2::consp-of-car-when-alistp
                                 acl2::subsetp-member)))
      (ifndef "DEFS_ONLY"
        (local (in-theory (disable acl2::consp-of-node-list-fix-x-normalize-const)))
        :endif))
     (define glcp-unify-term/gobj ((pat pseudo-termp)
                                   (x gl-object-p)
                                   (alist gl-object-alist-p))
       :returns (mv flag
                    (new-alist gl-object-alist-p))
       :measure (pseudo-term-count pat)
       :verify-guards nil
       (b* ((alist (gl-object-alist-fix alist))
            (x (gl-object-fix x))
            (x.kind (gl-object-kind x))
            ((when (gl-object-kind-eq x.kind :g-concrete))
             (glcp-unify-concrete pat (g-concrete->val x) alist)))
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
                                      (gl-object-kind-eq x.kind :g-ite)))
                         (b* (((g-ite x))
                              ((mv ok alist)
                               (glcp-unify-term/gobj (first pat.args) x.test alist))
                              ((unless ok) (mv nil nil))
                              ((mv ok alist)
                               (glcp-unify-term/gobj (second pat.args) x.then alist))
                              ((unless ok) (mv nil nil)))
                           (glcp-unify-term/gobj (third pat.args) x.else alist)))

                        ((when (and** (or** (eq fn 'intcons)
                                            (eq fn 'intcons*))
                                      (int= (len pat.args) 2)
                                      (gl-object-kind-eq x.kind :g-integer)))
                         (b* ((bits (g-integer->bits x))
                              ((mv first rest end) (first/rest/end bits))
                              ((when (and end (not (eq fn 'intcons*))))
                               (mv nil nil))
                              ((mv car-ok alist)
                               (glcp-unify-term/gobj (first pat.args)
                                                     (mk-g-boolean first)
                                                     alist))
                              ((unless car-ok) (mv nil nil)))
                           (glcp-unify-term/gobj (second pat.args)
                                                 (mk-g-integer rest)
                                                 alist)))
                        ((when (and** (eq fn 'endint)
                                      (int= (len pat.args) 1)
                                      (gl-object-kind-eq x.kind :g-integer)))
                         (b* ((bits (g-integer->bits x))
                              ((unless (s-endp bits)) (mv nil nil)))
                           (glcp-unify-term/gobj (first pat.args) (mk-g-boolean (car bits)) alist)))

                        ((when (and** (eq fn 'int)
                                      (int= (len pat.args) 1)
                                      (gl-object-kind-eq x.kind :g-integer)))
                         (glcp-unify-term/gobj (first pat.args) x alist))

                        ((when (and** (eq fn 'bool)
                                      (int= (len pat.args) 1)
                                      (gl-object-kind-eq x.kind :g-boolean)))
                         (glcp-unify-term/gobj (first pat.args) x alist))

                        ((when (gl-object-kind-eq x.kind :g-apply))
                         (b* (((g-apply x)))
                           (if (eq x.fn fn)
                               (glcp-unify-term/gobj-list pat.args x.args alist)
                             (mv nil nil))))
                        ((when (gl-object-kind-eq x.kind :g-cons))
                         (b* (((g-cons x))
                              ((unless (and (eq fn 'cons)
                                            (int= (len pat.args) 2)))
                               (mv nil nil))
                              ((mv car-ok alist) (glcp-unify-term/gobj (first pat.args) x.car alist))
                              ((unless car-ok) (mv nil nil)))
                           (glcp-unify-term/gobj (second pat.args) x.cdr alist))))
                     (mv nil nil))
           ;; don't support unifying with lambdas
           :otherwise (mv nil nil))))

     (define glcp-unify-term/gobj-list ((pat pseudo-term-listp)
                                        (x gl-objectlist-p)
                                        (alist gl-object-alist-p))
       :returns (mv flag
                    (new-alist gl-object-alist-p))
       :measure (pseudo-term-list-count pat)
       (b* (((when (atom pat))
             (if (mbe :logic (atom x) :exec (eq x nil))
                 (mv t (gl-object-alist-fix alist))
               (mv nil nil)))
            ((when (atom x)) (mv nil nil))
            ((mv ok alist)
             (glcp-unify-term/gobj (car pat) (car x) alist))
            ((unless ok) (mv nil nil)))
         (glcp-unify-term/gobj-list (cdr pat) (cdr x) alist)))
     ///
     (local (in-theory (disable (:d glcp-unify-term/gobj)
                                (:d glcp-unify-term/gobj-list)))) 

     (verify-guards glcp-unify-term/gobj)

     (local (defthm not-member-of-scdr
              (implies (not (member b x))
                       (not (member b (scdr x))))
              :hints(("Goal" :in-theory (enable scdr)))))
     

     (fty::deffixequiv-mutual glcp-unify-term/gobj)

     (defret-mutual bfrlist-of-<fn>
       (defret bfrlist-of-<fn>
         (implies (and (not (member b (gl-object-alist-bfrlist alist)))
                       (not (member b (gl-object-bfrlist x)))
                       ;; (not (equal b nil))
                       )
                  (not (member b (gl-object-alist-bfrlist new-alist))))
         :hints ('(:expand ((:free (x) <call>)
                            (glcp-unify-term/gobj nil x alist)))
                 (and stable-under-simplificationp
                      '(:expand ((gl-object-bfrlist x)))))
         :fn glcp-unify-term/gobj)
       (defret bfrlist-of-<fn>
         (implies (and (not (member b (gl-object-alist-bfrlist alist)))
                       (not (member b (gl-objectlist-bfrlist x)))
                       ;; (not (equal b nil))
                       )
                  (not (member b (gl-object-alist-bfrlist new-alist))))
         :hints ('(:expand ((:free (x) <call>)
                            (gl-objectlist-bfrlist x))))
         :fn glcp-unify-term/gobj-list))
     

     (ifndef "DEFS_ONLY"
       
       (local
        (defthmd equal-of-len
          (implies (syntaxp (quotep n))
                   (equal (Equal (len x) n)
                          (cond ((eql n 0) (atom x))
                                ((zp n) nil)
                                (t (and (consp x)
                                        (equal (len (cdr x)) (1- n)))))))
          :hints(("Goal" :in-theory (enable len)))))

       (defret-mutual <fn>-alist-lookup-when-present
         (defret <fn>-alist-lookup-when-present
           (implies (and (hons-assoc-equal k (gl-object-alist-fix alist))
                         flag)
                    (equal (hons-assoc-equal k new-alist)
                           (hons-assoc-equal k (gl-object-alist-fix alist))))
           :hints ('(:expand (<call>
                              (glcp-unify-term/gobj nil x alist))))
           :fn glcp-unify-term/gobj)
         (defret <fn>-alist-lookup-when-present
           (implies (and (hons-assoc-equal k (gl-object-alist-fix alist))
                         flag)
                    (equal (hons-assoc-equal k new-alist)
                           (hons-assoc-equal k (gl-object-alist-fix alist))))
           :hints ('(:expand ((:free (x) <call>))))
           :fn glcp-unify-term/gobj-list))

       (defret-mutual <fn>-preserves-all-keys-bound
         (defret <fn>-preserves-all-keys-bound
           (implies (and (subsetp keys (alist-keys (gl-object-alist-fix alist)))
                         flag)
                    (subsetp keys (alist-keys new-alist)))
           :hints ('(:expand (<call>
                              (glcp-unify-term/gobj nil x alist))))
           :fn glcp-unify-term/gobj)
         (defret <fn>-preserves-all-keys-bound
           (implies (and (subsetp keys (alist-keys (gl-object-alist-fix alist)))
                         flag)
                    (subsetp keys (alist-keys new-alist)))
           :hints ('(:expand ((:free (x) <call>))))
           :fn glcp-unify-term/gobj-list))

       (local (defthm termlist-vars-when-consp
                (implies (consp x)
                         (equal (termlist-vars x)
                                (union-eq (termlist-vars (cdr x))
                                          (term-vars (car x)))))
                :hints (("goal" :expand ((termlist-vars x))))))

       (defret-mutual all-keys-bound-of-<fn>
         (defret all-keys-bound-of-<fn>
           (implies flag
                    (subsetp (term-vars pat) (alist-keys new-alist)))
           :hints ('(:expand (<call>
                              (glcp-unify-term/gobj nil x alist))
                     :in-theory (enable equal-of-len))
                   (and stable-under-simplificationp
                        '(:expand ((term-vars pat)))))
           :fn glcp-unify-term/gobj)
         (defret all-keys-bound-of-<fn>
           (implies flag
                    (subsetp (termlist-vars pat) (alist-keys new-alist)))
           :hints ('(:expand ((:free (x) <call>)
                              (termlist-vars pat))))
           :fn glcp-unify-term/gobj-list))

       (defret-mutual <fn>-preserves-eval-when-all-keys-bound
         (defret <fn>-preserves-eval-when-all-keys-bound
           (implies (and flag
                         (subsetp (term-vars term)
                                  (alist-keys (gl-object-alist-fix alist))))
                    (equal (fgl-ev term (fgl-object-alist-eval new-alist env))
                           (fgl-ev term (fgl-object-alist-eval alist env))))
           :hints ('(:expand (<call>
                              (glcp-unify-term/gobj nil x alist)
                              (:free (a b) (fgl-object-alist-eval (cons a b) env)))))
           :fn glcp-unify-term/gobj)
         (defret <fn>-preserves-eval-when-all-keys-bound
           (implies (and flag
                         (subsetp (term-vars term)
                                  (alist-keys (gl-object-alist-fix alist))))
                    (equal (fgl-ev term (fgl-object-alist-eval new-alist env))
                           (fgl-ev term (fgl-object-alist-eval alist env))))
           :hints ('(:expand ((:free (x) <call>))))
           :fn glcp-unify-term/gobj-list))

       ;; (local (defthm not-of-g-object-fix
       ;;          (implies (not (gl-object-fix x))
       ;;                   (gl-object-equiv x nil))
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
       
       (defret-mutual <fn>-correct
         (defret <fn>-correct
           (implies flag
                    (equal (fgl-ev pat (fgl-object-alist-eval new-alist env))
                           (fgl-object-eval x env)))
           :hints ('(:expand (<call>
                              (glcp-unify-term/gobj nil x alist))
                     :in-theory (enable fgl-apply
                                        ;; fgl-ev-of-fncall-args
                                        ))
                   (and stable-under-simplificationp
                        '(:expand ((fgl-object-eval x env))
                          :do-not-induct t))
                   (acl2::use-termhint
                    (b* (((when (gl-object-case x :g-concrete)) nil))
                      (pseudo-term-case pat
                        :const nil
                        :var nil
                        :lambda nil
                        :fncall
                        (b* ((fn pat.fn)
                             ((when (and** (eq fn 'if)
                                           (eql (len pat.args) 3)
                                           (gl-object-case x :g-ite)))
                              (b* ((bits (g-integer->bits x))
                                   ((unless (atom (cdr bits))) nil))
                                `(:in-theory (enable equal-of-len)
                                  :expand (;;(gobj-bfr-list-eval ,(acl2::hq bits) env)
                                           ;; (:free (a b) (bools->int (cons a b)))
                                           (gobj-bfr-list-eval nil env)))))
                             ((when (and** (or** (eq fn 'intcons)
                                                 (eq fn 'intcons*))
                                           (int= (len pat.args) 2)
                                           (gl-object-case x :g-integer)))
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
                                           (gl-object-case x :g-integer)))
                              (b* ((bits (g-integer->bits x))
                                   ((mv first rest end) (first/rest/end bits)))
                                `(:in-theory (enable equal-of-len)
                                  :expand (;; (gobj-bfr-list-eval ,(acl2::hq bits) env)
                                           ;; (:free (a b) (bools->int (cons a b)))
                                           ))))
                             ((when (and (gl-object-case x :g-apply)
                                         (equal fn (g-apply->fn x))))
                              '(:in-theory (enable fgl-ev-of-fncall-args))))
                          nil)))))
           :fn glcp-unify-term/gobj)
         (defret <fn>-correct
           (implies flag
                    (equal (fgl-ev-list pat (fgl-object-alist-eval new-alist env))
                           (fgl-objectlist-eval x env)))
           :hints ('(:expand ((:free (x) <call>)
                              (fgl-objectlist-eval x env)
                              (fgl-objectlist-eval nil env))))
           :fn glcp-unify-term/gobj-list))

       ;; (defret-mutual depends-on-of-<fn>
       ;;   (defret depends-on-of-<fn> 
       ;;     (implies (and (not (bfr-list-depends-on v (gl-object-alist-bfrlist alist)))
       ;;                   (not (bfr-list-depends-on v (gl-object-bfrlist x))))
       ;;              (not (bfr-list-depends-on v (gl-object-alist-bfrlist new-alist))))
       ;;     :hints ((acl2::use-termhint
       ;;              (acl2::termhint-seq
       ;;               `(:expand ((glcp-unify-term/gobj ,(acl2::hq pat) ,(acl2::hq x) ,(acl2::hq alist)))
       ;;                 :in-theory (enable* gl-object-bfrlist-when-thms))
       ;;               (b* (((when (acl2::variablep pat)) nil)
       ;;                    (fn (car pat))
       ;;                    ((when (eq fn 'quote)) nil)
       ;;                    ((when (or (and (eq fn 'endint)
       ;;                                    (int= (len pat) 2)
       ;;                                    (gl-object-case x :g-integer))
       ;;                               (and (or (eq fn 'intcons)
       ;;                                        (eq fn 'intcons*))
       ;;                                    (int= (len pat) 3)
       ;;                                    (gl-object-case x :g-integer))))
       ;;                     '(:in-theory (enable equal-of-len))))
       ;;                 nil))))
       ;;     :fn glcp-unify-term/gobj)
       ;;   (defret depends-on-of-<fn> 
       ;;     (implies (and (not (bfr-list-depends-on v (gl-object-alist-bfrlist alist)))
       ;;                   (not (bfr-list-depends-on v (gl-objectlist-bfrlist x))))
       ;;              (not (bfr-list-depends-on v (gl-object-alist-bfrlist new-alist))))
       ;;     :hints ('(:expand (:free (x) <call>)))
       ;;     :fn glcp-unify-term/gobj-list))

       :endif))))
