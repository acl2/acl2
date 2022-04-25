; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)
(include-book "centaur/fgl/checks" :dir :system) ;; integer-length-bound
(include-book "centaur/fgl/fgl-object" :dir :system) ;; for syntaxp checks
(include-book "../svex/lists")
(include-book "../svex/env-ops")
(include-book "svtv-fsm-override")
(local (include-book "centaur/bitops/ihsext-basics" :Dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/append" :dir :system))



(fgl::def-fgl-rewrite len-fgl
  (implies (and (equal consp (and (consp x) t))
                (syntaxp (fgl::fgl-object-case consp :g-concrete)))
           (equal (len x)
                  (if consp (+ 1 (len (cdr x))) 0))))

(fgl::remove-fgl-rewrite len)

(fgl::def-fgl-rewrite equal-of-len
  (implies (syntaxp (fgl::fgl-object-case n :g-concrete))
           (equal (equal (len x) n)
                  (if (zp n)
                      (and (equal n 0) (not (consp x)))
                    (and (consp x)
                         (equal (len (cdr x)) (1- n)))))))


(fgl::def-fgl-rewrite svex-env-lookup-fgl-when-g-map
  (implies (syntaxp (and (fgl::fgl-object-case x :g-map)
                         (fgl::fgl-object-case k :g-concrete)))
           (equal (svex-env-lookup k x)
                  (4vec-fix (cdr (hons-get (svar-fix k) x)))))
  :hints(("Goal" :in-theory (enable svex-env-lookup))))

(fgl::def-fgl-rewrite svex-env-lookup-fgl-when-g-cons
  (implies (and (syntaxp (and (fgl::fgl-object-case x :g-cons)
                              (fgl::fgl-object-case k :g-concrete)))
                (consp x))
           (equal (svex-env-lookup k x)
                  (if (and (consp (car x))
                           (svar-p (caar x))
                           (equal (caar x) (svar-fix k)))
                      (4vec-fix (cdar x))
                    (svex-env-lookup k (cdr x)))))
  :hints(("Goal" :in-theory (enable svex-env-lookup))))

(fgl::remove-fgl-rewrite sv::svex-env-lookup)


(fgl::add-fgl-rewrites svex-env-boundp-of-svex-env-append
                       svex-env-lookup-of-svex-env-append
                       svex-env-p-of-svex-env-append
                       alist-keys-of-svex-env-append)
(fgl::remove-fgl-rewrite svex-env-append)


(fgl::add-fgl-rewrite sv::svex-env-fix-when-svex-env-p)

(fgl::remove-fgl-rewrite sv::svex-env-p)
(fgl::remove-fgl-rewrite sv::svex-env-fix$inline)

(fgl::def-fgl-rewrite svex-env-fix-fgl
  (implies (syntaxp (fgl::fgl-object-case x
                      :g-map t
                      :g-cons t
                      :otherwise nil))
           (equal (svex-env-fix x)
                  (if (atom x) nil
                    (if (and (consp (car x))
                             (svar-p (caar x)))
                        (cons (cons (caar x) (4vec-fix (cdar x)))
                              (svex-env-fix (cdr X)))
                      (svex-env-fix (cdr X))))))
  :hints(("Goal" :in-theory (enable svex-env-fix))))

(fgl::def-fgl-rewrite alist-keys-fgl
  (implies (and (equal consp (and (consp x) t))
                (syntaxp (fgl::fgl-object-case consp :g-concrete)))
           (equal (alist-keys x)
                  (if consp
                      (if (consp (car x))
                          (cons (caar x)
                                (alist-keys (cdr x)))
                        (alist-keys (cdr x)))
                    nil)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(fgl::remove-fgl-rewrite alist-keys)


;; set symbolic eval params
;; make probealist/namemap-eval use ssvex-eval

(define svex-alistlist->svexes ((x svex-alistlist-p))
  :returns (svexes svexlist-p)
  (if (atom x)
      nil
    (append (svex-alist-vals (car x))
            (svex-alistlist->svexes (cdr x)))))

(define svex-alistlist-4vecs->envlist ((4vecs 4veclist-p)
                                       (x svex-alistlist-p))
  :guard (equal (len 4vecs) (len (svex-alistlist->svexes x)))
  :guard-hints (("goal" :in-theory (enable svex-alistlist->svexes)))
  (if (atom x)
      nil
    (b* ((keys (svex-alist-keys (car x))))
      (cons (pairlis$ (svex-alist-keys (car x)) 4vecs)
            (svex-alistlist-4vecs->envlist (nthcdr (len keys) 4vecs) (cdr x)))))
  ///
  (local (defthm pairlis$-of-append-vals
           (implies (equal (len vals1) (len keys))
                    (equal (pairlis$ keys (append vals1 vals))
                           (pairlis$ keys vals1)))
           :hints(("Goal" :in-theory (enable pairlis$)))))

  (local (defthm nthcdr-of-append
           (implies (equal (nfix n) (len a))
                    (equal (nthcdr n (append a b))
                           b))
           :hints(("Goal" :in-theory (enable nthcdr append)
                   :induct (nthcdr n a)))))

  (local (defthm svex-alist-eval-is-pairlis
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svex-alist-vals
                                             svex-alist-keys
                                             svex-alist-eval)))))
  
  (defthmd svex-alistlist-eval-in-terms-of-svex-alistlist->svexes
    (equal (svex-alistlist-eval x env)
           (b* ((svexes (svex-alistlist->svexes x))
                (4vecs (sv::svexlist-eval-for-symbolic svexes env '((:allvars . t)))))
             (svex-alistlist-4vecs->envlist 4vecs x)))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                      svex-alistlist->svexes
                                      svexlist-eval-for-symbolic)
            :induct (svex-alistlist-eval x env)
            :expand ((:free (4vecs) (svex-alistlist-4vecs->envlist 4vecs x))))))

  (fgl::add-fgl-rewrite svex-alistlist-eval-in-terms-of-svex-alistlist->svexes))

(fgl::def-fgl-rewrite 4vec-bit?!-fgl
  (equal (4vec-bit?! tests thens elses)
         (b* (((4vec tests))
              ((4vec thens))
              ((4vec elses))
              (pick-then (logand tests.upper tests.lower)))
           (b* (((when (eql pick-then -1)) (4vec-fix thens))
                ((when (eql pick-then 0)) (4vec-fix elses))
                (pick-else (lognot pick-then))
                (upper (logior (logand pick-then thens.upper)
                               (logand pick-else elses.upper)))
                (lower (logior (logand pick-then thens.lower)
                               (logand pick-else elses.lower))))
             (4vec upper lower))))
  :hints(("Goal" :in-theory (e/d (4vec-bit?!)
                                 (bitops::associativity-of-logand
                                  bitops::commutativity-2-of-logand)))))

(fgl::def-fgl-rewrite 4vec-bit?!-0-fgl
  (equal (4vec-bit?! tests thens 0)
         (b* (((4vec tests))
              ((4vec thens))
              (pick-then (logand tests.upper tests.lower)))
           (b* (((when (eql pick-then -1)) (4vec-fix thens))
                ((when (eql pick-then 0)) 0)
                (upper (logand pick-then thens.upper))
                (lower (logand pick-then thens.lower)))
             (4vec upper lower))))
  :hints(("Goal" :in-theory (e/d (4vec-bit?!)
                                 (bitops::associativity-of-logand
                                  bitops::commutativity-2-of-logand)))))

(fgl::add-fgl-rewrite sv::4vec-p-of-svex-env-lookup)


(local (defun logand-with-loghead-integer-length-bound-ind (len x y)
         (declare (xargs :measure (integer-length x)
                         :hints(("Goal" :in-theory (enable bitops::integer-length**)))))
         (if (zp (integer-length x))
             (list len y)
           (logand-with-loghead-integer-length-bound-ind (1- len) (logcdr x) (logcdr y)))))

(local (defthm logand-with-loghead-integer-length-bound
         (implies (and (<= 0 x)
                       (integerp len)
                       (<= (integer-length x) len))
                  (equal (logand x (loghead len y))
                         (logand x y)))
         :hints (("goal" :induct (logand-with-loghead-integer-length-bound-ind len x y)
                  :expand ((loghead len y)
                           (:free (y) (logand x y))
                           (integer-length x))))))

(fgl::def-fgl-rewrite logand-mask-out-notnice
  (equal (logand x y)
         (b* ((x-type (fgl::syntax-bind x-type
                                        (fgl::g-concrete
                                         (fgl::fgl-object-case x
                                           :g-concrete :nice
                                           :g-integer :nice
                                           :g-apply :not-nice
                                           :g-var :not-nice
                                           :otherwise nil))))
              (y-type (fgl::syntax-bind y-type
                                        (fgl::g-concrete
                                         (fgl::fgl-object-case y
                                           :g-concrete :nice
                                           :g-integer :nice
                                           :g-apply :not-nice
                                           :g-var :not-nice
                                           :otherwise nil))))
              ((unless (or (and (eq x-type :nice) (eq y-type :not-nice))
                           (and (eq x-type :not-nice) (eq y-type :nice))))
               ; (fgl::fgl-prog2 (fgl::syntax-interp (cw "x: ~x0 y: ~x1~%" x-type y-type))
                               (fgl::abort-rewrite (logand x y)))
              ((mv nice not-nice) (if (eq x-type :nice) (mv x y) (mv y x)))
              ((unless (<= 0 nice))
               ; (fgl::fgl-prog2 (fgl::syntax-interp (cw "maybe negative~%"))
                               (fgl::abort-rewrite (logand x y)))
              (nice-len (fgl::integer-length-bound nice-len nice))
              ((unless nice-len)
               (fgl::abort-rewrite (logand x y))))
           (logand nice (loghead nice-len not-nice))))
  :hints(("Goal" :in-theory (enable fgl::integer-length-bound))))

;; (fgl::def-fgl-rewrite svex-envs-disagree-witness-fgl
;;   (iff (svex-envs-disagree-witness vars x y)
;;        (not (svex-envs-agree vars x y))))

;; (fgl::remove-fgl-rewrite svex-envs-disagree-witness)


;; Use FGL to prove that if pipeline input envs agree except on pipeline
;; override vars, then FSM input envs agree except on FSM override vars.

(fgl::remove-fgl-rewrite svex-envs-agree-except)



;; Non-FTY compliant! Just meant for FGL processing of svex-envs-agree-except.
(define svex-envs-correspond-except ((vars) ;; alist
                                     (env1 svex-env-p)
                                     (env2 svex-env-p))
  :measure (+ (len env1) (len env2))
  :hooks nil ;; 
  :guard-debug t
  (b* (((when (atom env1)) (if (atom env2) t nil))
       ;; (cond ((atom env2) t)
       ;;       ((mbt (and (consp (car env2)) (svar-p (caar env2)))) nil)
       ;;       (t (svex-envs-correspond-except vars env1 (cdr env2))))
       ((when (atom env2)) nil)
       ;; (if (mbt (and (consp (car env1)) (svar-p (caar env1))))
       ;;     nil
       ;;   (svex-envs-correspond-except vars (cdr env1) env2))
       ;; ((unless (mbt (and (consp (car env1)) (svar-p (caar env1)))))
       ;;  (svex-envs-correspond-except vars (cdr env1) env2))
       ;; ((unless (mbt (and (consp (car env2)) (svar-p (caar env2)))))
       ;;  (svex-envs-correspond-except vars env1 (cdr env2)))
       ((cons key1 val1) (car env1))
       ((cons key2 val2) (car env2))
       ((unless (and (equal key1 key2)
                     (or (hons-get key1 vars)
                         (equal val1 val2))))
        nil))
    (svex-envs-correspond-except vars (cdr env1) (cdr env2)))
  ///
  (local (defthm svex-env-lookup-when-consp
           (implies (and (consp env)
                         (svex-env-p env))
                    (equal (svex-env-lookup var env)
                           (if (equal (svar-fix var) (caar env))
                               (cdar env)
                             (svex-env-lookup var (cdr env)))))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (local (defthm no-duplicatesp-equal-of-cons
           (equal (no-duplicatesp-equal (cons a b))
                  (and (not (member-equal a b))
                       (no-duplicatesp-equal b)))))

  (local (defthm hons-assoc-equal-is-member-alist-keys
           (iff (hons-assoc-equal k x)
                (member-equal k (Alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))
  
  (local (in-theory (disable (:d svex-envs-correspond-except)
                             member-equal
                             no-duplicatesp-equal)))
  
  (defthm svex-envs-correspond-except-implies-agree-except
    (implies (and (svex-envs-correspond-except vars env1 env2)
                  (svex-env-p env1)
                  (svex-env-p env2)
                  (svarlist-p (alist-keys vars)))
             (svex-envs-agree-except (alist-keys vars) env1 env2))
    :hints (("goal" :induct (svex-envs-correspond-except vars env1 env2)
             :expand ((svex-envs-correspond-except vars env1 env2)
                      (svex-envs-correspond-except vars env1 nil)
                      (svex-envs-correspond-except vars nil env2)
                      (svex-envs-correspond-except vars nil nil)))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-envs-agree-except-implies)))))

  (local (Defthm svex-env-lookup-when-not-member-keys
           (implies (and (not (member-equal (svar-fix v) (alist-keys env)))
                         (svex-env-p env))
                    (equal (svex-env-lookup v env) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup alist-keys member-equal)))))


  (defthm svex-envs-correspond-except-is-agree-except
    (implies (and (svex-env-p env1)
                  (svex-env-p env2)
                  (svarlist-p (alist-keys vars))
                  (equal (alist-keys env1)
                         (alist-keys env2))
                  (no-duplicatesp-equal (alist-keys env1)))
             (equal (svex-envs-correspond-except vars env1 env2)
                    (svex-envs-agree-except (alist-keys vars) env1 env2)))
    :hints (("goal" :induct (svex-envs-correspond-except vars env1 env2))
            '(:cases ((svex-envs-agree-except (alist-keys vars) env1 env2)))
            (and stable-under-simplificationp
                 '(
             :expand ((svex-envs-correspond-except vars env1 env2)
                      (svex-envs-correspond-except vars nil nil)
                      (alist-keys env1)
                      (alist-keys env2))))
            (and stable-under-simplificationp
                 (let ((lit (assoc-equal 'svex-envs-agree-except clause)))
                   (if lit
                       `(:expand (,lit)
                         :use ((:instance svex-envs-agree-except-implies
                                (x env1) (y env2) (vars (alist-keys vars))
                                (var (svex-envs-agree-except-witness
                                      . ,(cdr lit))))))
                     `(:use ((:instance svex-envs-agree-except-implies
                              (x env1) (y env2) (vars (alist-keys vars))
                              (var (caar env1))))))))
            )))
                 
(local (in-theory (disable acl2::hons-dups-p)))

(local (defthm alist-keys-of-pairlis
         (equal (alist-keys (pairlis$ x y))
                (acl2::true-list-fix x))
         :hints(("Goal" :in-theory (enable alist-keys)))))


(define svex-env-p-fgl-enabled (x)
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (svar-p (caar x))
         (4vec-p (cdar x))
         (svex-env-p-fgl-enabled (cdr x))))
  ///
  (defthm svex-env-p-fgl-enabled-elim
    (Equal (svex-env-p-fgl-enabled x)
           (svex-env-p x))))

(fgl::def-fgl-rewrite svex-envs-agree-except-when-same-shape
  (implies (and (syntaxp (fgl::fgl-object-case vars :g-concrete))
                (equal env1-keys (alist-keys env1))
                (syntaxp (fgl::fgl-object-case env1-keys :g-concrete))
                (equal env1-keys (alist-keys env2))
                (svex-env-p-fgl-enabled env1)
                (svex-env-p-fgl-enabled env2)
                (not (acl2::hons-dups-p env1-keys))
                (svarlist-p vars))
           (equal (svex-envs-agree-except vars env1 env2)
                  (svex-envs-correspond-except
                   (make-fast-alist (pairlis$ vars nil))
                   env1 env2))))


(fgl::remove-fgl-rewrite svex-envs-correspond-except)

(fgl::def-fgl-rewrite svex-envs-correspond-except-fgl
  (equal (svex-envs-correspond-except vars env1 env2)
         (b* ((env1-atom (fgl::check-non-consp env1-atom env1))
              (env2-atom (fgl::check-non-consp env2-atom env2))
              ((when (and env1-atom env2-atom))
               ;; we know they're both atoms.
               t)
              (env1-consp (fgl::check-consp env1-consp env1))
              (env2-consp (fgl::check-consp env2-consp env2))
              ((unless (and (or env1-atom env1-consp)
                            (or env2-atom env2-consp)))
               ;; for one of them, we don't know if it's atom or cons, so give up
               (fgl::abort-rewrite (svex-envs-correspond-except vars env1 env2)))
              ;; we know whether each of them are atom/cons and at least one is consp
              (env1-pair (car env1))
              (env1-pair-consp (fgl::check-consp env1-pair-consp env1-pair))
              ((unless env1-pair-consp)
               ;; (cheap) give up if we don't know whether the first element of env1 is consp
               ;; -- could skip past it if we know it's not
               (fgl::abort-rewrite (svex-envs-correspond-except vars env1 env2)))
              (env2-pair (car env2))
              (env2-pair-consp (fgl::check-consp env2-pair-consp env2-pair))
              ((unless env2-pair-consp)
               ;; (cheap) give up if we don't know whether the first element of env2 is consp
               ;; -- could skip past it if we know it's not
               (fgl::abort-rewrite (svex-envs-correspond-except vars env1 env2)))

              (env1-key (car env1-pair))
              (env2-key (car env2-pair))
              ((unless (fgl::syntax-bind keys-known (fgl::g-concrete
                                                     (and (fgl::fgl-object-case env1-key :g-concrete)
                                                          (fgl::fgl-object-case env2-key :g-concrete)))))
               ;; give up if the first key of env1 isn't concrete
               (fgl::abort-rewrite (svex-envs-correspond-except vars env1 env2)))
              ((unless (equal env1-key env2-key))
               ;; nil if they aren't equal
               nil)
              ((when (hons-get env1-key vars))
               ;; skip past this one
               (svex-envs-correspond-except vars (cdr env1) (cdr env2)))
              (first (equal (cdr env1-pair) (cdr env2-pair)))
              (rest (svex-envs-correspond-except vars (cdr env1) (cdr env2))))
           (and first rest)))
  :hints(("Goal" :in-theory (enable svex-envs-correspond-except
                                    fgl::check-consp
                                    fgl::check-non-consp))))



(table fgl::magitastic-ev-definitions 'svex-envs-agree-except
       '((vars env1 env2)
         (SVEX-ENVS-AGREE
          (HONS-SET-DIFF (BINARY-APPEND (ALIST-KEYS (SVEX-ENV-FIX$INLINE ENV1))
                                        (ALIST-KEYS (SVEX-ENV-FIX$INLINE ENV2)))
                         (SVARLIST-FIX$INLINE VARS))
          ENV1 ENV2)))


(defsection no-1s-lookup
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

  (define no-1s-fix-lower ((upper integerp)
                           (lower integerp))
    (logandc1 upper lower)
    ///
    (fgl::remove-fgl-rewrite no-1s-fix-lower)
    (fgl::def-fgl-rewrite intcar-of-no-1s-fix-lower
      (equal (fgl::intcar (no-1s-fix-lower upper lower))
             (and (not (fgl::intcar upper)) (fgl::intcar lower) t)))

    (fgl::def-fgl-rewrite intcdr-of-no-1s-fix-lower
      (equal (fgl::intcdr (no-1s-fix-lower upper lower))
             (no-1s-fix-lower (fgl::intcdr upper) (fgl::intcdr lower)))))

  ;; (define 4vec-no-1s->lower ((x 4vec-p))
  ;;   :enabled t
  ;;   (4vec->lower x)
  ;;   ///
  ;;   (fgl::remove-fgl-rewrite 4vec-no-1s->lower)

  ;;   (fgl::def-fgl-rewrite 4vec-no-1s->lower-of-4vec
  ;;     (equal (4vec-no-1s->lower (4vec upper lower))
  ;;            (ifix lower))))

  (define 4vec-no-1s-fix ((x 4vec-p))
    :returns (new-x 4vec-p)
    :prepwork ((local (in-theory (enable no-1s-fix-lower))))
    (b* (((4vec x)))
      (4vec x.upper (no-1s-fix-lower x.upper x.lower)))
    ///
    (local (in-theory (enable 4vec-no-1s-p)))
    (defret 4vec-no-1s-p-of-<fn>
      (4vec-no-1s-p new-x))

    (defret <fn>-when-4vec-no-1s-p
      (implies (4vec-no-1s-p x)
               (equal new-x (4vec-fix x)))
      :hints ((acl2::logbitp-reasoning))))

  (define svex-env-no-1s-lookup ((v svar-p) (x svex-env-p))
    :enabled t
    (svex-env-lookup v x)
    ///
    (fgl::remove-fgl-rewrite svex-env-no-1s-lookup))
  
  (defthmd svex-env-lookup-when-svex-env-no-1s-p
    (implies (and (svex-env-keys-no-1s-p vars x)
                  (member-equal (svar-fix v) (svarlist-fix vars)))
             (equal (svex-env-lookup v x)
                    (4vec-no-1s-fix (svex-env-no-1s-lookup v x)))))


  (fgl::def-fgl-rewrite svex-env-keys-no-1s-p-expand
    (implies (syntaxp (and (fgl::fgl-object-case vars :g-concrete)
                           (fgl::fgl-object-case x
                             :g-concrete t
                             :g-cons t
                             :g-map t
                             :otherwise nil)))
             (equal (svex-env-keys-no-1s-p vars x)
                    (if (atom vars)
                        t
                      (and (4vec-no-1s-p (svex-env-lookup (car vars) x))
                           (svex-env-keys-no-1s-p (cdr vars) x)))))
    :hints(("Goal" :in-theory (enable svex-env-keys-no-1s-p))))

  (fgl::def-fgl-rewrite svex-envlist-keys-no-1s*-p-expand
    (implies (syntaxp (fgl::fgl-object-case vars :g-concrete))
             (equal (svex-envlist-keys-no-1s*-p vars x)
                    (if (atom vars)
                        t
                      (and (svex-env-keys-no-1s-p (car vars) (car x))
                           (svex-envlist-keys-no-1s*-p (cdr vars) (cdr x))))))
    :hints(("Goal" :in-theory (enable svex-envlist-keys-no-1s*-p))))

  (fgl::remove-fgl-rewrite svex-env-keys-no-1s-p)

  (fgl::add-fgl-rewrite svex-env-lookup-of-svex-env-fix-env))
