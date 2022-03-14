;; SV - Symbolic Vector Hardware Analysis Framework

;; INTEL TEMPORARY COPYRIGHT HEADER --
;; Not for public distribution until this is replaced with a proper license!

;; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)
(include-book "centaur/fgl/checks" :dir :system) ;; integer-length-bound
(include-book "centaur/fgl/fgl-object" :dir :system) ;; for syntaxp checks
(include-book "../svex/lists")
(include-book "../svex/env-ops")
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

(fgl::def-fgl-rewrite svex-envs-disagree-witness-fgl
  (iff (svex-envs-disagree-witness vars x y)
       (not (svex-envs-agree vars x y))))

(fgl::remove-fgl-rewrite svex-envs-disagree-witness)
