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


(include-book "override-transparency")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

(local (std::add-default-post-define-hook :fix))


(defprod overridekey-syntaxcheck-data
  ((keys svarlist-p)
   (values svex-alist-p)))

(define bit?!-overridekey-syntax-check ((test svex-p)
                                        (then svex-p)
                                        (else svex-p)
                                        (key svar-p)
                                        (value maybe-svex-p))
  ;; Variant of bit?!-overridekeys-syntax-check which only checks one override key.
  ;; Value is the reference value of key.
  :returns (result (implies (and result (not (equal result t)))
                            (equal result (svar-change-override key nil))))
  (b* (((unless (svex-case test :var))
        nil)
       ((svex-var test))
       (key (svar-change-override key nil))
       ((unless (and (svar-equiv-nonoverride test.name key)
                     (svar-override-p test.name :test)))
        nil) 
       ((unless (svex-case then :var))
        ;; bad
        key)
       ((svex-var then))
       ((unless (and (svar-equiv-nonoverride then.name key)
                     (svar-override-p then.name :val)))
        ;; bad
        key)
       ((unless (and value (equal (svex-fix else) (svex-fix value))))
        key))
    t)
  ///
  (local (in-theory (enable maybe-svex-fix)))

  (defret <fn>-of-svar-change-override
    (equal (let ((key (svar-change-override key type))) <call>)
           result)))


(define bit?!-overridekeys-syntax-check ((test svex-p)
                                         (then svex-p)
                                         (else svex-p)
                                         (keys svarlist-p)
                                         (values svex-alist-p))
  ;; returns NIL if it doesn't look like an override triple,
  ;; T if it looks like a correct override triple,
  ;; the violating overridekey if it is malformed.
  :returns (result (iff (svar-p result) (and result (not (equal result t)))))
  (b* (((unless (svex-case test :var))
        nil)
       ((svex-var test))
       ((unless (and (svarlist-member-nonoverride test.name keys)
                     (svar-override-p test.name :test)))
        nil)
       (key (svar-change-override test.name nil)) 
       ((unless (svex-case then :var))
        ;; bad
        key)
       ((svex-var then))
       ((unless (and (svar-equiv-nonoverride then.name test.name)
                     (svar-override-p then.name :val)))
        ;; bad
        key)
       (val (svex-fastlookup key values))
       ((unless (equal (svex-fix else) val))
        key))
    t)
  ///
  (defthmd bit?!-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
    (equal (bit?!-overridekeys-syntax-check test then else keys values)
           (b* (((when (atom keys)) nil)
                (key1 (car keys))
                (val1 (svex-fastlookup (svar-change-override key1 nil) values))
                (result1 (bit?!-overridekey-syntax-check test then else key1 val1)))
             (or result1
                 (bit?!-overridekeys-syntax-check test then else (cdr keys) values))))
    :hints(("Goal" :in-theory (enable bit?!-overridekey-syntax-check
                                      equal-of-svar-change-override
                                      svar-equiv-nonoverride)
            :expand ((svarlist-change-override keys nil))
            :do-not-induct t))
    :otf-flg t
    :rule-classes ((:definition :install-body nil)))

  (defretd <fn>-when-bit?!-overridekey-syntax-check-bad
    (b* ((key-check (bit?!-overridekey-syntax-check test then else key value)))
      (implies (and key-check
                    (not (equal key-check t))
                    (equal value (svex-lookup (svar-change-override key nil) values)))
               (equal result
                      (and (svarlist-member-nonoverride key keys)
                           (svar-change-override key nil)))))
    :hints (("goal" :induct (len keys)
             :expand ((:with bit?!-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                       (bit?!-overridekeys-syntax-check test then else keys values)))
             :in-theory (e/d (svarlist-member-nonoverride
                              svarlist-change-override
                              bit?!-overridekey-syntax-check
                              equal-of-svar-change-override
                              svar-equiv-nonoverride)
                             (<fn>)))))

  (defretd <fn>-when-bit?!-overridekey-syntax-check-good
    (b* ((key-check (bit?!-overridekey-syntax-check test then else key value)))
      (implies (and (equal key-check t)
                    (equal value (svex-lookup (svar-change-override key nil) values)))
               (equal result
                      (and (svarlist-member-nonoverride key keys) t))))
    :hints (("goal" :induct (len keys)
             :expand ((:with bit?!-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                       (bit?!-overridekeys-syntax-check test then else keys values)))
             :in-theory (e/d (svarlist-member-nonoverride
                              svarlist-change-override
                              bit?!-overridekey-syntax-check
                              equal-of-svar-change-override
                              svar-equiv-nonoverride)
                             (<fn>))))))
 


(defines svex-overridekey-syntax-check
  :flag-local nil
  (define svex-overridekey-syntax-check ((x svex-p)
                                         (key svar-p)
                                         (value maybe-svex-p)) ;; lookup of key
    :returns (bad-key-p)
    :measure (two-nats-measure (svex-count x) 1)
    (svex-case x
      :quote nil
      :var (and (svar-equiv-nonoverride x.name key)
                (or (svar-override-p x.name :test)
                    (svar-override-p x.name :val)))
      :call (svex-call-overridekey-syntax-check x key value)))

  (define svex-call-overridekey-syntax-check ((x svex-p)
                                              (key svar-p)
                                              (value maybe-svex-p))
    :returns (bad-key-p)
    :measure (two-nats-measure (svex-count x) 0)
    :guard (svex-case x :call)
    (b* (((unless (mbt (svex-case x :call))) nil)
         ((svex-call x)))
      (case x.fn
        (bit?! (b* (((unless (Eql (len x.args) 3))
                     (svexlist-overridekey-syntax-check x.args key value))

                    ((list test then else) x.args)

                    (check (bit?!-overridekey-syntax-check test then else key value))

                    ((when (eq check nil))
                     ;; not an override triple -- recur on args
                     (svexlist-overridekey-syntax-check x.args key value))

                    ((when (eq check t))
                     ;; good override triple -- recur on else
                     (svex-overridekey-syntax-check else key value)))

                 ;; else bad!
                 t))
        (otherwise
         (svexlist-overridekey-syntax-check x.args key value)))))

  (define svexlist-overridekey-syntax-check ((x svexlist-p)
                                              (key svar-p)
                                              (value maybe-svex-p))
    :measure (two-nats-measure (svexlist-count x) 0)
    :returns (bad-key-p)
    (if (atom x)
        nil
      (or (svex-overridekey-syntax-check (car x) key value)
          (svexlist-overridekey-syntax-check (cdr x) key value))))
  ///
  

  (fty::deffixequiv-mutual svex-overridekey-syntax-check)

  (std::defret-mutual <fn>-of-change-override
    (defret <fn>-of-change-override
      (equal (let ((key (svar-change-override key type))) <call>)
             bad-key-p)
      :hints ('(:expand ((:free (key) <call>))
                :in-theory (enable svar-equiv-nonoverride)))
      :fn svex-overridekey-syntax-check)
    (defret <fn>-of-change-override
      (equal (let ((key (svar-change-override key type))) <call>)
             bad-key-p)
      :hints ('(:expand ((:free (key) <call>))))
      :fn svex-call-overridekey-syntax-check)
    (defret <fn>-of-change-override
      (equal (let ((key (svar-change-override key type))) <call>)
             bad-key-p)
      :hints ('(:expand ((:free (key) <call>))))
      :fn svexlist-overridekey-syntax-check)))


(local (include-book "std/osets/element-list" :dir :system))

(local (deflist svarlist
         :elt-type svar
         :true-listp t
         :elementp-of-nil nil))






(defines svex-overridekeys-syntax-check
  :flag-local nil
  (define svex-overridekeys-syntax-check ((x svex-p)
                                          (data overridekey-syntaxcheck-data-p))
    :returns (bad-keys svarlist-p)
    :measure (two-nats-measure (svex-count x) 1)
    :verify-guards nil
    (svex-case x
      :quote nil
      :var (and (svarlist-member-nonoverride x.name (overridekey-syntaxcheck-data->keys data))
                (or (svar-override-p x.name :test)
                    (svar-override-p x.name :val))
                (list (svar-change-override x.name nil)))
      :call (svex-call-overridekeys-syntax-check x data)))

  (define svex-call-overridekeys-syntax-check ((x svex-p)
                                               (data overridekey-syntaxcheck-data-p))
    :returns (bad-keys svarlist-p)
    :measure (two-nats-measure (svex-count x) 0)
    :guard (svex-case x :call)
    (b* (((unless (mbt (svex-case x :call))) nil)
         ((svex-call x)))
      (case x.fn
        (bit?! (b* (((unless (Eql (len x.args) 3))
                     (svexlist-overridekeys-syntax-check x.args data))

                    ((list test then else) x.args)

                    ((overridekey-syntaxcheck-data data))
                    (check (bit?!-overridekeys-syntax-check test then else data.keys data.values))

                    ((when (eq check nil))
                     ;; not an override triple -- recur on args
                     (svexlist-overridekeys-syntax-check x.args data))

                    ((when (eq check t))
                     ;; good override triple -- recur on else
                     (svex-overridekeys-syntax-check else data)))

                 ;; else bad -- insert bad key into result from args
                 (set::insert check (svexlist-overridekeys-syntax-check x.args data))))
        (otherwise
         (svexlist-overridekeys-syntax-check x.args data)))))

  (define svexlist-overridekeys-syntax-check ((x svexlist-p)
                                              (data overridekey-syntaxcheck-data-p))
    :measure (two-nats-measure (svexlist-count x) 0)
    :returns (bad-keys svarlist-p)
    (if (atom x)
        nil
      (union (svex-overridekeys-syntax-check (car x) data)
             (svexlist-overridekeys-syntax-check (cdr x) data))))

  ///

  (local (in-theory (disable svex-overridekeys-syntax-check
                             svex-call-overridekeys-syntax-check
                             svexlist-overridekeys-syntax-check)))
  
  (local (defthm setp-of-singleton
           (setp (list x))
           :hints(("Goal" :in-theory (enable setp)))))
  
  (std::defret-mutual setp-of-<fn>
    :mutual-recursion svex-overridekeys-syntax-check
    (defret setp-of-<fn>
      (setp bad-keys)
      :hints ('(:expand (<call>)))
      :fn svex-overridekeys-syntax-check)

    (defret setp-of-<fn>
      (setp bad-keys)
      :hints ('(:expand (<call>)))
      :fn svex-call-overridekeys-syntax-check)

    (defret setp-of-<fn>
      (setp bad-keys)
      :hints ('(:expand (<call>)))
      :fn svexlist-overridekeys-syntax-check))

  (verify-guards svex-overridekeys-syntax-check)

  

  (local (defthm svex-eval-when-var
           (implies (svex-case x :var)
                    (equal (svex-eval x env)
                           (svex-env-lookup (svex-var->name x) env)))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (defthm caddr-args-when-len
           (implies (and (svexlist-p args)
                         (equal (len args) 3))
                    (caddr args))))

  (local (defthm svex-env-lookup-of-svex-alist-eval-when-lookup
           (implies (double-rewrite (svex-lookup v x))
                    (equal (svex-env-lookup v (svex-alist-eval x env))
                           (svex-eval (svex-lookup v x) env)))))

  (local (in-theory (disable svex-env-lookup-of-svex-alist-eval)))
  
  (local (defthm overridekeys-transparent-p-when-bit?!-overridekeys-syntax-check
           (implies (and (svex-case x :call)
                         (equal (svex-call->fn x) 'bit?!)
                         (equal (len (svex-call->args x)) 3)
                         (svex-overridekey-transparent-p (caddr (svex-call->args x)) keys values)
                         (equal (bit?!-overridekeys-syntax-check
                                 (car (svex-call->args x))
                                 (cadr (svex-call->args x))
                                 (caddr (svex-call->args x))
                                 keys values)
                                t))
                    (svex-overridekey-transparent-p x keys values))
           :hints (("goal" :expand ((:free (keys values) (svex-overridekey-transparent-p x keys values))
                                    (svexlist-vars (svex-call->args x))
                                    (svexlist-vars (cdr (svex-call->args x)))
                                    (svexlist-vars (cddr (svex-call->args x))))
                    :in-theory (enable svex-apply 4veclist-nth-safe
                                       bit?!-overridekeys-syntax-check
                                       svex-vars
                                       svar-equiv-nonoverride
                                       equal-of-svar-change-override
                                       4vec-bit?!-agree-when-overridekeys-envs-agree)
                    :use ((:instance svex-overridekey-transparent-p-necc
                           (x (caddr (svex-call->args x)))
                           (overridekeys keys)
                           (subst values)
                           (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness x keys values)))
                           (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness x keys values)))))
                    ))
           :otf-flg t))

  ;; (local (defthm insert-under-iff
  ;;          (iff (insert k x) t)))

  (local (defthm union-under-iff
           (iff (union a b)
                (or (sfix a) (sfix b)))
           :hints(("Goal" :in-theory (enable union)))))

    
  (std::defret-mutual overridekeys-transparent-p-when-<fn>
    (defret overridekeys-transparent-p-when-<fn>
      (b* (((overridekey-syntaxcheck-data data)))
        (implies (not bad-keys)
                 (svex-overridekey-transparent-p x data.keys data.values)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env)))
                     :in-theory (enable svex-overridekey-transparent-p-when-non-override-var
                                        svex-overridekey-transparent-p-when-const))))
      :fn svex-overridekeys-syntax-check)
    (defret overridekeys-transparent-p-when-<fn>
      (b* (((overridekey-syntaxcheck-data data)))
        (implies (and (not bad-keys)
                      (svex-case x :call))
                 (svex-overridekey-transparent-p x data.keys data.values)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env)))
                     :in-theory (enable svexlist-vars 
                                        svex-overridekey-transparent-p-when-args-transparent
                                        ;; svex-override-triple-check
                                        ))))
      :fn svex-call-overridekeys-syntax-check)
    (defret overridekeys-transparent-p-when-<fn>
      (b* (((overridekey-syntaxcheck-data data)))
        (implies (not bad-keys)
                 (svexlist-overridekey-transparent-p x data.keys data.values)))
      :hints ('(:expand (<call>
                         (:free (overridekeys values)
                          (svexlist-overridekey-transparent-p x overridekeys values)))
                :do-not-induct t))
      :fn svexlist-overridekeys-syntax-check))




  (local (defthm set-lemma2
           (implies (equal b (insert c d))
                    (equal (equal (union a b) (insert c (union a d)))
                           t))
           :hints(("Goal" :in-theory (enable set::pick-a-point-subset-strategy
                                             double-containment)))))

  (local (defthm set-lemma3
           (implies (equal b (insert a c))
                    (equal (equal (insert a b) b) t))
           :hints(("Goal" :in-theory (enable set::pick-a-point-subset-strategy
                                             double-containment)))))

  (local (defthm in-of-singleton
           (iff (in b (list a))
                (equal a b))
           :hints(("Goal" :in-theory (enable in empty head tail)))))

  (local (defthm insert-nil
           (equal (insert a nil) (list a))
           :hints(("Goal" :in-theory (enable set::pick-a-point-subset-strategy
                                             double-containment)))))
           
  
  (local (defthm set-lemma4
           (equal (insert a (list a)) (list a))
           :hints(("Goal" :in-theory (enable set::pick-a-point-subset-strategy
                                             double-containment)))))

  (local (defthm bit?!-overridekey-syntax-check-t-implies-args-syntax-check
           (implies (and (equal (bit?!-overridekey-syntax-check
                                 (car args) (cadr args) (caddr args) key value)
                                t)
                         (equal value (svex-lookup (svar-change-override key nil) values))
                         (equal (len args) 3)
                         (not (member-equal (svar-change-override key nil)
                                            (svarlist-change-override keys nil))))
                    (equal (svexlist-overridekeys-syntax-check args (overridekey-syntaxcheck-data keys values))
                           (svex-overridekeys-syntax-check (caddr args) (overridekey-syntaxcheck-data keys values))))
           :hints (("goal"
                    :do-not-induct t
                    :in-theory (enable bit?!-overridekey-syntax-check
                                       svar-equiv-nonoverride)
                    :expand ((svexlist-overridekeys-syntax-check args (overridekey-syntaxcheck-data keys values))
                             (svexlist-overridekeys-syntax-check (cdr args) (overridekey-syntaxcheck-data keys values))
                             (svexlist-overridekeys-syntax-check (cddr args) (overridekey-syntaxcheck-data keys values))
                             (svexlist-overridekeys-syntax-check (cdddr args) (overridekey-syntaxcheck-data keys values))
                             (svex-overridekeys-syntax-check (car args) (overridekey-syntaxcheck-data keys values))
                             (svex-overridekeys-syntax-check (cadr args) (overridekey-syntaxcheck-data keys values)))))))

  (local (defthm bit?!-overridekey-syntax-check-t-implies-overridekey-args-syntax-check
           (implies (and (equal (bit?!-overridekey-syntax-check
                                 (car args) (cadr args) (caddr args) key1 value1)
                                t)
                         (not (equal (svar-change-override key1 nil)
                                     (svar-change-override key nil)))
                         (equal value (svex-lookup (svar-change-override key nil) values))
                         (equal value1 (svex-lookup (svar-change-override key1 nil) values))
                         (equal (len args) 3))
                    (equal (svexlist-overridekey-syntax-check args key value)
                           (svex-overridekey-syntax-check (caddr args) key value)))
           :hints (("goal"
                    :do-not-induct t
                    :in-theory (enable bit?!-overridekey-syntax-check
                                       svar-equiv-nonoverride)
                    :expand ((:free (value) (svexlist-overridekey-syntax-check args key value))
                             (:free (value) (svexlist-overridekey-syntax-check (cdr args) key value))
                             (:free (value) (svexlist-overridekey-syntax-check (cddr args) key value))
                             (:free (value) (svexlist-overridekey-syntax-check (cdddr args) key value))
                             (:free (value) (svex-overridekey-syntax-check (car args) key value))
                             (:free (value) (svex-overridekey-syntax-check (cadr args) key value)))))))

  (local (defthm bit?!-overridekeys-syntax-check-t-implies-overridekey-args-syntax-check
           (implies (and (equal (bit?!-overridekeys-syntax-check
                                 (car args) (cadr args) (caddr args) keys values)
                                t)
                         (not (bit?!-overridekey-syntax-check
                                 (car args) (cadr args) (caddr args) key value))
                         (equal value (svex-lookup (svar-change-override key nil) values))
                         (equal (len args) 3))
                    (equal (svexlist-overridekey-syntax-check args key value)
                           (svex-overridekey-syntax-check (caddr args) key value)))
           :hints (("goal"
                    :induct (len keys)
                    :expand ((:with bit?!-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                              (bit?!-overridekeys-syntax-check
                               (car args) (cadr args) (caddr args) keys values))))
                   (and stable-under-simplificationp
                        '(:cases ((equal (svar-change-override (car keys) nil)
                                         (svar-change-override key nil)))
                          :restrict ((bit?!-overridekey-syntax-check-t-implies-overridekey-args-syntax-check
                                      ((values values))))))
                   (and stable-under-simplificationp
                        '(:in-theory (enable bit?!-overridekey-syntax-check))))))

  (local (defthm svexlist-overridekey-syntax-check-when-svex-overridekey-syntax-check
           (implies (and (svex-overridekey-syntax-check (caddr args) key value)
                         (equal (len args) 3))
                    (svexlist-overridekey-syntax-check args key value))
           :hints(("goal"
                   :do-not-induct t
                   :expand ((svexlist-overridekey-syntax-check args         key value)
                            (svexlist-overridekey-syntax-check (cdr args)   key value)
                            (svexlist-overridekey-syntax-check (cddr args)  key value)
                            (svexlist-overridekey-syntax-check (cdddr args) key value))))))

  
  (std::defret-mutual <fn>-in-terms-of-overridekey-syntax-check
    (defretd <fn>-in-terms-of-overridekey-syntax-check
      (equal <call>
             (b* (((overridekey-syntaxcheck-data data))
                  ((when (atom data.keys)) nil)
                  (key1 (car data.keys))
                  (val1 (svex-lookup (svar-change-override key1 nil) data.values))
                  (bad (svex-overridekey-syntax-check x key1 val1))
                  (rest (svex-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                           (cdr data.keys) data.values))))
               (if bad
                   (insert (svar-change-override key1 nil) rest)
                 rest)))
      :hints ('(:expand ((:free (data) <call>)
                         (:free (key1 val1) (svex-overridekey-syntax-check x key1 val1))
                         (svarlist-change-override (overridekey-syntaxcheck-data->keys data) nil))
                :in-theory (enable svar-equiv-nonoverride)))
      :rule-classes ((:definition :install-body nil))
      :fn svex-overridekeys-syntax-check)
    (defretd <fn>-in-terms-of-overridekey-syntax-check
      (equal <call>
             (b* (((overridekey-syntaxcheck-data data))
                  ((when (atom data.keys)) nil)
                  (key1 (car data.keys))
                  (val1 (svex-lookup (svar-change-override key1 nil) data.values))
                  (bad (svex-call-overridekey-syntax-check x key1 val1))
                  (rest (svex-call-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                           (cdr data.keys) data.values))))
               (if bad
                   (insert (svar-change-override key1 nil) rest)
                 rest)))
      :hints ('(:expand ((:free (data) <call>)))
              (and stable-under-simplificationp
                   '(:expand ((:with bit?!-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                               (:free (values)
                                (bit?!-overridekeys-syntax-check (car (svex-call->args x))
                                                                 (cadr (svex-call->args x))
                                                                 (caddr (svex-call->args x))
                                                                 (overridekey-syntaxcheck-data->keys data)
                                                                 values)))
                              (:with bit?!-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                               (:free (values)
                                (bit?!-overridekeys-syntax-check (car (svex-call->args x))
                                                                 (cadr (svex-call->args x))
                                                                 (caddr (svex-call->args x))
                                                                 nil
                                                                 values))))))
              (and stable-under-simplificationp
                   '(:expand ((:free (key1 val1) (svex-call-overridekey-syntax-check x key1 val1)))
                     :in-theory (enable bit?!-overridekeys-syntax-check-when-bit?!-overridekey-syntax-check-bad
                                        bit?!-overridekeys-syntax-check-when-bit?!-overridekey-syntax-check-good)
                     :do-not-induct t)))
      :rule-classes ((:definition :install-body nil))
      :fn svex-call-overridekeys-syntax-check)
    (defretd <fn>-in-terms-of-overridekey-syntax-check
      (equal <call>
             (b* (((overridekey-syntaxcheck-data data))
                  ((when (atom data.keys)) nil)
                  (key1 (car data.keys))
                  (val1 (svex-lookup (svar-change-override key1 nil) data.values))
                  (bad (svexlist-overridekey-syntax-check x key1 val1))
                  (rest (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                           (cdr data.keys) data.values))))
               (if bad
                   (insert (svar-change-override key1 nil) rest)
                 rest)))
      :hints ('(:expand ((:free (data) <call>)
                         (:free (key1 val1) (svexlist-overridekey-syntax-check x key1 val1)))))
      :rule-classes ((:definition :install-body nil))
      :fn svexlist-overridekeys-syntax-check))



    (defthm svexlist-override-syntax-check-of-append
      (equal (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                    (append keys1 keys2) values))
             (union (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                           keys1 values))
                    (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                           keys2 values))))
      :hints (("goal" :induct (len keys1)
               :expand ((:with
                         svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                         (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                                keys1 values)))
                        (:with
                         svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                         (:free (a b)
                          (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                                 (cons a b) values))))))))

    (local
     (defthmd svexlist-override-syntax-check-subsetp-of-keys-lemma
       (subsetp-equal
        (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data keys values))
        (svarlist-change-override keys nil))
       :hints (("goal" :induct (len keys)
                :in-theory (enable svarlist-change-override)
                :expand ((:with
                          svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                          (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                                 keys values))))))))

    (fty::deffixequiv-mutual svex-overridekeys-syntax-check)
    
    (defthm svexlist-override-syntax-check-subsetp-of-keys
      (subsetp-equal
       (svexlist-overridekeys-syntax-check x data)
       (svarlist-change-override (overridekey-syntaxcheck-data->keys data) nil))
      :hints (("goal" :use ((:instance svexlist-override-syntax-check-subsetp-of-keys-lemma
                             (keys (overridekey-syntaxcheck-data->keys data))
                             (values (overridekey-syntaxcheck-data->values data)))))))

    (memoize 'svex-call-overridekeys-syntax-check))




