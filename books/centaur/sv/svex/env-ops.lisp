; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "eval")
(include-book "vars")
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (std::add-default-post-define-hook :fix))

(define svex-env-extract-aux ((keys svarlist-p) (env svex-env-p))
  :parents (svex-env-extract)
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (env1 svex-env-p)
  (if (atom keys)
      nil
    (cons (cons (svar-fix (car keys))
                (svex-env-fastlookup (car keys) env))
          (svex-env-extract-aux (cdr keys) env))))

(define svex-env-extract
  :parents (svex-env)
  :short "Restrict an @(see svex-env) to only particular variables.  Variables that are present in keys but not env will be bound to X."
  ((keys svarlist-p "Variables to keep.")
   (env  svex-env-p "Original environment to filter.  Need not be fast."))
  :returns
  (sub-env svex-env-p "Restriction of @('env') to @('keys').  Slow alist.")
  :prepwork ((local (in-theory (enable svex-env-extract-aux svarlist-fix))))
  :verify-guards nil
  (mbe :logic (if (atom keys)
                  nil
                (cons (cons (svar-fix (car keys))
                            (svex-env-fastlookup (car keys) env))
                      (svex-env-extract (cdr keys) env)))
       :exec (with-fast-alist env (svex-env-extract-aux keys env)))
  ///
  (local (defthm svex-env-extract-aux-elim
           (equal (svex-env-extract-aux keys env)
                  (svex-env-extract keys env))))

  (verify-guards svex-env-extract)

  (defthm svex-env-lookup-of-svex-env-extract
    (equal (svex-env-lookup v (svex-env-extract vars env))
           (if (member (svar-fix v) (svarlist-fix vars))
               (svex-env-lookup v env)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svarlist-fix svex-env-lookup))))

  (local (in-theory (disable svex-env-extract)))

  (defthm-svex-eval-flag
    (defthm svex-eval-extract-var-superset
      (implies (subsetp (svex-vars x) (svarlist-fix vars))
               (equal (svex-eval x (svex-env-extract vars env))
                      (svex-eval x env)))
      :hints ('(:expand ((svex-vars x)
                         (:free (env) (svex-eval x env)))))
      :flag expr)
    (defthm svexlist-eval-extract-var-superset
      (implies (subsetp (svexlist-vars x) (svarlist-fix vars))
               (equal (svexlist-eval x (svex-env-extract vars env))
                      (svexlist-eval x env)))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (env) (svexlist-eval x env)))))
      :flag list))

  (defthm svex-alist-eval-of-extract-var-supserset
    (implies (subsetp (svexlist-vars (svex-alist-vals x)) (svarlist-fix vars))
             (equal (svex-alist-eval x (svex-env-extract vars env))
                    (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vals svexlist-vars))))

  (defthm alist-keys-of-svex-env-extract
    (equal (alist-keys (svex-env-extract vars env))
           (svarlist-fix vars))
    :hints(("Goal" :in-theory (enable svarlist-fix alist-keys
                                      svex-env-extract))))


  (local (defthm svex-env-extract-when-car-not-member
           (implies (not (member (caar x) (svarlist-fix keys)))
                    (equal (svex-env-extract keys (cdr x))
                           (svex-env-extract keys x)))
           :hints(("Goal" :in-theory (enable svex-env-extract svex-env-lookup)))))

  (local (defthm svex-env-extract-when-car-not-consp
           (implies (not (and (consp (car x)) (svar-p (caar x))))
                    (equal (svex-env-extract keys (cdr x))
                           (svex-env-extract keys x)))
           :hints(("Goal" :in-theory (enable svex-env-extract svex-env-lookup)))))

  (local (defthm svarlist-p-of-alist-keys-of-env
           (implies (svex-env-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-env-p alist-keys)))))

  (defthm svex-env-extract-when-alist-keys-equal
    (implies (and (equal (alist-keys (svex-env-fix x)) keys)
                  (no-duplicatesp keys))
             (equal (svex-env-extract keys x)
                    (svex-env-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-extract svex-env-fix alist-keys no-duplicatesp))
           (and stable-under-simplificationp
                (not (access acl2::clause-id id :pool-lst))
                '(:induct t))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-lookup)))))

  (defthm svex-env-extract-of-superset
    (implies (subsetp (svarlist-fix keys) (svarlist-fix keys2))
             (Equal (svex-env-extract keys (svex-env-extract keys2 x))
                    (svex-env-extract keys x)))
    :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix))))

  (defret svex-env-boundp-of-<fn>
    (iff (svex-env-boundp k sub-env)
         (member-equal (svar-fix k) (svarlist-fix keys)))
    :hints(("Goal" :in-theory (enable svex-env-boundp (:i <fn>))
            :induct <call>
            :expand (<call>))))

  ;; for :fix hook
  (local (in-theory (enable svex-env-extract))))


(define svex-env-reduce-aux ((keys svarlist-p) (env svex-env-p))
  :parents (svex-env-reduce)
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (env1 svex-env-p)
  (if (atom keys)
      nil
    (b* ((key (svar-fix (car keys)))
         (look (hons-get key (svex-env-fix env))))
      (if look
          (cons (cons key (cdr look))
                (svex-env-reduce-aux (cdr keys) env))
        (svex-env-reduce-aux (cdr keys) env)))))

(define svex-env-reduce
  :parents (svex-env)
  :short "Restrict an @(see svex-env) to only particular variables.  
Variables that are present in keys but not env will be left unbound."
  ((keys svarlist-p "Variables to keep.")
   (env  svex-env-p "Original environment to filter.  Need not be fast."))
  :returns
  (sub-env svex-env-p "Restriction of @('env') to @('keys').  Slow alist.")
  :prepwork ((local (in-theory (enable svex-env-reduce-aux svarlist-fix))))
  :verify-guards nil
  (mbe :logic (if (atom keys)
                  nil
                (b* ((key (svar-fix (car keys)))
                     (look (hons-get key (svex-env-fix env))))
                  (if look
                      (cons (cons key (cdr look))
                            (svex-env-reduce (cdr keys) env))
                    (svex-env-reduce (cdr keys) env))))
       :exec (with-fast-alist env (svex-env-reduce-aux keys env)))
  ///
  (local (defthm svex-env-reduce-aux-elim
           (equal (svex-env-reduce-aux keys env)
                  (svex-env-reduce keys env))))

  (verify-guards svex-env-reduce)

  (defthm svex-env-lookup-of-svex-env-reduce
    (equal (svex-env-lookup v (svex-env-reduce vars env))
           (if (member (svar-fix v) (svarlist-fix vars))
               (svex-env-lookup v env)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svarlist-fix svex-env-lookup))))

  (defthm svex-env-boundp-of-svex-env-reduce
         (iff (svex-env-boundp key (svex-env-reduce vars x))
              (and (member-equal (svar-fix key) (svarlist-fix vars))
                   (svex-env-boundp key x)))
         :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-reduce))))

  (local (in-theory (disable svex-env-reduce)))

  (defthm-svex-eval-flag
    (defthm svex-eval-reduce-var-superset
      (implies (subsetp (svex-vars x) (svarlist-fix vars))
               (equal (svex-eval x (svex-env-reduce vars env))
                      (svex-eval x env)))
      :hints ('(:expand ((svex-vars x)
                         (:free (env) (svex-eval x env)))))
      :flag expr)
    (defthm svexlist-eval-reduce-var-superset
      (implies (subsetp (svexlist-vars x) (svarlist-fix vars))
               (equal (svexlist-eval x (svex-env-reduce vars env))
                      (svexlist-eval x env)))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (env) (svexlist-eval x env)))))
      :flag list))

  (defthm svex-alist-eval-of-reduce-var-supserset
    (implies (subsetp (svexlist-vars (svex-alist-vals x)) (svarlist-fix vars))
             (equal (svex-alist-eval x (svex-env-reduce vars env))
                    (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vals svex-alist-vars svexlist-vars))))

  (local (defthm member-alist-keys-rw
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys hons-assoc-equal)))))

  (defthm alist-keys-of-svex-env-reduce
    (equal (alist-keys (svex-env-reduce vars env))
           (intersection-equal (svarlist-fix vars) (alist-keys (svex-env-fix env))))
    :hints(("Goal" :in-theory (e/d (svarlist-fix alist-keys
                                      svex-env-reduce
                                      intersection-equal)
                                   (hons-assoc-equal-of-svex-env-fix)))))


  (local (defthm svex-env-reduce-when-car-not-member
           (implies (not (member (caar x) (svarlist-fix keys)))
                    (equal (svex-env-reduce keys (cdr x))
                           (svex-env-reduce keys x)))
           :hints(("Goal" :in-theory (enable svex-env-reduce svex-env-lookup)))))

  (local (defthm svex-env-reduce-when-car-not-consp
           (implies (not (and (consp (car x)) (svar-p (caar x))))
                    (equal (svex-env-reduce keys (cdr x))
                           (svex-env-reduce keys x)))
           :hints(("Goal" :in-theory (enable svex-env-reduce svex-env-lookup)))))

  (local (defthm svarlist-p-of-alist-keys-of-env
           (implies (svex-env-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-env-p alist-keys)))))

  (defthm svex-env-reduce-when-alist-keys-equal
    (implies (and (equal (alist-keys (svex-env-fix x)) keys)
                  (no-duplicatesp keys))
             (equal (svex-env-reduce keys x)
                    (svex-env-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-reduce svex-env-fix alist-keys no-duplicatesp))
           (and stable-under-simplificationp
                (not (access acl2::clause-id id :pool-lst))
                '(:induct t))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-lookup)))))

  (defthm hons-assoc-equal-of-svex-env-reduce
    (equal (hons-assoc-equal v (svex-env-reduce keys x))
           (and (member v (svarlist-fix keys))
                (hons-assoc-equal v (svex-env-fix x))))
    :hints(("Goal" :in-theory (enable svex-env-reduce svarlist-fix hons-assoc-equal))))

  (defthm svex-env-reduce-of-superset
    (implies (subsetp (svarlist-fix keys) (svarlist-fix keys2))
             (Equal (svex-env-reduce keys (svex-env-reduce keys2 x))
                    (svex-env-reduce keys x)))
    :hints(("Goal" :in-theory (enable svex-env-reduce svarlist-fix))))

  (defthm svex-env-extract-of-subset-of-env-reduce
    (implies (subsetp (svarlist-fix keys) (svarlist-fix keys2))
             (Equal (svex-env-extract keys (svex-env-reduce keys2 x))
                    (svex-env-extract keys x)))
    :hints(("Goal" :in-theory (e/d (svex-env-extract svarlist-fix)
                                   (svex-env-reduce)))))


  (defthmd svex-env-reduce-redef
    (equal (svex-env-reduce keys env)
           (if (atom keys)
               nil
             (if (svex-env-boundp (car keys) env)
                 (cons (cons (svar-fix (car keys))
                             (svex-env-lookup (car keys) env))
                       (svex-env-reduce (cdr keys) env))
               (svex-env-reduce (cdr keys) env))))
    :hints (("goal" :in-theory (enable svex-env-boundp svex-env-lookup)
             :expand ((svex-env-reduce keys env))))
    :rule-classes :definition)

  ;; for :fix hook
  (local (in-theory (enable svex-env-reduce))))


(def-universal-equiv svex-envs-similar
  :qvars (k)
  :equiv-terms ((equal (svex-env-lookup k x)))
  :defquant t
  :parents (svex-env)
  :short "@('(svex-envs-similar x y)') is like alist equivalence for @(see
svex-env)s: environments are <b>similar</b> if they bind all variables to the
same values, in the sense of @(see svex-env-lookup)."

  :long "<p>Recall that @(see svex-env-lookup) treats any unbound variables as
being bound to an infinite X vector.  Accordingly, two environments need not
have the same bound variables to be regarded as equal.</p>

<p>This is an important equivalence relation that is satisfied by, e.g., @(see
svex-eval).  It is used more than is apparent because of the congruences it
provides.</p>")

(defsection svex-envs-similar-thms
  :extension (svex-envs-similar)
  ;; bozo would be nice for def-universal-equiv to support /// instead

  (defexample svex-envs-similar-lookup-ex
    :pattern (svex-env-lookup k x)
    :templates (k)
    :instance-rulename svex-envs-similar-instancing)

  (defcong svex-envs-similar equal (svex-env-lookup k x) 2
    :hints ((witness)))

  (defthm-svex-eval-flag
    (defthm svex-eval-env-congruence
      (implies (svex-envs-similar env env2)
               (equal (svex-eval x env) (svex-eval x env2)))
      :hints ('(:expand ((:free (env) (svex-eval x env)))))
      :rule-classes :congruence
      :flag expr)
    (defthm svexlist-eval-env-congruence
      (implies (svex-envs-similar env env2)
               (equal (svexlist-eval x env) (svexlist-eval x env2)))
      :hints ('(:expand ((:free (env) (svexlist-eval x env)))))
      :rule-classes :congruence
      :flag list))

  (defcong svex-envs-similar equal (svex-alist-eval x env) 2
    :hints(("Goal" :in-theory (enable svex-alist-eval))))

  (deffixcong svex-env-equiv svex-env-equiv (append a b) a)
  (deffixcong svex-env-equiv svex-env-equiv (append a b) b)

  (defrefinement svex-env-equiv svex-envs-similar
    :hints ((witness))))




(def-universal-equiv svex-envs-equivalent
  :qvars (k)
  :equiv-terms ((equal (svex-env-lookup k x))
                (iff (svex-env-boundp k x)))
  :defquant t
  :parents (svex-env)
  :short "@('(svex-envs-equivalent x y)') is a stronger form of alist
equivalence for @(see svex-env)s than @(see svex-envs-similar): environments
are <b>similar</b> if they bind all variables to the same values, in the sense
of @(see svex-env-lookup), and they bind the same variables.")

(defsection svex-envs-equivalent-thms
  :extension (svex-envs-equivalent)
  ;; bozo would be nice for def-universal-equiv to support /// instead

  (defexample svex-envs-equivalent-lookup-ex
    :pattern (svex-env-lookup k x)
    :templates (k)
    :instance-rulename svex-envs-equivalent-instancing)

  (defexample svex-envs-equivalent-boundp-ex
    :pattern (svex-env-boundp k x)
    :templates (k)
    :instance-rulename svex-envs-equivalent-instancing)

  (defrefinement svex-envs-equivalent svex-envs-similar
    :hints ((witness)))

  (local (defthmd equal-of-booleans
           (implies (and (booleanp a) (booleanp b))
                    (equal (equal a b) (iff a b)))))

  (defcong svex-envs-equivalent equal (svex-env-boundp k x) 2
    :hints (("goal" :in-theory (enable equal-of-booleans))
            (witness)))

  (defcong set-equiv svex-envs-equivalent (svex-env-extract keys env) 1
    :hints ((witness :ruleset svex-envs-equivalent-witnessing)))

  (defcong svex-envs-similar svex-envs-equivalent (svex-env-extract keys env) 2
    :hints ((witness :ruleset svex-envs-equivalent-witnessing)))

  (defthm svex-env-boundp-of-append
    (iff (svex-env-boundp k (append a b))
         (or (svex-env-boundp k a)
             (svex-env-boundp k b)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defthm svex-env-lookup-of-append
    (equal (svex-env-lookup k (append a b))
           (if (svex-env-boundp k a)
               (svex-env-lookup k a)
             (svex-env-lookup k b)))
    :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-lookup))))

  (defcong svex-envs-equivalent svex-envs-equivalent (append a b) 1
    :hints ((witness)))

  (defcong svex-envs-equivalent svex-envs-equivalent (append a b) 2
    :hints ((witness)))

  (defcong svex-envs-similar svex-envs-similar (append a b) 2
    :hints ((witness)))

  (defrefinement svex-env-equiv svex-envs-equivalent
    :hints ((witness))))





(define svex-alist-extract-aux ((keys svarlist-p)
                                (alist svex-alist-p))
  :returns (sub-alist svex-alist-p)
  (if (atom keys)
      nil
    (cons (cons (svar-fix (car keys))
                (or (svex-fastlookup (car keys) alist) (svex-x)))
          (svex-alist-extract-aux (cdr keys) alist))))

(define svex-alist-extract ((keys svarlist-p)
                            (alist svex-alist-p))
  :returns (sub-alist svex-alist-p)
  :verify-guards nil
  (mbe :logic
       (if (atom keys)
           nil
         (cons (cons (svar-fix (car keys))
                     (or (svex-fastlookup (car keys) alist) (svex-x)))
               (svex-alist-extract (cdr keys) alist)))
       :exec (with-fast-alist alist (svex-alist-extract-aux keys alist)))
  ///
  (local (defthm svex-alist-extract-aux-elim
           (equal (svex-alist-extract-aux x alist)
                  (svex-alist-extract x alist))
           :hints(("Goal" :in-theory (enable svex-alist-extract-aux)))))

  (verify-guards svex-alist-extract)

  (defret svex-alist-eval-of-svex-alist-extract
    (equal (svex-alist-eval sub-alist env)
           (svex-env-extract keys (svex-alist-eval alist env)))
    :hints(("Goal" :in-theory (enable svex-env-extract)
            :induct t
            :expand ((svex-alist-eval nil env)
                     (:free (a b) (svex-alist-eval (cons a b) env))))))

  (defret lookup-in-svex-alist-extract
    (equal (svex-lookup v sub-alist)
           (and (member (svar-fix v) (svarlist-fix keys))
                (or (svex-lookup v alist) (svex-x))))
    :hints(("Goal"
            :in-theory
            (e/d (svex-lookup hons-assoc-equal svarlist-fix)

; Matt K.:  The following rewrite rule made the proof fail after introducing
; the change, after v8-0, to keep LET expressions on right-hand-sides of
; rewrite rules, like this one.

                 (hons-assoc-equal-of-svex-alist-fix))))))



(define svex-alist-reduce-aux ((keys svarlist-p)
                                (alist svex-alist-p))
  :returns (sub-alist svex-alist-p)
  (if (atom keys)
      nil
    (let ((look (svex-fastlookup (car keys) alist)))
      (if look
          (cons (cons (svar-fix (car keys)) look)
                (svex-alist-reduce-aux (cdr keys) alist))
        (svex-alist-reduce-aux (cdr keys) alist)))))

(define svex-alist-reduce ((keys svarlist-p)
                            (alist svex-alist-p))
  :returns (sub-alist svex-alist-p)
  :verify-guards nil
  (mbe :logic
       (if (atom keys)
           nil
         (let ((look (svex-fastlookup (car keys) alist)))
           (if look
               (cons (cons (svar-fix (car keys)) look)
                     (svex-alist-reduce (cdr keys) alist))
             (svex-alist-reduce (cdr keys) alist))))
       :exec (with-fast-alist alist (svex-alist-reduce-aux keys alist)))
  ///
  (local (defthm svex-alist-reduce-aux-elim
           (equal (svex-alist-reduce-aux x alist)
                  (svex-alist-reduce x alist))
           :hints(("Goal" :in-theory (enable svex-alist-reduce-aux)))))

  (verify-guards svex-alist-reduce)

  (defret svex-alist-eval-of-svex-alist-reduce
    (equal (svex-alist-eval sub-alist env)
           (svex-env-reduce keys (svex-alist-eval alist env)))
    :hints(("Goal" :in-theory (enable svex-env-reduce-redef)
            :induct t
            :expand ((svex-alist-eval nil env)
                     (:free (a b) (svex-alist-eval (cons a b) env))))))

  (defret lookup-in-svex-alist-reduce
    (equal (svex-lookup v sub-alist)
           (and (member (svar-fix v) (svarlist-fix keys))
                (svex-lookup v alist)))
    :hints(("Goal"
            :in-theory
            (e/d (svex-lookup hons-assoc-equal svarlist-fix)

; Matt K.:  The following rewrite rule made the proof fail after introducing
; the change, after v8-0, to keep LET expressions on right-hand-sides of
; rewrite rules, like this one.

                 (hons-assoc-equal-of-svex-alist-fix))))))

(defun assigns-for-svassocs (args alist)
  (if (atom args)
      nil
    (cons (if (consp (car args))
              `(,(caar args) (sv::svex-env-lookup ,(cadar args) ,alist))
            (mv-let (sym ign)
              (acl2::decode-varname-for-patbind (car args))
              (declare (ignore ign))
              `(,(car args) (sv::svex-env-lookup ',sym ,alist))))
          (assigns-for-svassocs (cdr args) alist))))

(acl2::def-b*-binder svassocs
  :body
  #!acl2
  (b* (((mv pre-bindings name rest)
        (if (and (consp (car forms))
                 (not (eq (caar forms) 'quote)))
            (mv `((?tmp-for-assocs ,(car forms)))
                'tmp-for-assocs
                `(check-vars-not-free (tmp-for-assocs)
                                      ,rest-expr))
          (mv nil (car forms) rest-expr))))
    `(b* (,@pre-bindings
          . ,(sv::assigns-for-svassocs args name))
       ,rest)))


(define svex-env-removekeys ((keys svarlist-p) (env svex-env-p))
  :returns (new-env svex-env-p)
  (b* (((when (atom env)) nil)
       ((unless (mbt (and (consp (car env))
                          (svar-p (caar env)))))
        (svex-env-removekeys keys (cdr env)))
       ((when (member-equal (caar env) (svarlist-fix keys)))
        (svex-env-removekeys keys (cdr env))))
    (cons (mbe :logic (cons (caar env) (4vec-fix (cdar env)))
               :exec (car env))
          (svex-env-removekeys keys (cdr env))))
  ///
  (defret svex-env-boundp-of-<fn>
    (equal (svex-env-boundp key new-env)
           (and (not (member-equal (svar-fix key) (svarlist-fix keys)))
                (svex-env-boundp key env)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup key new-env)
           (if (member-equal (svar-fix key) (svarlist-fix keys))
               (4vec-x)
             (svex-env-lookup key env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (local (in-theory (enable svex-env-fix))))



(define svarlist-x-env ((x svarlist-p))
  :short "Creates an env alist that maps the given variables to X."
  :returns (subst svex-env-p)
  (b* (((when (atom x)) nil))
    (cons (cons (svar-fix (car x))
                (4vec-x))
          (svarlist-x-env (cdr x))))
  ///
  (defthm svex-env-lookup-of-svarlist-x-env
    (equal (svex-env-lookup var (svarlist-x-env x))
           (4vec-x))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (defthm svex-env-boundp-of-svarlist-x-env
    (iff (svex-env-boundp var (svarlist-x-env x))
         (member-equal (svar-fix var) (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-boundp)))))



(define svarlist-x-subst ((x svarlist-p))
  :short "Creates a substitution alist that maps the given variables to X."
  :returns (subst svex-alist-p)
  (b* (((when (atom x)) nil))
    (cons (cons (svar-fix (car x))
                (svex-x))
          (svarlist-x-subst (cdr x))))
  ///
  (defthm svex-lookup-of-svarlist-x-subst
    (implies (and (not (member v (svarlist-fix x)))
                  (svar-p v))
             (not (svex-lookup v (svarlist-x-subst x))))
    :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup))))

  (defthm vars-of-svarlist-x-subst
    (equal (svex-alist-vars (svarlist-x-subst x)) nil)
    :hints(("Goal" :in-theory (enable svex-alist-vars))))

  (defthm svex-alist-eval-of-svarlist-x-subst
    (equal (svex-alist-eval (svarlist-x-subst x) env)
           (svarlist-x-env x))
    :hints(("Goal" :in-theory (enable svarlist-x-env svex-alist-eval)))))
