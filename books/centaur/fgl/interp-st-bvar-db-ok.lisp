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
(include-book "interp-st-bfrs-ok")
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))


(Defsection interp-st-bvar-db-ok
  (defun-sk interp-st-bvar-db-ok (interp-st env)
    (forall n
            (b* ((bvar-db (interp-st->bvar-db interp-st))
                 (logicman (interp-st->logicman interp-st)))
              (implies (and (<= (base-bvar$c bvar-db) (nfix n))
                            (< (nfix n) (next-bvar$c bvar-db)))
                       (iff* (fgl-object-eval (get-bvar->term$c n bvar-db) env logicman)
                             (gobj-bfr-eval (bfr-var n) env logicman)))))
    :rewrite :direct)

  (in-theory (disable interp-st-bvar-db-ok))

  (local (defthm bfr-listp-of-append-when-each
           (implies (And (bfr-listp a)
                         (bfr-listp b))
                    (bfr-listp (append a b)))))

  ;; (local (in-theory (disable not-member-of-append)))

  (local (defthmd fgl-object-bfrlist-of-get-bvar->term$c-aux
           (implies (and (not (member v (bvar-db-bfrlist-aux m bvar-db)))
                         (< (nfix n) (nfix m))
                         (<= (base-bvar$c bvar-db) (nfix n)))
                    (not (member v (fgl-object-bfrlist (get-bvar->term$c n bvar-db)))))
           :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux)))))

  (local (defthm fgl-object-bfrlist-of-get-bvar->term$c
           (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                         (<= (base-bvar$c bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$c bvar-db)))
                    (not (member v (fgl-object-bfrlist (get-bvar->term$c n bvar-db)))))
           :hints (("goal" :in-theory (enable bvar-db-bfrlist)
                    :use ((:instance fgl-object-bfrlist-of-get-bvar->term$c-aux
                           (m (next-bvar$c bvar-db))))))))

  (local (defthm bfr-listp-of-bvar-db-bfrlist-when-equal
           (implies (and (equal bvar-db (interp-st->bvar-db interp-st))
                         (interp-st-bfrs-ok interp-st))
                    (bfr-listp (bvar-db-bfrlist bvar-db)
                               (logicman->bfrstate (interp-st->logicman interp-st))))))

  (local (in-theory (enable bfr-listp-when-not-member-witness)))
  
  (def-updater-independence-thm interp-st-bvar-db-ok-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (interp-st-bfrs-ok old)
                  (equal (interp-st->bvar-db new) (interp-st->bvar-db old)))
             (iff (interp-st-bvar-db-ok new env)
                  (interp-st-bvar-db-ok old env)))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'interp-st-bvar-db-ok clause))
                        (other (if (eq (cadr lit) 'new) 'old 'new)))
                   `(:expand (,lit)
                     :use ((:instance interp-st-bvar-db-ok-necc
                            (interp-st ,other)
                            (n (interp-st-bvar-db-ok-witness . ,(cdr lit)))))
                     :in-theory (e/d (bfr-varname-p)
                                     (interp-st-bvar-db-ok-necc)))))))
  
  (defcong logicman-equiv equal (bfr-var n logicman) 2
    :hints(("Goal" :in-theory (enable bfr-var))))

  (local (std::make-returnspec-config :hints-sub-returnnames t))
  
  (defret interp-st-bvar-db-ok-of-interp-st-add-term-bvar
    (implies (and (not (interp-st-bvar-db-ok interp-st env))
                  (interp-st-bfrs-ok interp-st))
             (not (interp-st-bvar-db-ok new-interp-st env)))
    :hints(("Goal" :in-theory (e/d (interp-st-add-term-bvar
                                    interp-st-bfrs-ok-implies
                                    bfr-varname-p)
                                   (interp-st-bvar-db-ok-necc))
            :expand ((interp-st-bvar-db-ok interp-st env))
            :use ((:instance interp-st-bvar-db-ok-necc
                   (interp-st new-interp-st)
                   (n (interp-st-bvar-db-ok-witness interp-st env))))
            :cases ((bfr-varname-p (interp-st-bvar-db-ok-witness interp-st env)
                                   (interp-st->logicman interp-st)))))
    ;; :otf-flg t
    :fn interp-st-add-term-bvar)

  (defret interp-st-bvar-db-ok-of-interp-st-add-term-bvar-unique
    (implies (and (not (interp-st-bvar-db-ok interp-st env))
                  (interp-st-bfrs-ok interp-st))
             (not (interp-st-bvar-db-ok new-interp-st env)))
    :hints(("Goal" :in-theory (e/d (interp-st-add-term-bvar-unique bfr-varname-p)
                                   (interp-st-bvar-db-ok-necc))
            :expand ((interp-st-bvar-db-ok interp-st env))
            :use ((:instance interp-st-bvar-db-ok-necc
                   (interp-st new-interp-st)
                   (n (interp-st-bvar-db-ok-witness interp-st env))))
            :cases ((bfr-varname-p (interp-st-bvar-db-ok-witness interp-st env)
                                   (interp-st->logicman interp-st)))))
    :otf-flg t
    :fn interp-st-add-term-bvar-unique))

(define bvar-db-to-bfr-env-aux ((n natp) (env fgl-env-p) bvar-db logicman)
  :guard (and (<= n (next-bvar bvar-db))
              (<= (base-bvar bvar-db) n)
              (bvar-db-bfrs-ok bvar-db (logicman->bfrstate))
              ;; (not (consp (bvar-db-bfrlist bvar-db)))
              )
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  (b* (((When (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql (next-bvar bvar-db) n)))
        (fgl-env-fix env))
       (obj (get-bvar->term n bvar-db))
       (val (bool-fix (fgl-object-eval obj env logicman)))
       (env (change-fgl-env env :bfr-vals (bfr-set-var n val (fgl-env->bfr-vals env)))))
    (bvar-db-to-bfr-env-aux (+ 1 (lnfix n)) env bvar-db logicman))
  ///

  (defthm fgl-env->obj-alist-of-bvar-db-to-bfr-env-aux
    (equal (fgl-env->obj-alist (bvar-db-to-bfr-env-aux n env bvar-db logicman))
           (fgl-env->obj-alist env)))

  (defthm gobj-var-lookup-of-bfr-set-var
    (equal (gobj-var-lookup v (fgl-env (fgl-env->obj-alist env)
                                      bfr-vals))
           (gobj-var-lookup v env))
    :hints(("Goal" :in-theory (enable gobj-var-lookup))))

  (defthm gobj-var-lookup-of-bvar-db-to-bfr-env-aux
    (equal (gobj-var-lookup v (bvar-db-to-bfr-env-aux n env bvar-db logicman))
           (gobj-var-lookup v env)))

  (defthm bvar-db-to-bfr-env-aux-preserves-bfr-eval-when-bounded
    (implies (and (bfr-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (bfr-eval x (fgl-env->bfr-vals (bvar-db-to-bfr-env-aux n env bvar-db logicman)) logicman)
                    (bfr-eval x (fgl-env->bfr-vals env) logicman))))

  (defthm bvar-db-to-bfr-env-aux-preserves-bfrlist-eval-when-bounded
    (implies (and (bfrlist-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (bfr-list-eval x (fgl-env->bfr-vals (bvar-db-to-bfr-env-aux n env bvar-db logicman)) logicman)
                    (bfr-list-eval x (fgl-env->bfr-vals env) logicman)))
    :hints(("Goal" :in-theory (e/d (bfrlist-boundedp bfr-list-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm bvar-db-to-bfr-env-aux-preserves-gobj-bfr-eval-when-bounded
    (implies (and (bfr-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                    (gobj-bfr-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (gobj-bfr-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm bvar-db-to-bfr-env-aux-preserves-gobj-bfrlist-eval-when-bounded
    (implies (and (bfrlist-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-list-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                    (gobj-bfr-list-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (bfrlist-boundedp gobj-bfr-list-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm gobj-bfr-eval-of-set-var-when-bounded
    (implies (and (bfr-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-eval x (fgl-env (fgl-env->obj-alist env)
                                             (bfr-set-var n v (fgl-env->bfr-vals env))) logicman)
                    (gobj-bfr-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (gobj-bfr-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm gobj-bfrlist-eval-of-set-var-when-bounded
    (implies (and (bfrlist-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-list-eval x (fgl-env (fgl-env->obj-alist env)
                                                  (bfr-set-var n v (fgl-env->bfr-vals env))) logicman)
                    (gobj-bfr-list-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (bfrlist-boundedp gobj-bfr-list-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defret-mutual fgl-object-eval-of-bvar-db-to-bfr-env-aux-when-bounded
    (defret fgl-object-eval-of-bvar-db-to-bfr-env-aux-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                      (fgl-object-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-eval x env logicman))
                         (fgl-object-bfrlist x)))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable if*
              ;;                           gobj-var-lookup
              ;;                           gobj-bfr-list-eval)))
              )
      :fn fgl-object-eval)

    (defret fgl-objectlist-eval-of-bvar-db-to-bfr-env-aux-when-bounded
      (implies (and (bfrlist-boundedp (fgl-objectlist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-objectlist-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                      (fgl-objectlist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-objectlist-eval x env logicman))
                         (fgl-objectlist-bfrlist x)))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable if*
              ;;                           gobj-var-lookup
              ;;                           gobj-bfr-list-eval)))
              )
      :fn fgl-objectlist-eval)

    (defret fgl-object-alist-eval-of-bvar-db-to-bfr-env-aux-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-alist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-alist-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                      (fgl-object-alist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-alist-eval x env logicman))
                         (fgl-object-alist-bfrlist x)))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable if*
              ;;                           gobj-var-lookup
              ;;                           gobj-bfr-list-eval)))
              )
      :fn fgl-object-alist-eval)
    :mutual-recursion fgl-object-eval)

  (defret-mutual fgl-object-eval-of-bfr-set-var-when-bounded
    (defret fgl-object-eval-of-bfr-set-var-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-eval x (fgl-env (fgl-env->obj-alist env)
                                                 (bfr-set-var n v (fgl-env->bfr-vals env)))
                                       logicman)
                      (fgl-object-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-eval x env logicman))
                         (fgl-object-bfrlist x))))
      :fn fgl-object-eval)

    (defret fgl-objectlist-eval-of-bfr-set-var-when-bounded
      (implies (and (bfrlist-boundedp (fgl-objectlist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-objectlist-eval x (fgl-env (fgl-env->obj-alist env)
                                                     (bfr-set-var n v (fgl-env->bfr-vals env)))
                                       logicman)
                      (fgl-objectlist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-objectlist-eval x env logicman))
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-eval)

    (defret fgl-object-alist-eval-of-bfr-set-var-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-alist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-alist-eval x (fgl-env (fgl-env->obj-alist env)
                                                     (bfr-set-var n v (fgl-env->bfr-vals env)))
                                       logicman)
                      (fgl-object-alist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-alist-eval x env logicman))
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-eval)
    :mutual-recursion fgl-object-eval)


  (defthm bfr-lookup-preserved-by-of-bvar-db-to-bfr-env-aux
    (implies (< (nfix m) (nfix n))
             (equal (bfr-lookup m (fgl-env->bfr-vals
                                   (bvar-db-to-bfr-env-aux n env bvar-db logicman)))
                    (bfr-lookup m (fgl-env->bfr-vals env)))))

  ;; (defret fgl-object-eval-when-no-bvars-rw
  ;;   (implies (and (syntaxp (not (and (equal bfr-env ''nil)
  ;;                                    (equal logicman ''nil))))
  ;;                 (not (consp (fgl-object-bfrlist x))))
  ;;            (equal (fgl-object-eval x (fgl-env obj-alist bfr-env) logicman)
  ;;                   (fgl-object-eval x (fgl-env obj-alist nil) nil)))
  ;;   :hints (("Goal" :use ((:instance fgl-object-eval-when-no-bvars
  ;;                          (env (fgl-env obj-alist bfr-env))))
  ;;            :in-theory (disable fgl-object-eval-when-no-bvars)))
  ;;   :fn fgl-object-eval)



  (local (in-theory (enable bfr-varname-p)))

  (defthm bvar-db-to-bfr-env-aux-correct
    (implies (and (bvar-db-boundedp bvar-db logicman)
                  (<= (base-bvar$c bvar-db) (nfix n))
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (next-bvar$c bvar-db))
                  (equal (next-bvar$c bvar-db) (bfr-nvars logicman)))
             (iff (bfr-lookup m
                              (fgl-env->bfr-vals (bvar-db-to-bfr-env-aux n env bvar-db logicman))
                              logicman)
                  (fgl-object-eval (get-bvar->term$c m bvar-db)
                                   (bvar-db-to-bfr-env-aux n env bvar-db logicman)
                                   logicman)))
    :hints (("goal"
             :in-theory (enable* acl2::arith-equiv-forwarding)
             :induct (bvar-db-to-bfr-env-aux n env bvar-db logicman))
            (and stable-under-simplificationp
                 '(:use ((:instance bvar-db-boundedp-necc
                          (var (nfix m))))))))

  (defthm bfr-set-var-when-logicman-equiv
    (implies (logicman-equiv logicman1 logicman2)
             (equal (bfr-set-var n val env logicman1)
                    (bfr-set-var n val env logicman2)))
    :hints(("Goal" :in-theory (enable bfr-set-var)))
    :rule-classes :congruence)

  (defthm bvar-db-to-bfr-env-aux-logicman-equiv
    (implies (logicman-equiv logicman1 logicman2)
             (equal (bvar-db-to-bfr-env-aux n env bvar-db logicman1)
                    (bvar-db-to-bfr-env-aux n env bvar-db logicman2)))
    :rule-classes :congruence))

(define fix-env-for-bvar-db ((env fgl-env-p) bvar-db logicman)
  :guard (bvar-db-bfrs-ok bvar-db (logicman->bfrstate))
  (bvar-db-to-bfr-env-aux (base-bvar bvar-db) env bvar-db logicman)
  ///

  (local (in-theory (enable bfr-varname-p)))

  (defthm interp-st-bvar-db-ok-of-fix-env-for-bvar-db
    (b* ((bvar-db (interp-st->bvar-db interp-st))
         (logicman (interp-st->logicman interp-st)))
      (implies (interp-st-bfrs-ok interp-st)
               (interp-st-bvar-db-ok interp-st
                                     (fix-env-for-bvar-db env bvar-db logicman))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-db-ok
                                      interp-st-bfrs-ok))))

  (defthm fgl-env->obj-alist-of-<fn>
    (equal (fgl-env->obj-alist (fix-env-for-bvar-db env bvar-db logicman))
           (fgl-env->obj-alist env)))

  (defthm fix-env-for-bvar-db-when-logicman-equiv
    (implies (logicman-equiv logicman1 logicman2)
             (equal (fix-env-for-bvar-db env bvar-db logicman1)
                    (fix-env-for-bvar-db env bvar-db logicman2)))
    :rule-classes :congruence))

