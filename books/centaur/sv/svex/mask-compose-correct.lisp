; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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

(include-book "rewrite")
(include-book "compose-theory-base")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "clause-processors/find-matching" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define svex-mask-alist-negcount ((keys svarlist-p)
                                  (masks svex-mask-alist-p))
  :returns (count natp :rule-classes :type-prescription)
  (if (atom keys)
      0
    (+ (if (sparseint-< (svex-mask-lookup (svex-var (car keys)) masks) 0)
           1
         0)
       (svex-mask-alist-negcount (cdr keys) masks))))

(define svex-mask-alist-nonnegcount ((keys svarlist-p)
                                  (masks svex-mask-alist-p))
  :returns (count natp :rule-classes :type-prescription)
  (if (atom keys)
      0
    (+ (let ((look (svex-mask-lookup (svex-var (car keys)) masks)))
         (if (sparseint-< look 0)
             0
           (sparseint-bitcount look)))
       (svex-mask-alist-nonnegcount (cdr keys) masks))))

(define svex-mask-alist-measure ((keys svarlist-p)
                                 (masks svex-mask-alist-p))
  (list (svex-mask-alist-negcount keys masks)
        (svex-mask-alist-nonnegcount keys masks)))

(local
 (defthmd logcount-less-when-logandc1-0-and-unequal
   (implies (and (equal 0 (logand x (lognot y)))
                 (not (equal (ifix x) (ifix y)))
                 (<= 0 (ifix y)))
            (< (logcount x) (logcount y)))
   :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs)
           :induct (logand x y)))))

(defthm sparseint-bitcount-decr-when-4vmask-subsumes
  (implies (and (4vmask-subsumes y x)
                (not (equal (sparseint-val (4vmask-fix x))
                            (sparseint-val (4vmask-fix y))))
                (<= 0 (sparseint-val (4vmask-fix y))))
           (< (logcount (sparseint-val (4vmask-fix x)))
              (logcount (sparseint-val (4vmask-fix y)))))
  :hints(("Goal" :in-theory (enable 4vmask-subsumes
                                    logcount-less-when-logandc1-0-and-unequal)))
  :rule-classes :linear)

(defthm sparseint-bitcount-decr-when-4vmask-subsumes-no-fix
  (implies (and (4vmask-subsumes y x)
                (4vmask-p x) (4vmask-p y)
                (not (equal (sparseint-val x)
                            (sparseint-val y)))
                (<= 0 (sparseint-val y)))
           (< (logcount (sparseint-val x))
              (logcount (sparseint-val y))))
  :hints(("Goal" :in-theory (enable 4vmask-subsumes
                                    logcount-less-when-logandc1-0-and-unequal)))
  :rule-classes :linear)


(define check-masks-decreasing ((assigns svex-alist-p)
                                (masks svex-mask-alist-p)
                                (new-masks svex-mask-alist-p))
  :returns (status)
  ;; t for decreasing
  ;; nil for nonincreasing
  ;; svar key for increasing
  (b* (((when (atom assigns)) nil)
       ((unless (mbt (and (consp (car assigns))
                          (svar-p (caar assigns)))))
        (check-masks-decreasing (cdr assigns) masks new-masks))
       (key (caar assigns))
       (svex-key (svex-var key))
       (mask1 (svex-mask-lookup svex-key masks))
       (mask2 (svex-mask-lookup svex-key new-masks))
       ((unless (4vmask-subsumes mask1 mask2))
        ;; violation
        key)
       ((when (or (sparseint-equal mask1 mask2)
                  (and (sparseint-< mask1 0)
                       (sparseint-< mask2 0))))
        ;; nonincreasing
        (check-masks-decreasing (cdr assigns) masks new-masks))
       ;; otherwise decreasing, as long as rest is nonincreasing
       (rest (check-masks-decreasing (cdr assigns) masks new-masks)))
    (or rest t))
  ///
  (local (defthm 4vmask-subsumes-false-by-sign
           (implies (and (<= 0 (sparseint-val (4vmask-fix x)))
                         (< (sparseint-val (4vmask-fix y)) 0))
                    (not (4vmask-subsumes x y)))
           :hints(("Goal" :in-theory (enable 4vmask-subsumes)) )))

  (defret svex-mask-alist-measure-decreasing-by-<fn>
    (let* ((keys (svex-alist-keys assigns))
           (new-meas (svex-mask-alist-measure keys new-masks))
           (old-meas (svex-mask-alist-measure keys masks)))
      (and (implies (not status)
                    (equal new-meas old-meas))
           (implies (equal status t)
                    (acl2::nat-list-< new-meas old-meas))))
    :hints(("Goal" :in-theory (enable svex-mask-alist-measure
                                      svex-alist-keys
                                      svex-mask-alist-negcount
                                      svex-mask-alist-nonnegcount))))

  (local (in-theory (enable svex-alist-fix))))


(local (defthmd svex-lookup-redef
         (equal (svex-lookup key alist)
                (cond ((atom alist) nil)
                      ((and (consp (car alist))
                            (equal (caar alist) (svar-fix key)))
                       (svex-fix (cdar alist)))
                      (t (svex-lookup key (cdr alist)))))
         :hints(("Goal" :in-theory (enable svex-lookup)))
         :rule-classes :definition))

(define svex-maskcompose-decreasing-vars ((assigns svex-alist-p)
                                (masks svex-mask-alist-p)
                                (new-masks svex-mask-alist-p))
  :returns (decr svarlist-p)
  (b* (((when (atom assigns)) nil)
       ((unless (mbt (and (consp (car assigns))
                          (svar-p (caar assigns)))))
        (svex-maskcompose-decreasing-vars (cdr assigns) masks new-masks))
       (key (caar assigns))
       (svex-key (svex-var key))
       (mask1 (svex-mask-lookup svex-key masks))
       (mask2 (svex-mask-lookup svex-key new-masks))
       ;; ((unless (4vmask-subsumes mask1 mask2))
       ;;  ;; violation
       ;;  key)
       ((when (sparseint-equal mask1 mask2))
        ;; nonincreasing
        (svex-maskcompose-decreasing-vars (cdr assigns) masks new-masks))
       ;; otherwise decreasing, as long as rest is nonincreasing
       (rest (svex-maskcompose-decreasing-vars (cdr assigns) masks new-masks)))
    (cons key rest))
  ///
  (defret <fn>-subsetp-of-svex-alist-keys
    (subsetp-equal decr (svex-alist-keys assigns))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defretd mask-lookup-when-not-member-<fn>
    (implies (and (booleanp (check-masks-decreasing assigns masks new-masks))
                  (not (member-equal (svar-fix v) decr))
                  (svex-lookup v assigns))
             (equal (sparseint-val (svex-mask-lookup (svex-var v) new-masks))
                    (sparseint-val (svex-mask-lookup (svex-var v) masks))))
    :hints(("Goal" :in-theory (enable check-masks-decreasing
                                      svex-lookup-redef))))

  (local (in-theory (enable svex-alist-fix))))


(local (defthm svex-lookup-of-cons
         (equal (svex-lookup key (cons (cons var val) rest))
                (if (and (svar-p var)
                         (equal (svar-fix key) var))
                    (svex-fix val)
                  (svex-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))

(define svex-maskcompose-step-alist ((assigns svex-alist-p)
                                      (masks svex-mask-alist-p)
                                      (new-masks svex-mask-alist-p)
                                      (composed svex-alist-p))
  :returns (new-composed svex-alist-p)
  ;; t for decreasing
  ;; nil for nonincreasing
  ;; svar key for increasing
  :guard-hints (("goal" :in-theory (enable svex-compose-lookup)))
  (b* (((when (atom assigns)) nil)
       ((unless (mbt (and (consp (car assigns))
                          (svar-p (caar assigns)))))
        (svex-maskcompose-step-alist (cdr assigns) masks new-masks composed))
       (key (caar assigns))
       (svex-key (svex-var key))
       (mask1 (svex-mask-lookup svex-key masks))
       (mask2 (svex-mask-lookup svex-key new-masks))
       ((when (sparseint-equal mask1 mask2))
        ;; nonincreasing
        (b* ((rest (svex-maskcompose-step-alist (cdr assigns) masks new-masks composed)))
          (cons (cons key (mbe :logic (svex-compose-lookup key composed)
                               :exec (or (svex-fastlookup key composed) svex-key)))
                rest)))
       ;; otherwise decreasing, as long as rest is nonincreasing
       (rest (svex-maskcompose-step-alist (cdr assigns) masks new-masks composed)))
    (cons (cons key (svex-compose (cdar assigns) composed)) rest))
  ///

  (local (in-theory (disable member-svex-mask-alist-keys
                             member-equal
                             equal-of-svex-var)))
  
  (local (defthm svex-lookup-caar
           (implies (and (consp x)
                         (consp (car x))
                         (svar-p (caar x)))
                    (equal (svex-lookup (caar x) x)
                           (svex-fix (cdar x))))
           :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))

  (local (defthm svex-alist-reduce-cdr
           (implies (or (not (consp x))
                        (not (consp (car x)))
                        (not (svar-p (caar x)))
                        (not (member-equal (caar x) (svarlist-fix keys))))
                    (equal (svex-alist-reduce keys (cdr x))
                           (svex-alist-reduce keys x)))
           :hints(("Goal" :induct (svex-alist-reduce keys x)
                   :in-theory (enable (:i svex-alist-reduce)
                                      svex-lookup
                                      member-equal)
                   :expand ((:free (x) (svex-alist-reduce keys x)))))))

  (local (defthm not-member-of-svex-maskcompose-decreasing-vars
           (implies (not (svex-lookup key x))
                    (not (member-equal (svar-fix key)
                                       (svex-maskcompose-decreasing-vars x masks new-masks))))
           :hints(("Goal" :in-theory (enable svex-maskcompose-decreasing-vars
                                             svex-lookup member-equal)))))
                         
  (defret <fn>-correct
    (implies (no-duplicatesp-equal (svex-alist-keys assigns))
             (svex-alist-eval-equiv new-composed
                                    (svex-alist-compose
                                     (append (svex-alist-reduce
                                              (svex-maskcompose-decreasing-vars assigns masks new-masks)
                                              assigns)
                                             (svex-identity-subst (svex-alist-keys assigns)))
                                     composed)))
    :hints (("goal" :induct <call>
             :in-theory (e/d (svex-acons svex-compose-lookup)
                             ((:d <fn>)))
             :expand (<call>
                      (svex-maskcompose-decreasing-vars assigns masks new-masks)
                      (svex-alist-keys assigns)
                      (:free (a b) (svex-alist-reduce (cons a b) assigns))
                      (:free (a b c) (append (cons a b) c))
                      (:free (a b) (svex-alist-compose (cons a b) composed))))
            (and stable-under-simplificationp
                 `(:computed-hint-replacement
                   ((let ((key (acl2::find-call-lst 'SVEX-ALIST-eval-equiv-witness clause)))
                   `(:clause-processor (acl2::generalize-with-alist-cp clause '((,key . key))))))
                   :expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:expand ((svex-compose (svex-var key) composed))))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys new-composed)
           (svex-alist-keys assigns))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (local (in-theory (enable svex-alist-fix))))


(define svex-mask-alist-expand ((x svex-mask-alist-p))
  :returns (mask-al svex-mask-alist-p)
  (b* (((mv toposort al) (cwtime (svexlist-toposort (svex-mask-alist-keys x) nil nil)))
       (- (fast-alist-free al)))
    (cwtime (svexlist-compute-masks toposort (make-fast-alist x))))
  ///

  (fty::deffixequiv svex-mask-alist-expand)

  (defthm svex-mask-alist-expand-complete
    (svex-mask-alist-complete (svex-mask-alist-expand x)))

  ;;  svex-mask-alist-expand ((x svex-mask-alist-p))
  ;;   :returns (mask-al svex-mask-alist-p)
  (defret svex-mask-alist-expand-lookup-subsumes
    (implies (4vmask-subsumes (svex-mask-lookup key x) m)
             (4vmask-subsumes (svex-mask-lookup key mask-al)
                              m))
    :hints(("Goal" :in-theory (enable svex-mask-alist-expand)))))


(local (defthmd svex-lookup-redef2
         (equal (svex-lookup key alist)
                (let ((alist (svex-alist-fix alist)))
                  (cond ((atom alist) nil)
                        ((and (consp (car alist))
                              (equal (caar alist) (svar-fix key)))
                         (cdar alist))
                        (t (svex-lookup key (cdr alist))))))
         :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))
         :rule-classes :definition))

(local (defthm svex-mask-lookup-of-cons
         (equal (svex-mask-lookup key1 (cons (cons key val) rest))
                (if (equal (svex-fix key1) key)
                    (4vmask-fix val)
                  (svex-mask-lookup key1 rest)))
         :hints(("Goal" :in-theory (enable svex-mask-lookup)))))

(define svex-updates-pair-masks ((updates svex-alist-p)
                                 (masks svex-mask-alist-p))
  :returns (newmasks svex-mask-alist-p
                     :hints(("Goal" :in-theory (enable svex-mask-alist-p))))
  :verify-guards :after-returns
  :guard-hints (("goal" :in-theory (enable svarlist-p)))
  :measure (len (svex-alist-fix updates))
  (b* ((updates (svex-alist-fix updates))
       ((when (atom updates)) nil)
       ((cons var svex) (car updates))
       (rest (svex-updates-pair-masks (cdr updates) masks))
       (mask (svex-mask-lookup (svex-var var) masks))
       (rest-mask (svex-mask-lookup svex rest))
       (full-mask (sparseint-bitor mask rest-mask))
       ((when (sparseint-equal full-mask rest-mask))
        rest))
    (cons (cons svex full-mask) rest))
  ///
  (deffixequiv svex-updates-pair-masks
    :hints(("Goal" :in-theory (enable svarlist-fix))))

  (local (defthm 4vmask-subsumes-of-bitor-1
           (implies (and (4vmask-subsumes a c)
                         (4vmask-p a))
                    (4vmask-subsumes (sparseint-bitor a b) c))
           :hints(("Goal" :in-theory (enable 4vmask-subsumes))
                  (bitops::logbitp-reasoning))))

  (local (defthm 4vmask-subsumes-of-bitor-2
           (implies (and (4vmask-subsumes b c)
                         (4vmask-p b))
                    (4vmask-subsumes (sparseint-bitor a b) c))
           :hints(("Goal" :in-theory (enable 4vmask-subsumes))
                  (bitops::logbitp-reasoning))))

  (local (defthm sub-logior-into-4vmask-subsumes
           (implies (and (equal (logior (sparseint-val a) (sparseint-val b))
                                (sparseint-val c))
                         (4vmask-p a) (4vmask-p b) (4vmask-p c))
                    (iff (4vmask-subsumes c d)
                           (4vmask-subsumes (sparseint-bitor a b) d)))
           :hints(("Goal" :in-theory (enable 4vmask-subsumes)))))

  (defret lookup-of-<fn>
    (implies (svex-lookup key updates)
             (4vmask-subsumes (svex-mask-lookup (svex-lookup key updates) newmasks)
                              (svex-mask-lookup (svex-var key) masks)))
    :hints(("Goal" :in-theory (enable <fn>)
            :induct <call>
            :expand ((svex-lookup key updates))
            ))))
  
(define svex-assigns-propagate-masks ((masks svex-mask-alist-p)
                                      (assigns svex-alist-p))
  :returns (new-masks svex-mask-alist-p)
  (b* ((masks1
        ;; this pairs the update function for each var to the mask of that var
        (svex-updates-pair-masks assigns masks)))
    (svex-mask-alist-expand masks1))
  ///
  (defret svex-mask-alist-complete-of-<fn>
    (svex-mask-alist-complete new-masks))

  (defret mask-lookup-of-svex-lookup-of-<fn>
    (implies (and (svex-lookup key assigns)
                  (4vmask-subsumes (svex-mask-lookup (svex-var key) masks) m))
             (4vmask-subsumes (svex-mask-lookup (svex-lookup key assigns) new-masks)
                              m))))

(defsection svex-envs-agree-on-masks
  (defun-sk svex-envs-agree-on-masks (masks env1 env2)
    (forall var
            (let ((mask (svex-mask-lookup (svex-var var) masks)))
              (equal (4vec-mask mask
                                (svex-env-lookup var env1))
                     (4vec-mask mask
                                (svex-env-lookup var env2)))))
    :rewrite :direct)

  (in-theory (disable svex-envs-agree-on-masks))

  (defthm svex-envs-agree-on-masks-implies-var
    (implies (and (svex-envs-agree-on-masks masks env1 env2)
                  (svex-case x :var))
             (let* ((mask (svex-mask-lookup x masks))
                    (name (svex-var->name x)))
               (equal (4vec-mask mask (svex-env-lookup name env1))
                      (4vec-mask mask (svex-env-lookup name env2)))))
    :hints (("goal" :use ((:instance svex-envs-agree-on-masks-necc
                           (var (svex-var->name x))))
             :in-theory (disable svex-envs-agree-on-masks-necc))))


  (local (defthm svex-argmasks-okp-apply
           (implies (and (svex-case x :call)
                         (equal (4veclist-mask argmasks (svexlist-eval (svex-call->args x) env))
                                (4veclist-mask argmasks vals))
                         (svex-argmasks-okp x mask argmasks))
                    (equal (equal (4vec-mask mask (svex-apply (svex-call->fn x)
                                                              (svexlist-eval (svex-call->args x) env)))
                                  (4vec-mask mask (svex-apply (svex-call->fn x)
                                                              vals)))
                           t))
           :hints (("goal" :use ((:instance svex-argmasks-okp-necc))
                    :expand ((svex-eval x env))
                    :in-theory (disable svex-argmasks-okp-necc)))))

  (local (in-theory (enable svex-mask-alist-complete-necc)))

  (defthm-svex-eval-flag svex-envs-agree-on-masks-implies-eval-when-svex-mask-alist-complete
    (defthm svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
      (implies (And (svex-envs-agree-on-masks masks env1 env2)
                    (svex-mask-alist-complete masks))
               (let ((mask (svex-mask-lookup x masks)))
                 (equal (4vec-mask mask (svex-eval x env1))
                        (4vec-mask mask (svex-eval x env2)))))
      :hints ('(:expand ((:free (env) (svex-eval x env)))))
      :flag expr)
    (defthm svex-envs-agree-on-masks-implies-svexlist-eval-when-svex-mask-alist-complete
      (implies (And (svex-envs-agree-on-masks masks env1 env2)
                    (svex-mask-alist-complete masks))
               (let ((mask (svex-argmasks-lookup x masks)))
                 (equal (4veclist-mask mask (svexlist-eval x env1))
                        (4veclist-mask mask (svexlist-eval x env2)))))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svex-argmasks-lookup x masks)
                         (:free (a b c d) (4veclist-mask (cons a b) (cons c d))))))
      :flag list))


  (defthm svex-envs-agree-on-masks-propagate-masks
    (implies (svex-envs-agree-on-masks
              (svex-assigns-propagate-masks masks updates)
              env1 env2)
             (svex-envs-agree-on-masks
              masks
              (svex-alist-eval updates env1)
              (svex-alist-eval updates env2)))
    :hints (("goal" :expand ((svex-envs-agree-on-masks
                              masks
                              (svex-alist-eval updates env1)
                              (svex-alist-eval updates env2))))
            (and stable-under-simplificationp
                 (let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                   `(:computed-hint-replacement
                     ('(:use ((:instance svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                               (masks (svex-assigns-propagate-masks masks updates))
                               (x (svex-lookup var updates)))
                              (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                               (assigns updates)
                               (key var)
                               (m (svex-mask-lookup (svex-var var) masks))))
                        :in-theory (disable svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                                            mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks)))
                     :clause-processor (acl2::generalize-with-alist-cp clause '((,var . var))))))))

  (defcong svex-envs-similar iff (svex-envs-agree-on-masks masks env1 env2) 2
    :hints ((and stable-under-simplificationp
                 (let ((lit (assoc 'svex-envs-agree-on-masks clause)))
                   `(:computed-hint-replacement
                     ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                        (and var
                             `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
                     :expand (,lit))))))

  (defcong svex-envs-similar iff (svex-envs-agree-on-masks masks env1 env2) 3
    :hints ((and stable-under-simplificationp
                 (let ((lit (assoc 'svex-envs-agree-on-masks clause)))
                   `(:computed-hint-replacement
                     ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                        (and var
                             `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
                     :expand (,lit))))))

  (defthm svex-envs-agree-on-masks-refl
    (svex-envs-agree-on-masks masks x x)
    :hints(("Goal" :in-theory (enable svex-envs-agree-on-masks)))))
                  


(local (defthm svarlist-p-alist-keys-of-svex-env
         (implies (svex-env-p x)
                  (svarlist-p (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys)))))


(local
 (progn
   
   (local (defthm consp-of-hons-assoc-equal
            (iff (consp (hons-assoc-equal k a))
                 (hons-assoc-equal k a))))

   (local (defthmd hons-assoc-equal-iff-member-alist-keys
            (iff (hons-assoc-equal k a)
                 (member-equal k (alist-keys a)))
            :hints(("Goal" :in-theory (enable alist-keys)))))

   (local (defthmd member-alist-keys-iff-svex-env-boundp
            (iff (member-equal (svar-fix k) (alist-keys a))
                 (svex-env-boundp k a))
            :hints(("Goal" :in-theory (enable svex-env-boundp hons-assoc-equal-iff-member-alist-keys)))))

   (local (defthmd svex-env-boundp-redef
            (iff (svex-env-boundp var env)
                 (hons-assoc-equal (svar-fix var) (svex-env-fix env)))
            :hints(("Goal" :in-theory (enable svex-env-boundp)))))

   (local (defthm alist-keys-not-set-equiv-by-boundp-1
            (implies (and (svex-env-boundp var b)
                          (not (svex-env-boundp var a)))
                     (not (set-equiv (alist-keys (svex-env-fix a))
                                     (alist-keys (svex-env-fix b)))))
            :hints(("Goal" :in-theory (enable svex-env-boundp-redef
                                              hons-assoc-equal-iff-member-alist-keys)))))
   (local (defthm alist-keys-not-set-equiv-by-boundp-2
            (implies (and (svex-env-boundp var a)
                          (not (svex-env-boundp var b)))
                     (not (set-equiv (alist-keys (svex-env-fix a))
                                     (alist-keys (svex-env-fix b)))))
            :hints(("Goal" :in-theory (enable svex-env-boundp-redef
                                              hons-assoc-equal-iff-member-alist-keys)))))

   (local (defcong set-equiv svex-envs-equivalent (svarlist-x-env x) 1
            :hints(("Goal" :in-theory (enable svex-envs-equivalent)))))))



(define svex-alist-maskcompose-iter-simple
  ((masks svex-mask-alist-p "Masks -- initially all -1")
   (loop-updates svex-alist-p ;; original dfs-composed assignments
                 "Subset of update including only the bindings of the variables
                  that also appear as inputs."))
  :prepwork ((local (defthm svarlist-p-of-instersection
                      (implies (svarlist-p a)
                               (svarlist-p (intersection-equal a b)))
                      :hints(("Goal" :in-theory (enable svarlist-p)))))
             (local (include-book "std/lists/take" :dir :system))
             (local (defthm svarlist-p-of-take
                      (implies (and (svarlist-p x)
                                    (<= (nfix n) (len x)))
                               (svarlist-p (take n x)))
                      :hints(("Goal" :in-theory (enable svarlist-p))))))
  :ruler-extenders :lambdas
  :hints(("Goal" :in-theory (enable o<)))
  :verify-guards nil
  :measure (svex-mask-alist-measure (svex-alist-keys loop-updates) masks)
  :returns (mv (final-masks svex-mask-alist-p)
               (new-updates svex-alist-p))

  :well-founded-relation acl2::nat-list-<
  (b* ((next-masks (svex-assigns-propagate-masks masks loop-updates))
       (status (check-masks-decreasing loop-updates masks next-masks))
       ((unless status)
        (cw "Masks stopped shrinking~%")
        (mv next-masks (svex-alist-fix loop-updates)))
       ((unless (eq status t))
        (cw "Monotonicity violation: ~x0~%" status)
        (mv next-masks (svex-alist-fix loop-updates)))
       ((mv final-masks rest-composed)
        (svex-alist-maskcompose-iter-simple
         next-masks loop-updates))
       (composed (svex-maskcompose-step-alist loop-updates masks next-masks rest-composed)))
    (mv final-masks composed))
  ///
  (defret netcomp-p-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys loop-updates))
             (netcomp-p new-updates loop-updates)))

  (local (defcong svex-alist-eval-equiv set-equiv (svex-alist-keys x) 1
           :hints(("Goal" :in-theory (enable set-equiv)))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys new-updates)
           (svex-alist-keys loop-updates)))

  ;; (local (defthm lemma.1
  ;;          (IMPLIES
  ;;           (AND
  ;;            (SVEX-ENVS-AGREE-ON-MASKS (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
  ;;                                      (APPEND (SVEX-ALIST-EVAL RES ENV1) ENV1)
  ;;                                      (APPEND (SVEX-ALIST-EVAL RES ENV2)
  ;;                                              ENV2))
  ;;            (SUBSETP-EQUAL (SVEX-ALIST-KEYS RES)
  ;;                           (SVEX-ALIST-KEYS LOOP-UPDATES))
  ;;            (NOT (SVEX-LOOKUP VAR LOOP-UPDATES)))
  ;;           (EQUAL (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
  ;;                             (SVEX-ENV-LOOKUP VAR ENV1))
  ;;                  (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
  ;;                             (SVEX-ENV-LOOKUP VAR ENV2))))
  ;;          :hints (("goal" :use ((:instance 


  (local (defthm svex-envs-agree-on-masks-of-append-when-reduce-similar
           (implies (and (svex-envs-agree-on-masks masks a b)
                         (set-equiv (alist-keys (svex-env-fix a))
                                    (alist-keys (svex-env-fix b)))
                         (svex-envs-similar (svex-env-removekeys
                                             (alist-keys (svex-env-fix a))
                                             c)
                                            (svex-env-removekeys
                                             (alist-keys (svex-env-fix a))
                                             d)))
                    (svex-envs-agree-on-masks masks (append a c)
                                              (append b d)))
           :hints ((and stable-under-simplificationp
                        `(:computed-hint-replacement
                          ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                             (and var
                                  `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
                          :expand (,(car (last clause)))
                          :do-not-induct t))
                   (and stable-under-simplificationp
                        '(:use ((:instance svex-envs-similar-necc
                                 (k var)
                                 (x (append (svarlist-x-env (alist-keys (svex-env-fix a))) c))
                                 (y (append (svarlist-x-env (alist-keys (svex-env-fix a))) d))))
                          :in-theory (e/d (member-alist-keys-iff-svex-env-boundp)
                                          (svex-envs-similar-necc
                                           svex-envs-similar-implies-equal-svex-env-lookup-2)))))))


  (local (defthm lemma-1
           (implies (and (svex-envs-agree-on-masks
                          (svex-assigns-propagate-masks masks updates)
                          (svex-alist-eval res env1)
                          (svex-alist-eval res env2))
                         (set-equiv (svex-alist-keys updates)
                                    (svex-alist-keys res))
                         (svex-envs-similar (svex-env-removekeys (svex-alist-keys updates) env1)
                                            (svex-env-removekeys (svex-alist-keys updates) env2)))
                    (equal (4vec-mask (svex-mask-lookup (svex-var var) masks)
                                      (svex-eval (svex-lookup var updates)
                                                 (append (svex-alist-eval res env1) env1)))
                           (4vec-mask (svex-mask-lookup (svex-var var) masks)
                                      (svex-eval (svex-lookup var updates)
                                                 (append (svex-alist-eval res env2) env2)))))
           :hints (("goal"
                    :use ((:instance svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                           (masks (svex-assigns-propagate-masks masks updates))
                           (x (svex-lookup var updates))
                           (env1 (append (svex-alist-eval res env1) env1))
                           (env2 (append (svex-alist-eval res env2) env2)))
                          (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                           (assigns updates)
                           (key var)
                           (m (svex-mask-lookup (svex-var var) masks))))
                    :in-theory (disable svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                                        mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks)))))

  (local (defthm lemma-2
           (IMPLIES
            (AND
             (SVEX-ENVS-AGREE-ON-MASKS masks2
                                       (SVEX-ALIST-EVAL RES ENV1)
                                       (SVEX-ALIST-EVAL RES ENV2))
             (booleanp (check-masks-decreasing loop-updates masks masks2))
             (NOT
              (MEMBER-EQUAL (SVAR-FIX VAR)
                            (SVEX-MASKCOMPOSE-DECREASING-VARS
                             LOOP-UPDATES MASKS masks2)))
             (svex-lookup var loop-updates))
            (EQUAL (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
                              (SVEX-EVAL (SVEX-LOOKUP VAR RES) ENV1))
                   (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
                              (SVEX-EVAL (SVEX-LOOKUP VAR RES)
                                         ENV2))))
           :hints (("goal" :use ((:instance svex-envs-agree-on-masks-necc
                                  (masks masks2)
                                  (env1 (svex-alist-eval res env1))
                                  (env2 (svex-alist-eval res env2)))
                                 (:instance mask-lookup-when-not-member-svex-maskcompose-decreasing-vars
                                  (new-masks masks2)
                                  (assigns loop-updates)
                                  (v var)))
                    :in-theory (disable svex-envs-agree-on-masks-necc
                                        mask-lookup-when-not-member-svex-maskcompose-decreasing-vars))
                   (and stable-under-simplificationp
                        '(:in-theory (enable 4vec-mask))))))
                                  

  (local (defthmd svex-alist-keys-is-alist-keys-of-svex-alist-fix
           (equal (svex-alist-keys x)
                  (alist-keys (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-fix alist-keys)))))

  ;; (local (defthmd svex-lookup-redef

  (local (defthmd svex-lookup-under-iff
           (iff (svex-lookup k a)
                (hons-assoc-equal (svar-fix k) (svex-alist-fix a)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (local (defthm svex-alist-keys-not-set-equiv-by-svex-lookup-1
           (implies (and (svex-lookup var a)
                         (not (svex-lookup var b)))
                    (not (set-equiv (svex-alist-keys a)
                                    (svex-alist-keys b))))
           :hints(("Goal" :in-theory (e/d (svex-lookup-under-iff
                                           svex-alist-keys-is-alist-keys-of-svex-alist-fix
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-alist-fix))))))

  (local (defthm lemma
           (let ((vars (svex-maskcompose-decreasing-vars loop-updates masks
                                                         (svex-assigns-propagate-masks masks loop-updates))))
             (implies (and (svex-envs-agree-on-masks
                            (svex-assigns-propagate-masks masks loop-updates)
                            (svex-alist-eval res env1)
                            (svex-alist-eval res env2))
                           (booleanp (check-masks-decreasing loop-updates masks
                                                         (svex-assigns-propagate-masks masks loop-updates)))
                           (set-equiv (svex-alist-keys loop-updates)
                                      (svex-alist-keys res))
                           (svex-envs-similar (svex-env-removekeys (svex-alist-keys loop-updates) env1)
                                              (svex-env-removekeys (svex-alist-keys loop-updates) env2))
                           ;; (set-equiv (svex-alist-keys res)
                           ;;            (svex-alist-keys loop-updates))
                           )
                      (svex-envs-agree-on-masks
                       masks
                       (append
                        (svex-env-reduce
                         vars
                         (svex-alist-eval loop-updates (append (svex-alist-eval res env1) env1)))
                        (svex-env-extract
                         (svex-alist-keys loop-updates)
                         (append (svex-alist-eval res env1) env1)))
                       (append
                        (svex-env-reduce
                         vars
                         (svex-alist-eval loop-updates (append (svex-alist-eval res env2) env2)))
                        (svex-env-extract
                         (svex-alist-keys loop-updates)
                         (append (svex-alist-eval res env2) env2))))))
           :hints ((and stable-under-simplificationp
                        `(:computed-hint-replacement
                          ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                             `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var))))))
                          :expand (,(car (last clause)))
                          :do-not-induct t))
                   ;; (and stable-under-simplificationp
                   ;;      '(:use ((:instance svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                   ;;               (masks (svex-assigns-propagate-masks masks loop-updates))
                   ;;               (x (svex-lookup var loop-updates))
                   ;;               (env1 (append (svex-alist-eval res env1) env1))
                   ;;               (env2 (append (svex-alist-eval res env2) env2)))
                   ;;              (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                   ;;               (assigns loop-updates)
                   ;;               (key var)
                   ;;               (m (svex-mask-lookup (svex-var var) masks))))
                   ;;        :in-theory (disable svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                   ;;                            mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks)))
                   )
           :otf-flg t))

  (defret final-masks-valid-of-<fn>
    (implies (and (svex-envs-agree-on-masks final-masks env1 env2)
                  (svex-envs-similar (svex-env-removekeys (svex-alist-keys loop-updates) env1)
                                     (svex-env-removekeys (svex-alist-keys loop-updates) env2))
                  (no-duplicatesp-equal (svex-alist-keys loop-updates)))
             (svex-envs-agree-on-masks
              masks
              (svex-alist-eval new-updates env1)
              (svex-alist-eval new-updates env2)))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 (b* (((mv ok1 final-masks) (acl2::find-match-list '(mv-nth '0 (svex-alist-maskcompose-iter-simple a b)) clause nil))
                      ((mv ok2 res) (acl2::find-match-list '(mv-nth '1 (svex-alist-maskcompose-iter-simple a b)) clause nil)))
                   (and ok1 ok2
                        `(:clause-processor
                          (acl2::generalize-with-alist-cp clause '((,final-masks . final-masks)
                                                                   (,res . res)))))))))

  (verify-guards svex-alist-maskcompose-iter-simple))



(define svex-alist-rewrite-under-masks ((x svex-alist-p)
                                        (masks svex-mask-alist-p)
                                        &key (verbosep 'nil))
  :returns (new-x svex-alist-p)
  (pairlis$ (svex-alist-keys x)
            (svexlist-rewrite-under-masks (svex-alist-vals x) masks :verbosep verbosep))
  ///

  (local (Defthm svex-eval-of-svex-lookup
           (equal (svex-eval (svex-lookup k x) env)
                  (svex-env-lookup k (svex-alist-eval x env)))))

  (local (in-theory (disable svex-env-lookup-of-svex-alist-eval)))

  (local (defthm nth-of-4veclist-mask
           (implies (and (< (nfix n) (len 4veclist)))
                    (equal (nth n (4veclist-mask masklist 4veclist))
                           (4vec-mask (nth n masklist) (nth n 4veclist))))
           :hints(("Goal" :in-theory (enable 4veclist-mask nth)))))


  (local (defthm nth-of-svex-argmasks-lookup
           (implies (< (nfix n) (len x))
                    (equal (nth n (svex-argmasks-lookup x masks))
                           (svex-mask-lookup (nth n x) masks)))
           :hints(("Goal" :in-theory (enable svex-argmasks-lookup nth)))))


  (local (defthm nth-of-svexlist-eval
           (implies (< (nfix n) (len x))
                    (equal (nth n (svexlist-eval x env))
                           (svex-eval (nth n x) env)))
           :hints(("Goal" :in-theory (enable svexlist-eval nth)))))

  (local (defthm svexlist-rewrite-under-masks-nth-correct
           (implies (and (svex-mask-alist-complete masks)
                         (< (nfix n) (len x))
                         (svex-equiv nth (nth n x)))
                    (equal (4vec-mask (svex-mask-lookup nth masks)
                                      (svex-eval (nth n (svexlist-rewrite-under-masks
                                                         x masks :verbosep verbosep))
                                                 env))
                           (4vec-mask (svex-mask-lookup (nth n x) masks)
                                      (svex-eval (nth n x) env))))
           :hints (("goal" :use ((:instance nth-of-4veclist-mask
                                  (masklist (svex-argmasks-lookup x masks))
                                  (4veclist (svexlist-eval (svexlist-rewrite-under-masks
                                                            x masks :Verbosep verbosep)
                                                           env))))
                    :in-theory (disable nth-of-4veclist-mask)
                    :do-not-induct t)
                   (and stable-under-simplificationp
                        '(:in-theory (enable nth-of-4veclist-mask))))))


  (local (include-book "std/lists/index-of" :dir :system))

  (local (defthm svex-env-lookup-of-pairlis$
           (implies (and (svarlist-p keys)
                         (member-equal (svar-fix var) keys))
                    (equal (svex-env-lookup var (pairlis$ keys vals))
                           (4vec-fix (nth (acl2::index-of (svar-fix var) keys)
                                          vals))))
           :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-fix index-of)))))

  (local (defthm svex-alist-eval-of-pairlis$
           (implies (and (svarlist-p keys)
                         (<= (len keys) (len vals)))
                    (equal (svex-alist-eval (pairlis$ keys vals) env)
                           (pairlis$ keys (svexlist-eval vals env))))
           :hints(("Goal" :in-theory (enable svex-alist-eval svexlist-eval)))))


  (local (defthm nth-index-of-svex-alist
           (implies (svex-lookup var x)
                    (equal (nth (index-of (svar-fix var)
                                          (svex-alist-keys x))
                                (svex-alist-vals x))
                           (svex-lookup var x)))
           :hints(("Goal" :in-theory (enable svex-lookup svex-alist-keys svex-alist-vals index-of nth)))))

  (defret lookup-of-<fn>
    (implies (and (svex-mask-alist-complete masks)
                  (svex-lookup var x))
             (let ((orig  (svex-lookup var x)))
               (equal (4vec-mask (svex-mask-lookup orig masks)
                                 (svex-eval (svex-lookup var new-x) env))
                      (4vec-mask (svex-mask-lookup orig masks)
                                 (svex-eval orig env))))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys new-x) (svex-alist-keys x)))

  (defret svex-lookup-under-iff-of-<fn>
    (iff (svex-lookup var new-x)
         (svex-lookup var x))))


(defsection svex-alist-keys-equiv
  (def-universal-equiv svex-alist-keys-equiv
    :qvars ()
    :equiv-terms ((set-equiv (svex-alist-keys x))))

  (local (defthmd svex-lookup-under-iff
           (iff (svex-lookup k a)
                (hons-assoc-equal (svar-fix k) (svex-alist-fix a)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (local (defthmd svex-alist-keys-is-alist-keys-of-svex-alist-fix
           (equal (svex-alist-keys x)
                  (alist-keys (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-fix alist-keys)))))

  (local (defthmd hons-assoc-equal-iff-member-alist-keys
           (iff (hons-assoc-equal k a)
                (member-equal k (alist-keys a)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-alist-keys-not-set-equiv-by-svex-lookup-1
           (implies (and (svex-lookup var a)
                         (not (svex-lookup var b)))
                    (not (set-equiv (svex-alist-keys a)
                                    (svex-alist-keys b))))
           :hints(("Goal" :in-theory (e/d (svex-lookup-under-iff
                                           svex-alist-keys-is-alist-keys-of-svex-alist-fix
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-alist-fix))))))

  (local (defthm svex-alist-keys-not-set-equiv-by-svex-lookup-2
           (implies (and (svex-lookup var b)
                         (not (svex-lookup var a)))
                    (not (set-equiv (svex-alist-keys a)
                                    (svex-alist-keys b))))
           :hints(("Goal" :in-theory (e/d (svex-lookup-under-iff
                                           svex-alist-keys-is-alist-keys-of-svex-alist-fix
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-alist-fix))))))

  (defcong svex-alist-keys-equiv iff (svex-lookup var x) 2
    :hints(("Goal" :in-theory (enable svex-alist-keys-equiv))))

  (defthm equal-svex-alist-keys-forward-to-svex-alist-keys-equiv
    (implies (equal (svex-alist-keys x) (svex-alist-keys y))
             (svex-alist-keys-equiv x y))
    :hints(("Goal" :in-theory (enable svex-alist-keys-equiv)))
    :rule-classes :forward-chaining)

  ;; (defthmd svex-alist-keys-equiv-iff-svex-alist-keys-set-equiv
  ;;   (iff (svex-alist-keys-equiv x y)
  ;;        (set-equiv (svex-alist-keys x) (svex-alist-keys y))))
  )


(defsection svex-env-keys-equiv
  (def-universal-equiv svex-env-keys-equiv
    :qvars ()
    :equiv-terms ((set-equiv (alist-keys (svex-env-fix x)))))

  (local (defthmd svex-env-boundp-under-iff
           (iff (svex-env-boundp k a)
                (hons-assoc-equal (svar-fix k) (svex-env-fix a)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))


  (local (defthm svex-env-keys-not-set-equiv-by-svex-env-boundp-1
           (implies (and (svex-env-boundp var a)
                         (not (svex-env-boundp var b)))
                    (not (set-equiv (alist-keys (svex-env-fix a))
                                    (alist-keys (svex-env-fix b)))))
           :hints(("Goal" :in-theory (e/d (svex-env-boundp-under-iff
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-env-fix))))))

  (local (defthm svex-env-keys-not-set-equiv-by-svex-env-boundp-2
           (implies (and (svex-env-boundp var b)
                         (not (svex-env-boundp var a)))
                    (not (set-equiv (alist-keys (svex-env-fix a))
                                    (alist-keys (svex-env-fix b)))))
           :hints(("Goal" :in-theory (e/d (svex-env-boundp-under-iff
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-env-fix))))))

  (defcong svex-env-keys-equiv iff (svex-env-boundp var x) 2
    :hints(("Goal" :in-theory (enable svex-env-keys-equiv))))

  (defthm equal-svex-env-keys-forward-to-svex-env-keys-equiv
    (implies (equal (alist-keys (svex-env-fix x))
                    (alist-keys (svex-env-fix y)))
             (svex-env-keys-equiv x y))
    :hints(("Goal" :in-theory (enable svex-env-keys-equiv)))
    :rule-classes :forward-chaining)

  ;; (defthmd svex-alist-keys-equiv-iff-svex-alist-keys-set-equiv
  ;;   (iff (svex-alist-keys-equiv x y)
  ;;        (set-equiv (svex-alist-keys x) (svex-alist-keys y))))
  )

(local (defthm svex-compose-rw-under-svex-eval-equiv
         (svex-eval-equiv (svex-compose-rw x substconf)
                          (svex-compose x (svex-substconfig->alist substconf)))
         :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

(local
 (define svex-pair-eval-equiv (x y)
   :verify-guards nil
   (and (iff (consp x) (consp y))
        (implies (consp x)
                 (and (equal (car x) (car y))
                      (svex-eval-equiv (cdr x) (cdr y)))))
   ///
   (defequiv svex-pair-eval-equiv)
   (defcong svex-pair-eval-equiv svex-alist-eval-equiv (cons pair rest) 1
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                       svex-lookup))))

   (defcong svex-eval-equiv svex-pair-eval-equiv (cons key val) 2)))

(define svex-maskcompose-step-alist-rw ((assigns svex-alist-p)
                                        (masks svex-mask-alist-p)
                                        (new-masks svex-mask-alist-p)
                                        (substconf svex-substconfig-p))
  :returns (new-composed svex-alist-p)
  ;; t for decreasing
  ;; nil for nonincreasing
  ;; svar key for increasing
  :guard-hints (("goal" :in-theory (enable svex-compose-lookup)))
  (b* (((when (atom assigns)) nil)
       ((unless (mbt (and (consp (car assigns))
                          (svar-p (caar assigns)))))
        (svex-maskcompose-step-alist-rw (cdr assigns) masks new-masks substconf))
       (key (caar assigns))
       (svex-key (svex-var key))
       (mask1 (svex-mask-lookup svex-key masks))
       (mask2 (svex-mask-lookup svex-key new-masks))
       ((when (sparseint-equal mask1 mask2))
        ;; nonincreasing
        (b* ((rest (svex-maskcompose-step-alist-rw (cdr assigns) masks new-masks substconf)))
          (cons (cons key (mbe :logic (svex-compose-lookup key (svex-substconfig->alist substconf))
                               :exec (or (svex-fastlookup key (svex-substconfig->alist substconf)) svex-key)))
                rest)))
       ;; otherwise decreasing, as long as rest is nonincreasing
       (rest (svex-maskcompose-step-alist-rw (cdr assigns) masks new-masks substconf)))
    (cons (cons key (svex-compose-rw (cdar assigns) substconf)) rest))
  ///
  

  (defret svex-maskcompose-step-alist-rw-is-svex-maskcompose-step-alist
    (svex-alist-eval-equiv new-composed
                           (svex-maskcompose-step-alist assigns masks new-masks
                                                        (svex-substconfig->alist substconf)))
    :hints(("Goal" :in-theory (enable svex-maskcompose-step-alist))))

  (defret alist-keys-of-<fn>
    (equal (svex-alist-keys new-composed)
           (svex-alist-keys assigns))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (local (in-theory (enable svex-alist-fix))))


(define svex-alist-maskcompose-iter
  ((masks svex-mask-alist-p "Masks -- initially all -1")
   (loop-updates svex-alist-p ;; original dfs-composed assignments
                 "Subset of update including only the bindings of the variables
                  that also appear as inputs.")
   (simpconf svex-simpconfig-p))
  :prepwork ((local (defthm svarlist-p-of-instersection
                      (implies (svarlist-p a)
                               (svarlist-p (intersection-equal a b)))
                      :hints(("Goal" :in-theory (enable svarlist-p)))))
             (local (include-book "std/lists/take" :dir :system))
             (local (defthm svarlist-p-of-take
                      (implies (and (svarlist-p x)
                                    (<= (nfix n) (len x)))
                               (svarlist-p (take n x)))
                      :hints(("Goal" :in-theory (enable svarlist-p))))))
  :ruler-extenders :lambdas
  :hints(("Goal" :in-theory (enable o<)))
  :verify-guards nil
  :measure (svex-mask-alist-measure (svex-alist-keys loop-updates) masks)
  :returns (mv (final-masks svex-mask-alist-p)
               (new-updates svex-alist-p))

  :well-founded-relation acl2::nat-list-<
  (b* ((next-masks (svex-assigns-propagate-masks masks loop-updates))
       (status (check-masks-decreasing loop-updates masks next-masks))
       ((unless status)
        (cw "Masks stopped shrinking~%")
        (mv next-masks (svex-alist-fix loop-updates)))
       ((unless (eq status t))
        (cw "Monotonicity violation: ~x0~%" status)
        (mv next-masks (svex-alist-fix loop-updates)))
       ((mv final-masks rest-composed)
        (svex-alist-maskcompose-iter
         next-masks loop-updates simpconf))
       (composed (svex-maskcompose-step-alist-rw
                  (svex-alist-rewrite-under-masks loop-updates next-masks)
                  masks next-masks
                  (make-svex-substconfig :simp simpconf
                                         :alist rest-composed))))
    (mv final-masks composed))
  ///

  (defret final-masks-of-<fn>
    (b* (((mv ?simp-final-masks ?simp-new-updates)
           (svex-alist-maskcompose-iter-simple masks loop-updates)))
      (equal final-masks simp-final-masks))
    :hints(("Goal" :in-theory (disable (:d <fn>))
            :induct <call>
            :expand (<call>
                     (svex-alist-maskcompose-iter-simple masks loop-updates)))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys new-updates)
           (svex-alist-keys loop-updates)))

  (local (defun smdvwsake-ind (a b)
           (declare (xargs :measure (+ (len a) (len b))
                           :ruler-extenders :all))
           (b* (((when (and (atom a) (atom b))) (list a b))
                ((when (atom a))
                 (smdvwsake-ind a (cdr b)))
                ((when (atom b))
                 (smdvwsake-ind (cdr a) b))
                ((mv next-a next-b)
                 (if (and (consp (car a))
                          (svar-p (caar a)))
                     (if (and (consp (car b))
                              (svar-p (caar b)))
                         (mv (cdr a) (cdr b))
                       (mv a (cdr b)))
                   (if (and (consp (car b))
                              (svar-p (caar b)))
                       (mv (cdr a) b)
                     (mv (cdr a) (cdr b))))))
             (smdvwsake-ind next-a next-b))))

  (local (defthmd svex-maskcompose-decreasing-vars-when-svex-alist-keys-equal
           (implies (equal (svex-alist-keys a) (svex-alist-keys b))
                    (equal (equal (svex-maskcompose-decreasing-vars a masks new-masks)
                                  (svex-maskcompose-decreasing-vars b masks new-masks))
                           t))
           :hints(("Goal" :in-theory (enable svex-maskcompose-decreasing-vars
                                             svex-alist-keys)
                   :induct (smdvwsake-ind a b)
                   :expand ((svex-maskcompose-decreasing-vars a masks new-masks)
                            (svex-maskcompose-decreasing-vars b masks new-masks))))))

  (local (defthm svex-maskcompose-decreasing-vars-of-svex-alist-rewrite-under-masks
           (equal (svex-maskcompose-decreasing-vars (svex-alist-rewrite-under-masks a m :verbosep verb)
                                                    masks masks2)
                  (svex-maskcompose-decreasing-vars a masks masks2))
           :hints(("Goal" :in-theory (enable svex-maskcompose-decreasing-vars-when-svex-alist-keys-equal)))))

  (local (defthm svex-envs-agree-on-masks-of-append-same
           (implies (and (svex-envs-agree-on-masks masks a b)
                         (set-equiv (alist-keys (svex-env-fix a))
                                    (alist-keys (svex-env-fix b))))
                    (svex-envs-agree-on-masks masks (append a c)
                                              (append b c)))
           :hints ((and stable-under-simplificationp
                        `(:computed-hint-replacement
                          ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                             (and var
                                  `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
                          :expand (,(car (last clause)))
                          :do-not-induct t))
                   ;; (and stable-under-simplificationp
                   ;;      '(:use ((:instance svex-envs-similar-necc
                   ;;               (k var)
                   ;;               (x (append (svarlist-x-env (alist-keys (svex-env-fix a))) c))
                   ;;               (y (append (svarlist-x-env (alist-keys (svex-env-fix a))) d))))
                   ;;        :in-theory (e/d (member-alist-keys-iff-svex-env-boundp)
                   ;;                        (svex-envs-similar-necc
                   ;;                         svex-envs-similar-implies-equal-svex-env-lookup-2))))
                   )))


  (local (defthm lemma-1
           (IMPLIES
            (AND
             (EQUAL
              (CHECK-MASKS-DECREASING LOOP-UPDATES MASKS
                                      (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))
              T)
             (SVEX-ENVS-AGREE-ON-MASKS (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
                                       (SVEX-ALIST-EVAL NEW-UPDATES ENV)
                                       (SVEX-ALIST-EVAL SIMP-NEW-UPDATES ENV))
             (EQUAL (SVEX-ALIST-KEYS NEW-UPDATES)
                    (SVEX-ALIST-KEYS LOOP-UPDATES))
             (EQUAL (SVEX-ALIST-KEYS SIMP-NEW-UPDATES)
                    (SVEX-ALIST-KEYS LOOP-UPDATES))
             (NO-DUPLICATESP-EQUAL (SVEX-ALIST-KEYS LOOP-UPDATES))
             (MEMBER-EQUAL (SVAR-FIX VAR)
                           (SVEX-MASKCOMPOSE-DECREASING-VARS
                            LOOP-UPDATES MASKS
                            (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)))
             (SVEX-LOOKUP VAR LOOP-UPDATES))
            (EQUAL
             (4VEC-MASK
              (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
              (SVEX-EVAL
               (SVEX-LOOKUP VAR
                            (SVEX-ALIST-REWRITE-UNDER-MASKS
                             LOOP-UPDATES
                             (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
                             :VERBOSEP NIL))
               (APPEND (SVEX-ALIST-EVAL NEW-UPDATES ENV)
                       ENV)))
             (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
                        (SVEX-EVAL (SVEX-LOOKUP VAR LOOP-UPDATES)
                                   (APPEND (SVEX-ALIST-EVAL SIMP-NEW-UPDATES ENV)
                                           ENV)))))
           :hints (("goal" :use ((:instance lookup-of-svex-alist-rewrite-under-masks
                                  (x loop-updates)
                                  (masks (svex-assigns-propagate-masks masks loop-updates))
                                  (verbosep nil)
                                  (env (append (svex-alist-eval new-updates env) env)))
                                 (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                                  (key var) (assigns loop-updates)
                                  (m (svex-mask-lookup (svex-var var) masks)))
                                 (:instance svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                                  (masks (svex-assigns-propagate-masks masks loop-updates))
                                  (env1 (append (svex-alist-eval new-updates env) env))
                                  (env2 (append (svex-alist-eval simp-new-updates env) env))
                                  (x (svex-lookup var loop-updates))))
                    :in-theory (disable lookup-of-svex-alist-rewrite-under-masks
                                        mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                                        svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete)))))
                                  


  ;; very similar to lemma-2 above
  (local (defthm lemma-2
           (IMPLIES
            (AND
             (SVEX-ENVS-AGREE-ON-MASKS masks2
                                       (SVEX-ALIST-EVAL new-updates env)
                                       (SVEX-ALIST-EVAL simp-new-updates ENV))
             (booleanp (check-masks-decreasing loop-updates masks masks2))
             (NOT
              (MEMBER-EQUAL (SVAR-FIX VAR)
                            (SVEX-MASKCOMPOSE-DECREASING-VARS
                             LOOP-UPDATES MASKS masks2)))
             (svex-lookup var loop-updates))
            (EQUAL (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
                              (SVEX-EVAL (SVEX-LOOKUP VAR new-updates) ENV))
                   (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
                              (SVEX-EVAL (SVEX-LOOKUP VAR simp-new-updates)
                                         ENV))))
           :hints (("goal" :use ((:instance svex-envs-agree-on-masks-necc
                                  (masks masks2)
                                  (env1 (svex-alist-eval new-updates env))
                                  (env2 (svex-alist-eval simp-new-updates env)))
                                 (:instance mask-lookup-when-not-member-svex-maskcompose-decreasing-vars
                                  (new-masks masks2)
                                  (assigns loop-updates)
                                  (v var)))
                    :in-theory (disable svex-envs-agree-on-masks-necc
                                        mask-lookup-when-not-member-svex-maskcompose-decreasing-vars))
                   (and stable-under-simplificationp
                        '(:in-theory (enable 4vec-mask))))))

  (local
   (defthm lemma
     (IMPLIES
      (AND
       (EQUAL
        (CHECK-MASKS-DECREASING LOOP-UPDATES MASKS
                                (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))
        T)
       (SVEX-ENVS-AGREE-ON-MASKS (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
                                 (SVEX-ALIST-EVAL NEW-UPDATES ENV)
                                 (SVEX-ALIST-EVAL SIMP-NEW-UPDATES ENV))
       (equal (svex-alist-keys new-updates)
              (svex-alist-keys loop-updates))
       (equal (svex-alist-keys simp-new-updates)
              (svex-alist-keys loop-updates))
       (NO-DUPLICATESP-EQUAL (SVEX-ALIST-KEYS LOOP-UPDATES)))
      (SVEX-ENVS-AGREE-ON-MASKS
       MASKS
       (APPEND
        (SVEX-ENV-REDUCE
         (SVEX-MASKCOMPOSE-DECREASING-VARS
          LOOP-UPDATES MASKS
          (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))
         (SVEX-ALIST-EVAL (SVEX-ALIST-REWRITE-UNDER-MASKS
                           LOOP-UPDATES
                           (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
                           :VERBOSEP NIL)
                          (APPEND (SVEX-ALIST-EVAL NEW-UPDATES ENV)
                                  ENV)))
        (SVEX-ENV-EXTRACT (SVEX-ALIST-KEYS LOOP-UPDATES)
                          (APPEND (SVEX-ALIST-EVAL NEW-UPDATES ENV)
                                  ENV)))
       (APPEND
        (SVEX-ENV-REDUCE
         (SVEX-MASKCOMPOSE-DECREASING-VARS
          LOOP-UPDATES MASKS
          (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))
         (SVEX-ALIST-EVAL LOOP-UPDATES
                          (APPEND (SVEX-ALIST-EVAL SIMP-NEW-UPDATES ENV)
                                  ENV)))
        (SVEX-ENV-EXTRACT (SVEX-ALIST-KEYS LOOP-UPDATES)
                          (APPEND (SVEX-ALIST-EVAL SIMP-NEW-UPDATES ENV)
                                  ENV)))))
     :hints ((and stable-under-simplificationp
                  `(:computed-hint-replacement
                    ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                       `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var))))))
                    :expand (,(car (last clause)))
                    :do-not-induct t)))
     :otf-flg t))


  (defret composed-results-of-<fn>-correct
    (b* (((mv ?simp-final-masks ?simp-new-updates)
          (svex-alist-maskcompose-iter-simple masks loop-updates)))
      (implies (no-duplicatesp-equal (svex-alist-keys loop-updates))
               (svex-envs-agree-on-masks masks
                                         (svex-alist-eval new-updates env)
                                         (svex-alist-eval simp-new-updates env))))
    :hints(("Goal" :in-theory (disable (:d <fn>))
            :induct <call>
            :expand (<call>
                     (svex-alist-maskcompose-iter-simple masks loop-updates)))
           
            (and stable-under-simplificationp
                 (b* (((mv ?ok1 new-updates) (acl2::find-match-list '(mv-nth '1 (svex-alist-maskcompose-iter a b)) clause nil))
                      ((mv ?ok2 simp-new-updates) (acl2::find-match-list '(mv-nth '1 (svex-alist-maskcompose-iter-simple a b)) clause nil)))
                   (and ok1 ok2
                        `(:clause-processor
                          (acl2::generalize-with-alist-cp clause '((,new-updates . new-updates)
                                                                   (,simp-new-updates . simp-new-updates)))))))))

  (local (defthm member-svarlist->svexes
           (iff (member-equal (svex-var var) (svarlist->svexes vars))
                (member-equal (svar-fix var) (svarlist-fix vars)))
           :hints(("Goal" :in-theory (enable svarlist->svexes)))))

  ;; (local (defthmd svex-env-lookup-in-terms-of-svex-env-fix
  ;;          (equal (svex-env-lookup var env)
  ;;                 (4vec-fix (cdr (hons-assoc-equal (svar-fix var) (svex-env-fix env)))))
  ;;          :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  ;; (local (defthmd svex-env-lookup-when-not-member
  ;;          (implies (not (member-equal (svar-fix var) (alist-keys (svex-env-fix env))))
  ;;                   (equal (svex-env-lookup var env) (4vec-x)))
  ;;          :hints(("Goal" :in-theory (e/d (svex-env-lookup-in-terms-of-svex-env-fix
  ;;                                          hons-assoc-equal-iff-member-alist-keys)
  ;;                                         (hons-assoc-equal-of-svex-env-fix))
  ;;                  :cases ((hons-assoc-equal (svar-fix var) (svex-env-fix env)))))))

  ;; (local (defthmd svex-env-lookup-when-not-member
  ;;          (implies (not (member-equal (svar-fix var) (alist-keys (svex-env-fix env))))
  ;;                   (equal (svex-env-lookup var env) (4vec-x)))
  ;;          :hints(("Goal" :in-theory (e/d (svex-env-lookup-in-terms-of-svex-env-fix
  ;;                                          hons-assoc-equal-iff-member-alist-keys)
  ;;                                         (hons-assoc-equal-of-svex-env-fix))
  ;;                  :cases ((hons-assoc-equal (svar-fix var) (svex-env-fix env)))))))

  (local (defthmd svex-env-lookup-when-not-boundp
           (implies (not (svex-env-boundp var env))
                    (equal (svex-env-lookup var env) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup
                                             svex-env-boundp)))))


  (defthmd svex-envs-agree-on-masks-of-neg1s
    (implies (and (equal vars (alist-keys (svex-env-fix env1)))
                  (equal vars (alist-keys (svex-env-fix env2))))
             (iff (svex-envs-agree-on-masks (svexlist-mask-acons (svarlist->svexes vars) -1 nil) env1 env2)
                  (svex-envs-equivalent env1 env2)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable svex-envs-equivalent)))
            (and stable-under-simplificationp
                 (let ((var (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                   `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var))))))
            (and stable-under-simplificationp
                 '(:use ((:instance svex-envs-agree-on-masks-necc
                          (masks (svexlist-mask-acons (svarlist->svexes (alist-keys (svex-env-fix env1))) -1 nil))))
                   :in-theory (e/d (svex-env-lookup-when-not-boundp
                                    member-alist-keys-iff-svex-env-boundp)
                                   (svex-envs-agree-on-masks-necc))))))


  (local (defthm svex-envs-equivalent-by-agree-on-masks
           (implies (and (svex-envs-agree-on-masks (svexlist-mask-acons (svarlist->svexes (alist-keys (svex-env-fix env1)))
                                                                        -1 nil)
                                                   env1 env2)
                         (equal (alist-keys (svex-env-fix env1)) (alist-keys (svex-env-fix env2))))
                    (equal (svex-envs-equivalent env1 env2) t))
           :hints(("Goal" :in-theory (enable svex-envs-agree-on-masks-of-neg1s)))))

  (defret composed-results-of-<fn>-correct-top
    :pre-bind ((masks (svexlist-mask-acons (svarlist->svexes (svex-alist-keys loop-updates)) -1 nil)))
    (b* (((mv ?simp-final-masks ?simp-new-updates)
          (svex-alist-maskcompose-iter-simple masks loop-updates)))
      (implies (no-duplicatesp-equal (svex-alist-keys loop-updates))
               (svex-alist-eval-equiv new-updates simp-new-updates)))
    :hints (("goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))
            (and stable-under-simplificationp
                 (let ((env (acl2::find-call-lst 'svex-alist-eval-equiv-envs-equivalent-witness clause)))
                   `(:clause-processor (acl2::generalize-with-alist-cp clause '((,env . env))))))))

  (defret netcomp-p-of-<fn>
    :pre-bind ((masks (svexlist-mask-acons (svarlist->svexes (svex-alist-keys loop-updates)) -1 nil)))
    (implies (no-duplicatesp-equal (svex-alist-keys loop-updates))
             (netcomp-p new-updates loop-updates)))

  (verify-guards svex-alist-maskcompose-iter))
