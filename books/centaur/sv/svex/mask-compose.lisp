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
                (not (4vmask-equal x y))
                (<= 0 (sparseint-val (4vmask-fix y))))
           (< (logcount (sparseint-val (4vmask-fix x)))
              (logcount (sparseint-val (4vmask-fix y)))))
  :hints(("Goal" :in-theory (enable 4vmask-subsumes
                                    logcount-less-when-logandc1-0-and-unequal)))
  :rule-classes :linear)

(defthm sparseint-bitcount-decr-when-4vmask-subsumes-no-fix
  (implies (and (4vmask-subsumes y x)
                (4vmask-p x) (4vmask-p y)
                (not (4vmask-equal x y))
                (<= 0 (sparseint-val y)))
           (< (logcount (sparseint-val x))
              (logcount (sparseint-val y))))
  :hints(("Goal" :in-theory (enable 4vmask-subsumes
                                    logcount-less-when-logandc1-0-and-unequal)))
  :rule-classes :linear)


(local (defthmd svex-lookup-redef
         (equal (svex-lookup key alist)
                (cond ((atom alist) nil)
                      ((and (consp (car alist))
                            (equal (caar alist) (svar-fix key)))
                       (svex-fix (cdar alist)))
                      (t (svex-lookup key (cdr alist)))))
         :hints(("Goal" :in-theory (enable svex-lookup)))
         :rule-classes :definition))


(define check-masks-decreasing ((vars svarlist-p)
                                (masks svex-mask-alist-p)
                                (new-masks svex-mask-alist-p))
  :returns (status)
  ;; t for decreasing
  ;; nil for nonincreasing
  ;; svar key for increasing
  (b* (((when (atom vars)) nil)
       (key (svar-fix (car vars)))
       (svex-key (svex-var key))
       (mask1 (svex-mask-lookup svex-key masks))
       (mask2 (svex-mask-lookup svex-key new-masks))
       ((unless (4vmask-subsumes mask1 mask2))
        ;; violation
        key)
       ((when (or (sparseint-equal mask1 mask2)
                  (sparseint-< mask2 0)))
        ;; nonincreasing
        (check-masks-decreasing (cdr vars) masks new-masks))
       ;; otherwise decreasing, as long as rest is nonincreasing
       (rest (check-masks-decreasing (cdr vars) masks new-masks)))
    (or rest t))
  ///
  (local (defthm 4vmask-subsumes-false-by-sign
           (implies (and (<= 0 (sparseint-val (4vmask-fix x)))
                         (< (sparseint-val (4vmask-fix y)) 0))
                    (not (4vmask-subsumes x y)))
           :hints(("Goal" :in-theory (enable 4vmask-subsumes)) )))

  (defret svex-mask-alist-measure-decreasing-by-<fn>
    (let* ((new-meas (svex-mask-alist-measure vars new-masks))
           (old-meas (svex-mask-alist-measure vars masks)))
      (and (implies (not status)
                    (equal new-meas old-meas))
           (implies (equal status t)
                    (acl2::nat-list-< new-meas old-meas))))
    :hints(("Goal" :in-theory (enable svex-mask-alist-measure
                                      svex-mask-alist-negcount
                                      svex-mask-alist-nonnegcount))))

  (defretd 4vmask-subsumes-by-<fn>
    (implies (and (booleanp status)
                  (member-equal (svar-fix var) (svarlist-fix vars)))
             (4vmask-subsumes (svex-mask-lookup (svex-var var) masks)
                              (svex-mask-lookup (svex-var var) new-masks)))
    :hints(("Goal" :in-theory (enable svex-lookup-redef))))

  (local (in-theory (enable svex-alist-fix))))


(defstobj maskcompose-stats
  (maskcompose-status)
  (maskcompose-neg-varcount :type (integer 0 *) :initially 0)
  (maskcompose-nonneg-bitcount :type (integer 0 *) :initially 0)
  (maskcompose-nonneg-varcount :type (integer 0 *) :initially 0)
  (maskcompose-neg-decr-varcount :type (integer 0 *) :initially 0)
  (maskcompose-nonneg-decr-varcount :type (integer 0 *) :initially 0))

(local (in-theory (disable nth update-nth)))

(define update-maskcompose-stats ((key svar-p)
                                  (mask1 4vmask-p)
                                  (mask2 4vmask-p)
                                  (maskcompose-stats))
  :returns (mv violationp
               (new-maskcompose-stats))
  (b* ((mask1 (4vmask-fix mask1))
       (mask2 (4vmask-fix mask2))
       ((unless (4vmask-subsumes mask1 mask2))
        (b* ((maskcompose-stats (update-maskcompose-status (svar-fix key) maskcompose-stats)))
          (mv t maskcompose-stats)))
       (negp (sparseint-< mask2 0))
       (zerop (sparseint-equal mask2 0))
       (maskcompose-stats (if negp
                              (update-maskcompose-neg-varcount
                               (+ 1 (maskcompose-neg-varcount maskcompose-stats))
                               maskcompose-stats)
                            (b* ((maskcompose-stats
                                  (if zerop
                                      maskcompose-stats
                                    (update-maskcompose-nonneg-varcount
                                     (+ 1 (maskcompose-nonneg-varcount maskcompose-stats))
                                     maskcompose-stats))))
                              (update-maskcompose-nonneg-bitcount
                               (+ (sparseint-bitcount mask2)
                                  (maskcompose-nonneg-bitcount maskcompose-stats))
                               maskcompose-stats))))
       (equal (sparseint-equal mask1 mask2))
       (maskcompose-stats (if equal
                              maskcompose-stats
                            (if negp
                                (update-maskcompose-neg-decr-varcount
                                 (+ 1 (maskcompose-neg-decr-varcount maskcompose-stats))
                                 maskcompose-stats)
                              (update-maskcompose-nonneg-decr-varcount
                               (+ 1 (maskcompose-nonneg-decr-varcount maskcompose-stats))
                               maskcompose-stats))))
       (maskcompose-stats (if (or negp equal)
                              maskcompose-stats
                            (update-maskcompose-status t maskcompose-stats))))
    (mv nil maskcompose-stats))
  ///
  (defret violationp-of-<fn>
    (iff violationp
         (not (4vmask-subsumes mask1 mask2))))

  (defret maskcompose-status-of-<fn>
    (equal (nth *maskcompose-status* new-maskcompose-stats)
           (cond ((not (4vmask-subsumes mask1 mask2))
                  (svar-fix key))
                 ((or (4vmask-equal mask1 mask2)
                      (sparseint-< (4vmask-fix mask2) 0))
                  (maskcompose-status maskcompose-stats))
                 (t t)))))

(define check-masks-stats-aux ((assigns svex-alist-p)
                               (masks svex-mask-alist-p)
                               (new-masks svex-mask-alist-p)
                               maskcompose-stats)
  :returns new-maskcompose-stats
  ;; t for decreasing
  ;; nil for nonincreasing
  ;; svar key for increasing
  (b* (((when (atom assigns)) maskcompose-stats)
       ((unless (mbt (and (consp (car assigns))
                          (svar-p (caar assigns)))))
        (check-masks-stats-aux (cdr assigns) masks new-masks maskcompose-stats))
       (key (caar assigns))
       (svex-key (svex-var key))
       (mask1 (svex-mask-lookup svex-key masks))
       (mask2 (svex-mask-lookup svex-key new-masks))
       ((mv violationp maskcompose-stats)
        (update-maskcompose-stats key mask1 mask2 maskcompose-stats))
       ((when violationp)
        maskcompose-stats))
    (check-masks-stats-aux (cdr assigns) masks new-masks maskcompose-stats))
  ///
  (defret status-of-<fn>
    (implies (booleanp (maskcompose-status maskcompose-stats))
             (equal (nth *maskcompose-status* new-maskcompose-stats)
                    (let ((spec (check-masks-decreasing (svex-alist-keys assigns) masks new-masks)))
                      (or spec (maskcompose-status maskcompose-stats)))))
    :hints(("Goal" :in-theory (enable svex-alist-keys
                                      check-masks-decreasing))))

  (local (in-theory (enable svex-alist-fix))))

(define check-masks-stats ((assigns svex-alist-p)
                           (masks svex-mask-alist-p)
                           (new-masks svex-mask-alist-p)
                           ;; verboseness?
                           )
  :returns (status
            (equal status (check-masks-decreasing (svex-alist-keys assigns) masks new-masks)))
  (b* (((acl2::local-stobjs maskcompose-stats)
        (mv status maskcompose-stats))
       (maskcompose-stats (check-masks-stats-aux assigns masks new-masks maskcompose-stats))
       (status (maskcompose-status maskcompose-stats)))
    (cw "Mask bits: ~x0  Nonneg-mask vars: ~x1  Neg-mask vars: ~x2  Decr nonneg: ~x3  Decr neg: ~x4~%" 
        (maskcompose-nonneg-bitcount maskcompose-stats)
        (maskcompose-nonneg-varcount maskcompose-stats)
        (maskcompose-neg-varcount maskcompose-stats)
        (maskcompose-nonneg-decr-varcount maskcompose-stats)
        (maskcompose-neg-decr-varcount maskcompose-stats))
    (mv status maskcompose-stats)))

                           


(define svex-maskcompose-decreasing-vars ((vars svarlist-p)
                                (masks svex-mask-alist-p)
                                (new-masks svex-mask-alist-p))
  :returns (decr svarlist-p)
  (b* (((when (atom vars)) nil)
       (key (svar-fix (car vars)))
       (svex-key (svex-var key))
       (mask1 (svex-mask-lookup svex-key masks))
       (mask2 (svex-mask-lookup svex-key new-masks))
       ;; ((unless (4vmask-subsumes mask1 mask2))
       ;;  ;; violation
       ;;  key)
       ((when (sparseint-equal mask1 mask2))
        ;; nonincreasing
        (svex-maskcompose-decreasing-vars (cdr vars) masks new-masks))
       ;; otherwise decreasing, as long as rest is nonincreasing
       (rest (svex-maskcompose-decreasing-vars (cdr vars) masks new-masks)))
    (cons key rest))
  ///
  (defret <fn>-subsetp-of-svex-alist-keys
    (subsetp-equal decr (svarlist-fix vars))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defretd mask-lookup-when-not-member-<fn>
    :pre-bind ((vars (svex-alist-keys assigns)))
    (implies (and (booleanp (check-masks-decreasing (svex-alist-keys assigns) masks new-masks))
                  (not (member-equal (svar-fix v) decr))
                  (member-equal (svar-fix v) (svarlist-fix vars)))
             (4vmask-equal (svex-mask-lookup (svex-var v) new-masks)
                           (svex-mask-lookup (svex-var v) masks)))
    :hints(("Goal" :in-theory (enable check-masks-decreasing
                                      svex-lookup-redef
                                      svex-alist-keys))))

  (defret subsetp-<fn>
    (subsetp-equal decr (svarlist-fix vars)))

  (defret subsetp-<fn>-no-fix
    (implies (svarlist-p vars)
             (subsetp-equal decr vars)))

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
                                       (svex-maskcompose-decreasing-vars (svex-alist-keys x) masks new-masks))))
           :hints(("Goal" :in-theory (enable svex-maskcompose-decreasing-vars
                                             svex-lookup member-equal
                                             svex-alist-keys)))))
                         
  (defret <fn>-correct
    (implies (no-duplicatesp-equal (svex-alist-keys assigns))
             (svex-alist-eval-equiv new-composed
                                    (svex-alist-compose
                                     (append (svex-alist-reduce
                                              (svex-maskcompose-decreasing-vars
                                               (svex-alist-keys assigns) masks new-masks)
                                              assigns)
                                             (svex-identity-subst (svex-alist-keys assigns)))
                                     composed)))
    :hints (("goal" :induct <call>
             :in-theory (e/d (svex-acons svex-compose-lookup)
                             ((:d <fn>)))
             :expand (<call>
                      (:free (a b) (svex-maskcompose-decreasing-vars (cons a b) masks new-masks))
                      (svex-maskcompose-decreasing-vars nil masks new-masks)
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
    (svex-mask-acons svex full-mask rest))
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
    :hints(("Goal" :in-theory (enable svex-envs-agree-on-masks))))

  ;; (defthm svex-envs-agree-on-masks-of-propagate-masks
  ;;   (implies (and (svex-envs-agree-on-masks (svex-assigns-propagate-masks masks updates)
  ;;                                           a b)
  ;;                 (svex-lookup var updates)
  ;;                 (equal a-lookup (svex-env-lookup var a)))
  ;;            (equal (4vec-mask (svex-mask-lookup (svex-var var) masks)
  ;;                              a-lookup)
  ;;                   (4vec-mask (svex-mask-lookup (svex-var var) masks)
  ;;                              (svex-env-lookup var b))))
  ;;   :hints (("goal" :use ((:instance svex-envs-agree-on-masks-necc
  ;;                          (env1 a) (env2 b)
  ;;                          (masks (svex-assigns-propagate-masks masks updates)))
  ;;                         (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
  ;;                          (key var) (assigns updates)
  ;;                          (m (svex-mask-lookup (svex-var var) masks))))
  ;;            :in-theory (disable svex-envs-agree-on-masks-necc
  ;;                                mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks))))
  )
                    


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




;; (define svex-alist-clean ((x svex-alist-p))
;;   :prepwork ((local (defthm svex-alist-p-of-hons-remove-assoc
;;                       (implies (svex-alist-p x)
;;                                (svex-alist-p (acl2::hons-remove-assoc k x))))))
;;   :guard (no-duplicatesp-equal (svex-alist-keys x))
;;   :returns (new-x svex-alist-p)
;;   :verify-guards nil
;;   :inline t
;;   (mbe :logic
;;        (b* (((when (atom x)) nil)
;;             ((unless (mbt (and (consp (car x))
;;                                (svar-p (caar x)))))
;;              (svex-alist-clean (cdr x))))
;;          (cons (cons (caar x) (svex-fix (cdar x)))
;;                (acl2::hons-remove-assoc (caar x)
;;                                         (svex-alist-clean (cdr x)))))
;;        :exec x)
;;   ///
;;   (defret svex-lookup-of-<fn>
;;     (equal (svex-lookup k new-x)
;;            (svex-lookup k x))
;;     :hints(("Goal" :in-theory (enable svex-lookup-redef))))

;;   (local (defthm hons-remove-assoc-when-not-svex-lookup
;;            (implies (and (not (svex-lookup var x))
;;                          (svar-p var)
;;                          (svex-alist-p x))
;;                     (equal (acl2::hons-remove-assoc var x)
;;                            x))
;;            :hints(("Goal" :in-theory (enable svex-lookup-redef
;;                                              svex-alist-fix)))))

;;   (defret <fn>-when-no-duplicates
;;     (implies (no-duplicatesp-equal (svex-alist-keys x))
;;              (equal new-x (svex-alist-fix x)))
;;     :hints(("Goal" :in-theory (enable svex-alist-keys
;;                                       svex-alist-fix))))

;;   (verify-guards svex-alist-clean$inline
;;     :hints ((and stable-under-simplificationp
;;                  '(:expand ((svex-alist-keys x))))))

;;   (defret <fn>-under-svex-alist-equiv
;;     (svex-alist-eval-equiv new-x x)
;;     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))

;;   (local (defthm svex-alist-keys-of-hons-remove-assoc
;;            (implies (and (svex-alist-p x)
;;                          (svar-p var))
;;                     (equal (svex-alist-keys (acl2::hons-remove-assoc var x))
;;                            (remove-equal var (svex-alist-keys x))))
;;            :hints(("Goal" :in-theory (enable svex-alist-keys)))))

;;   (local (defthm no-dups-of-remove
;;            (implies (no-duplicatesp-equal x)
;;                     (no-duplicatesp-equal (remove-equal k x)))))

;;   (defret no-duplicate-keys-of-<fn>
;;     (no-duplicatesp-equal (svex-alist-keys new-x))
;;     :hints(("Goal" :in-theory (enable svex-alist-keys))))

;;   (local (in-theory (enable svex-alist-fix))))
            


;; (define svex-alist-maskcompose-iter-simple
;;   ((masks svex-mask-alist-p "Masks -- initially all -1")
;;    (loop-updates svex-alist-p ;; original dfs-composed assignments
;;                  "Subset of update including only the bindings of the variables
;;                   that also appear as inputs."))
;;   :prepwork ((local (defthm svarlist-p-of-instersection
;;                       (implies (svarlist-p a)
;;                                (svarlist-p (intersection-equal a b)))
;;                       :hints(("Goal" :in-theory (enable svarlist-p)))))
;;              (local (include-book "std/lists/take" :dir :system))
;;              (local (defthm svarlist-p-of-take
;;                       (implies (and (svarlist-p x)
;;                                     (<= (nfix n) (len x)))
;;                                (svarlist-p (take n x)))
;;                       :hints(("Goal" :in-theory (enable svarlist-p))))))
;;   :ruler-extenders :lambdas
;;   :hints(("Goal" :in-theory (enable o<)))
;;   :verify-guards nil
;;   :measure (svex-mask-alist-measure (svex-alist-keys (svex-alist-clean loop-updates)) masks)
;;   :returns ;; (mv (final-masks svex-mask-alist-p)
;;   (new-updates svex-alist-p)
;;   :guard (no-duplicatesp-equal (svex-alist-keys loop-updates))
;;   :well-founded-relation acl2::nat-list-<
;;   (b* ((loop-updates (svex-alist-clean loop-updates))
;;        (next-masks (svex-assigns-propagate-masks masks loop-updates))
;;        (status (check-masks-decreasing loop-updates masks next-masks))
;;        ((unless status)
;;         (cw "Masks stopped shrinking~%")
;;         ;; (mv next-masks (svex-alist-fix loop-updates))
;;         (svex-alist-fix loop-updates))
;;        ((unless (eq status t))
;;         (cw "Monotonicity violation: ~x0~%" status)
;;         (svex-alist-fix loop-updates);; (mv next-masks (svex-alist-fix loop-updates))
;;         )
;;        (rest-composed ;; (mv final-masks rest-composed)
;;         (svex-alist-maskcompose-iter-simple
;;          next-masks loop-updates))
;;        (composed (svex-maskcompose-step-alist loop-updates masks next-masks rest-composed)))
;;     ;; (mv final-masks composed)
;;     composed)
;;   ///
;;   (defret netcomp-p-of-<fn>
;;     (implies (no-duplicatesp-equal (svex-alist-keys loop-updates))
;;              (netcomp-p new-updates loop-updates)))

;;   (local (defcong svex-alist-eval-equiv set-equiv (svex-alist-keys x) 1
;;            :hints(("Goal" :in-theory (enable set-equiv)))))

;;   (defret svex-alist-keys-of-<fn>
;;     (equal (svex-alist-keys new-updates)
;;            (svex-alist-keys (svex-alist-clean loop-updates))))

;;   ;; (local (defthm lemma.1
;;   ;;          (IMPLIES
;;   ;;           (AND
;;   ;;            (SVEX-ENVS-AGREE-ON-MASKS (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
;;   ;;                                      (APPEND (SVEX-ALIST-EVAL RES ENV1) ENV1)
;;   ;;                                      (APPEND (SVEX-ALIST-EVAL RES ENV2)
;;   ;;                                              ENV2))
;;   ;;            (SUBSETP-EQUAL (SVEX-ALIST-KEYS RES)
;;   ;;                           (SVEX-ALIST-KEYS LOOP-UPDATES))
;;   ;;            (NOT (SVEX-LOOKUP VAR LOOP-UPDATES)))
;;   ;;           (EQUAL (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
;;   ;;                             (SVEX-ENV-LOOKUP VAR ENV1))
;;   ;;                  (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
;;   ;;                             (SVEX-ENV-LOOKUP VAR ENV2))))
;;   ;;          :hints (("goal" :use ((:instance 


;;   ;; (local (defthm svex-envs-agree-on-masks-of-append-when-reduce-similar
;;   ;;          (implies (and (svex-envs-agree-on-masks masks a b)
;;   ;;                        (set-equiv (alist-keys (svex-env-fix a))
;;   ;;                                   (alist-keys (svex-env-fix b)))
;;   ;;                        (svex-envs-similar (svex-env-removekeys
;;   ;;                                            (alist-keys (svex-env-fix a))
;;   ;;                                            c)
;;   ;;                                           (svex-env-removekeys
;;   ;;                                            (alist-keys (svex-env-fix a))
;;   ;;                                            d)))
;;   ;;                   (svex-envs-agree-on-masks masks (append a c)
;;   ;;                                             (append b d)))
;;   ;;          :hints ((and stable-under-simplificationp
;;   ;;                       `(:computed-hint-replacement
;;   ;;                         ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
;;   ;;                            (and var
;;   ;;                                 `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
;;   ;;                         :expand (,(car (last clause)))
;;   ;;                         :do-not-induct t))
;;   ;;                  (and stable-under-simplificationp
;;   ;;                       '(:use ((:instance svex-envs-similar-necc
;;   ;;                                (k var)
;;   ;;                                (x (append (svarlist-x-env (alist-keys (svex-env-fix a))) c))
;;   ;;                                (y (append (svarlist-x-env (alist-keys (svex-env-fix a))) d))))
;;   ;;                         :in-theory (e/d (member-alist-keys-iff-svex-env-boundp)
;;   ;;                                         (svex-envs-similar-necc
;;   ;;                                          svex-envs-similar-implies-equal-svex-env-lookup-2)))))))


;;   ;; (local (defthm lemma-1
;;   ;;          (implies (and (svex-envs-agree-on-masks
;;   ;;                         (svex-assigns-propagate-masks masks updates)
;;   ;;                         (svex-alist-eval res env1)
;;   ;;                         (svex-alist-eval res env2))
;;   ;;                        (set-equiv (svex-alist-keys updates)
;;   ;;                                   (svex-alist-keys res))
;;   ;;                        (svex-envs-similar (svex-env-removekeys (svex-alist-keys updates) env1)
;;   ;;                                           (svex-env-removekeys (svex-alist-keys updates) env2)))
;;   ;;                   (equal (4vec-mask (svex-mask-lookup (svex-var var) masks)
;;   ;;                                     (svex-eval (svex-lookup var updates)
;;   ;;                                                (append (svex-alist-eval res env1) env1)))
;;   ;;                          (4vec-mask (svex-mask-lookup (svex-var var) masks)
;;   ;;                                     (svex-eval (svex-lookup var updates)
;;   ;;                                                (append (svex-alist-eval res env2) env2)))))
;;   ;;          :hints (("goal"
;;   ;;                   :use ((:instance svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
;;   ;;                          (masks (svex-assigns-propagate-masks masks updates))
;;   ;;                          (x (svex-lookup var updates))
;;   ;;                          (env1 (append (svex-alist-eval res env1) env1))
;;   ;;                          (env2 (append (svex-alist-eval res env2) env2)))
;;   ;;                         (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
;;   ;;                          (assigns updates)
;;   ;;                          (key var)
;;   ;;                          (m (svex-mask-lookup (svex-var var) masks))))
;;   ;;                   :in-theory (disable svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
;;   ;;                                       mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks)))))

;;   ;; (local (defthm lemma-2
;;   ;;          (IMPLIES
;;   ;;           (AND
;;   ;;            (SVEX-ENVS-AGREE-ON-MASKS masks2
;;   ;;                                      (SVEX-ALIST-EVAL RES ENV1)
;;   ;;                                      (SVEX-ALIST-EVAL RES ENV2))
;;   ;;            (booleanp (check-masks-decreasing loop-updates masks masks2))
;;   ;;            (NOT
;;   ;;             (MEMBER-EQUAL (SVAR-FIX VAR)
;;   ;;                           (SVEX-MASKCOMPOSE-DECREASING-VARS
;;   ;;                            LOOP-UPDATES MASKS masks2)))
;;   ;;            (svex-lookup var loop-updates))
;;   ;;           (EQUAL (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
;;   ;;                             (SVEX-EVAL (SVEX-LOOKUP VAR RES) ENV1))
;;   ;;                  (4VEC-MASK (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS)
;;   ;;                             (SVEX-EVAL (SVEX-LOOKUP VAR RES)
;;   ;;                                        ENV2))))
;;   ;;          :hints (("goal" :use ((:instance svex-envs-agree-on-masks-necc
;;   ;;                                 (masks masks2)
;;   ;;                                 (env1 (svex-alist-eval res env1))
;;   ;;                                 (env2 (svex-alist-eval res env2)))
;;   ;;                                (:instance mask-lookup-when-not-member-svex-maskcompose-decreasing-vars
;;   ;;                                 (new-masks masks2)
;;   ;;                                 (assigns loop-updates)
;;   ;;                                 (v var)))
;;   ;;                   :in-theory (disable svex-envs-agree-on-masks-necc
;;   ;;                                       mask-lookup-when-not-member-svex-maskcompose-decreasing-vars))
;;   ;;                  (and stable-under-simplificationp
;;   ;;                       '(:in-theory (enable 4vec-mask))))))
                                  

;;   ;; (local (defthmd svex-alist-keys-is-alist-keys-of-svex-alist-fix
;;   ;;          (equal (svex-alist-keys x)
;;   ;;                 (alist-keys (svex-alist-fix x)))
;;   ;;          :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-fix alist-keys)))))

;;   ;; ;; (local (defthmd svex-lookup-redef

;;   ;; (local (defthmd svex-lookup-under-iff
;;   ;;          (iff (svex-lookup k a)
;;   ;;               (hons-assoc-equal (svar-fix k) (svex-alist-fix a)))
;;   ;;          :hints(("Goal" :in-theory (enable svex-lookup)))))

;;   ;; (local (defthm svex-alist-keys-not-set-equiv-by-svex-lookup-1
;;   ;;          (implies (and (svex-lookup var a)
;;   ;;                        (not (svex-lookup var b)))
;;   ;;                   (not (set-equiv (svex-alist-keys a)
;;   ;;                                   (svex-alist-keys b))))
;;   ;;          :hints(("Goal" :in-theory (e/d (svex-lookup-under-iff
;;   ;;                                          svex-alist-keys-is-alist-keys-of-svex-alist-fix
;;   ;;                                          hons-assoc-equal-iff-member-alist-keys)
;;   ;;                                         (hons-assoc-equal-of-svex-alist-fix))))))

;;   ;; (local (defthm lemma
;;   ;;          (let ((vars (svex-maskcompose-decreasing-vars loop-updates masks
;;   ;;                                                        (svex-assigns-propagate-masks masks loop-updates))))
;;   ;;            (implies (and (svex-envs-agree-on-masks
;;   ;;                           (svex-assigns-propagate-masks masks loop-updates)
;;   ;;                           (svex-alist-eval res env1)
;;   ;;                           (svex-alist-eval res env2))
;;   ;;                          (booleanp (check-masks-decreasing loop-updates masks
;;   ;;                                                        (svex-assigns-propagate-masks masks loop-updates)))
;;   ;;                          (set-equiv (svex-alist-keys loop-updates)
;;   ;;                                     (svex-alist-keys res))
;;   ;;                          (svex-envs-similar (svex-env-removekeys (svex-alist-keys loop-updates) env1)
;;   ;;                                             (svex-env-removekeys (svex-alist-keys loop-updates) env2))
;;   ;;                          ;; (set-equiv (svex-alist-keys res)
;;   ;;                          ;;            (svex-alist-keys loop-updates))
;;   ;;                          )
;;   ;;                     (svex-envs-agree-on-masks
;;   ;;                      masks
;;   ;;                      (append
;;   ;;                       (svex-env-reduce
;;   ;;                        vars
;;   ;;                        (svex-alist-eval loop-updates (append (svex-alist-eval res env1) env1)))
;;   ;;                       (svex-env-extract
;;   ;;                        (svex-alist-keys loop-updates)
;;   ;;                        (append (svex-alist-eval res env1) env1)))
;;   ;;                      (append
;;   ;;                       (svex-env-reduce
;;   ;;                        vars
;;   ;;                        (svex-alist-eval loop-updates (append (svex-alist-eval res env2) env2)))
;;   ;;                       (svex-env-extract
;;   ;;                        (svex-alist-keys loop-updates)
;;   ;;                        (append (svex-alist-eval res env2) env2))))))
;;   ;;          :hints ((and stable-under-simplificationp
;;   ;;                       `(:computed-hint-replacement
;;   ;;                         ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
;;   ;;                            `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var))))))
;;   ;;                         :expand (,(car (last clause)))
;;   ;;                         :do-not-induct t))
;;   ;;                  ;; (and stable-under-simplificationp
;;   ;;                  ;;      '(:use ((:instance svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
;;   ;;                  ;;               (masks (svex-assigns-propagate-masks masks loop-updates))
;;   ;;                  ;;               (x (svex-lookup var loop-updates))
;;   ;;                  ;;               (env1 (append (svex-alist-eval res env1) env1))
;;   ;;                  ;;               (env2 (append (svex-alist-eval res env2) env2)))
;;   ;;                  ;;              (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
;;   ;;                  ;;               (assigns loop-updates)
;;   ;;                  ;;               (key var)
;;   ;;                  ;;               (m (svex-mask-lookup (svex-var var) masks))))
;;   ;;                  ;;        :in-theory (disable svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
;;   ;;                  ;;                            mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks)))
;;   ;;                  )
;;   ;;          :otf-flg t))

;;   ;; (defret final-masks-valid-of-<fn>
;;   ;;   (implies (and (svex-envs-agree-on-masks final-masks env1 env2)
;;   ;;                 (svex-envs-similar (svex-env-removekeys (svex-alist-keys loop-updates) env1)
;;   ;;                                    (svex-env-removekeys (svex-alist-keys loop-updates) env2))
;;   ;;                 (no-duplicatesp-equal (svex-alist-keys loop-updates)))
;;   ;;            (svex-envs-agree-on-masks
;;   ;;             masks
;;   ;;             (svex-alist-eval new-updates env1)
;;   ;;             (svex-alist-eval new-updates env2)))
;;   ;;   :hints (("goal" :induct <call>
;;   ;;            :expand (<call>))
;;   ;;           (and stable-under-simplificationp
;;   ;;                (b* (((mv ok1 final-masks) (acl2::find-match-list '(mv-nth '0 (svex-alist-maskcompose-iter-simple a b)) clause nil))
;;   ;;                     ((mv ok2 res) (acl2::find-match-list '(mv-nth '1 (svex-alist-maskcompose-iter-simple a b)) clause nil)))
;;   ;;                  (and ok1 ok2
;;   ;;                       `(:clause-processor
;;   ;;                         (acl2::generalize-with-alist-cp clause '((,final-masks . final-masks)
;;   ;;                                                                  (,res . res)))))))))
;;   (verify-guards svex-alist-maskcompose-iter-simple))



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
           :hints(("Goal" :in-theory (enable nth svex-env-lookup svex-env-fix index-of)))))

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
         (svex-lookup var x)))

  (defret not-svex-lookup-of-<fn>
    (implies (not (svex-lookup var x))
             (not (svex-lookup var new-x)))))


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

(define svex-alist-nonzero-mask-keys ((x svex-alist-p)
                                      (masks svex-mask-alist-p))
  :returns (keys svarlist-p)
  (b* (((when (atom x)) nil)
       ((unless (and (mbt (and (consp (car x))
                               (svar-p (caar x))))
                     (not (sparseint-equal 0 (svex-mask-lookup (svex-var (caar x)) masks)))))
        (svex-alist-nonzero-mask-keys (cdr x) masks)))
    (cons (caar x)
          (svex-alist-nonzero-mask-keys (cdr x) masks)))
  ///
  (defret member-of-<fn>
    (iff (member-equal var keys)
         (and (svar-p var)
              (svex-lookup var x)
              (not (sparseint-equal 0 (svex-mask-lookup (svex-var var) masks)))))
    :hints(("Goal" :in-theory (enable svex-lookup-redef))))

  (defret no-duplicatesp-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (no-duplicatesp-equal keys))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (local (in-theory (enable svex-alist-fix))))



(define svex-alist-filter-nonzero-masks ((x svex-alist-p)
                                         (masks svex-mask-alist-p))
  :returns (new-x svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (and (mbt (and (consp (car x))
                               (svar-p (caar x))))
                     (not (sparseint-equal 0 (svex-mask-lookup (svex-var (caar x)) masks)))))
        (svex-alist-filter-nonzero-masks (cdr x) masks)))
    (cons-with-hint
     (mbe :logic (cons (caar x) (svex-fix (cdar x)))
          :exec (car x))
     (svex-alist-filter-nonzero-masks (cdr x) masks)
     x))
  ///
  (defret svex-lookup-in-<fn>
    (equal (svex-lookup var new-x)
           (and (not (sparseint-equal 0 (svex-mask-lookup (svex-var var) masks)))
                (svex-lookup var x)))
    :hints(("Goal" :in-theory (enable svex-lookup-redef))))

  (defret svex-alist-keys-subsetp-of-<fn>
    (subsetp-equal (svex-alist-keys new-x) (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defret svex-alist-keys-subsetp-of-<fn>-trans
    (implies (subsetp-equal (svex-alist-keys x) keys)
             (subsetp-equal (svex-alist-keys new-x) keys))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  ;; (defret no-duplicate-keys-of-<fn>
  ;;   (implies (no-duplicatesp-equal (svex-alist-keys x))
  ;;            (no-duplicatesp-equal (svex-alist-keys new-x))))

  (defret svex-mask-alist-negcount-of-<fn>
    (<= (svex-mask-alist-negcount (svex-alist-keys new-x) masks)
        (svex-mask-alist-negcount (svex-alist-keys x) masks))
    :hints(("Goal" :in-theory (enable svex-alist-keys
                                      svex-mask-alist-negcount)))
    :rule-classes :linear)
  (defret svex-mask-alist-nonnegcount-of-<fn>
    (<= (svex-mask-alist-nonnegcount (svex-alist-keys new-x) masks)
        (svex-mask-alist-nonnegcount (svex-alist-keys x) masks))
    :hints(("Goal" :in-theory (enable svex-alist-keys
                                      svex-mask-alist-nonnegcount)))
    :rule-classes :linear)

  (defret svex-mask-alist-measure-of-<fn>
    (implies (acl2::nat-list-< (svex-mask-alist-measure (svex-alist-keys x) masks)
                               (svex-mask-alist-measure y m))
             (acl2::nat-list-< (svex-mask-alist-measure (svex-alist-keys new-x) masks)
                               (svex-mask-alist-measure y m)))
    :hints(("Goal" :in-theory (enable svex-mask-alist-measure))))

  (local (defthm svex-alist-reduce-cdr-when-car-not-member
           (implies (and (or (not (consp x))
                             (not (consp (car x)))
                             (not (svar-p (caar x)))
                             (not (member-equal (caar x) (svarlist-fix keys)))))
                    (equal (svex-alist-reduce keys (cdr x))
                           (svex-alist-reduce keys x)))
           :hints(("Goal" :in-theory (enable svex-alist-reduce
                                             svex-lookup-redef)))))

  (defret no-duplicate-keys-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (no-duplicatesp-equal (svex-alist-keys new-x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defretd <fn>-in-terms-of-svex-alist-reduce
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal new-x
                    (svex-alist-reduce (svex-alist-nonzero-mask-keys x masks) x)))
    :hints(("Goal" :in-theory (enable svex-alist-nonzero-mask-keys
                                      svex-alist-reduce
                                      svex-alist-keys))))

  (local (in-theory (enable svex-alist-fix))))

(local
 (defthm svex-alist-keys-of-svex-alist-reduce
   (equal (svex-alist-keys (svex-alist-reduce keys a))
          (intersection-equal (svarlist-fix keys)
                              (svex-alist-keys a)))
   :hints(("Goal" :in-theory (enable svex-alist-reduce
                                     svex-alist-keys)))))

(local
 (defthm svex-alist-keys-of-svex-alist-compose
   (equal (svex-alist-keys (svex-alist-compose a b))
          (svex-alist-keys a))
   :hints(("Goal" :in-theory (enable svex-alist-compose
                                     svex-alist-keys)))))

(local
 (defthm svex-alist-keys-of-append
   (equal (svex-alist-keys (append a b))
          (append (svex-alist-keys a)
                  (svex-alist-keys b)))
   :hints(("Goal" :in-theory (enable svex-alist-keys)))))

(local
 (define svex-alist-maskcompose-iter-spec ((orig-updates svex-alist-p)
                                           (masks svex-mask-alist-p)
                                           (loop-updates svex-alist-p))
   :hints(("Goal" :in-theory (enable o<)))
   :verify-guards nil
   :measure (svex-mask-alist-measure (svex-alist-keys loop-updates) masks)
   :well-founded-relation acl2::nat-list-<
   :returns (new-updates svex-alist-p)
   (b* ((next-masks (cwtime (svex-assigns-propagate-masks masks loop-updates)))
        (status (check-masks-decreasing (svex-alist-keys loop-updates) masks next-masks))
        ((unless status)
         (cw "Masks stopped shrinking~%")
         (fast-alist-free next-masks)
         ;; (mv next-masks
         (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates))
        ((unless (eq status t))
         (cw "Monotonicity violation: ~x0~%" status)
         (fast-alist-free next-masks)
         ;; (mv next-masks 
         (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates))
        (next-updates (cwtime (svex-alist-rewrite-under-masks loop-updates next-masks)))
        (next-loop-updates (cwtime (svex-alist-filter-nonzero-masks next-updates next-masks)))
        (rest-composed ;; (mv final-masks rest-composed)
         (cwtime (svex-alist-maskcompose-iter-spec
                  orig-updates next-masks next-loop-updates)))
        (composed (with-fast-alist rest-composed
                    (cwtime
                     (svex-alist-compose
                      (append (svex-alist-reduce
                               (svex-maskcompose-decreasing-vars
                                (svex-alist-keys next-updates) masks next-masks)
                               orig-updates)
                              (svex-identity-subst (svex-alist-keys next-updates)))
                      ;;(cwtime (svex-alist-rewrite-under-masks loop-updates next-masks))
                      rest-composed)))))
     (fast-alist-free next-masks)
     composed)
   ///
   (defret netcomp-p-of-<fn>
     (implies (and (no-duplicatesp-equal (svex-alist-keys orig-updates))
                   (subsetp-equal (svex-alist-keys loop-updates)
                                  (svex-alist-keys orig-updates)))
              (netcomp-p new-updates orig-updates)))

   (local (defthm intersection-when-subsetp
            (implies (subsetp-equal a b)
                     (set-equiv (intersection-equal a b) a))
            :hints(("Goal" :in-theory (enable intersection-equal
                                              subsetp-equal)))))

   (local (defthm subsetp-of-intersection
            (implies (or (subsetp-equal a c)
                         (subsetp-equal b c))
                     (subsetp-equal (intersection-equal a b) c))
            :hints(("Goal" :in-theory (enable intersection-equal)))))

   (defret alist-keys-of-<fn>
     (implies (subsetp-equal (svex-alist-keys loop-updates)
                                  (svex-alist-keys orig-updates))
              (set-equiv (svex-alist-keys new-updates) (svex-alist-keys loop-updates))))))

(defsection svex-alists-agree-on-masks
  (defun-sk svex-alists-agree-on-masks (masks a b)
    (forall env
            (svex-envs-agree-on-masks
             masks
             (svex-alist-eval a env)
             (svex-alist-eval b env)))
    :rewrite :direct)

  (in-theory (disable svex-alists-agree-on-masks))

  (defthm svex-alists-agree-on-masks-implies-lookup
    (implies (svex-alists-agree-on-masks masks a b)
             (equal (4vec-mask (svex-mask-lookup (svex-var var) masks)
                               (svex-eval (svex-lookup var a) env))
                    (4vec-mask (svex-mask-lookup (svex-var var) masks)
                               (svex-eval (svex-lookup var b) env))))
    :hints (("goal" :use ((:instance svex-alists-agree-on-masks-necc)
                          (:instance svex-envs-agree-on-masks-necc
                           (env1 (svex-alist-eval a env))
                           (env2 (svex-alist-eval b env))))
             :in-theory (disable svex-alists-agree-on-masks-necc
                                 svex-envs-agree-on-masks-necc))))

  (defun svex-alists-agree-on-masks-lookup-witness (masks a b)
    (b* ((env (svex-alists-agree-on-masks-witness masks a b))
         (var (svex-envs-agree-on-masks-witness
               masks (svex-alist-eval a env) (svex-alist-eval b env))))
      (mv var env)))

  (defthmd svex-alists-agree-on-masks-iff-lookup-witness
    (iff (svex-alists-agree-on-masks masks a b)
         (b* (((mv var env) (svex-alists-agree-on-masks-lookup-witness masks a b))
              (mask (svex-mask-lookup (svex-var var) masks)))
           (equal (4vec-mask mask (svex-eval (svex-lookup var a) env))
                  (4vec-mask mask (svex-eval (svex-lookup var b) env)))))
    :hints(("Goal" :in-theory (enable svex-alists-agree-on-masks
                                      svex-envs-agree-on-masks)))
    :rule-classes :definition)

  (defthm svex-alists-agree-on-masks-refl
    (svex-alists-agree-on-masks masks a a)
    :hints(("Goal" :in-theory (enable svex-alists-agree-on-masks))))


  (defcong svex-alist-eval-equiv iff (svex-alists-agree-on-masks masks a b) 2
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-alists-agree-on-masks clause))
                        (other-a (if (eq (third lit) 'a) 'a-equiv 'a)))
                   `(:computed-hint-replacement
                     ((and stable-under-simplificationp
                           (let ((env (acl2::find-call-lst 'svex-alists-agree-on-masks-witness clause)))
                             `(:clause-processor (acl2::generalize-with-alist-cp clause '((,env . env))))))
                      (and stable-under-simplificationp
                           '(:use ((:instance svex-alists-agree-on-masks-necc
                                    (a ,other-a)))
                             :in-theory (disable svex-alists-agree-on-masks-necc))))
                     :expand ((:with svex-alists-agree-on-masks ,lit)))))))

  (defcong svex-alist-eval-equiv iff (svex-alists-agree-on-masks masks a b) 3
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-alists-agree-on-masks clause))
                        (other-b (if (eq (fourth lit) 'b) 'b-equiv 'b)))
                   `(:computed-hint-replacement
                     ((and stable-under-simplificationp
                           (let ((env (acl2::find-call-lst 'svex-alists-agree-on-masks-witness clause)))
                             `(:clause-processor (acl2::generalize-with-alist-cp clause '((,env . env))))))
                      (and stable-under-simplificationp
                           '(:use ((:instance svex-alists-agree-on-masks-necc
                                    (b ,other-b)))
                             :in-theory (disable svex-alists-agree-on-masks-necc))))
                     :expand ((:with svex-alists-agree-on-masks ,lit)))))))
            
                 

  (in-theory (disable svex-alists-agree-on-masks-lookup-witness)))


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
  (b* ((next-masks (cwtime (svex-assigns-propagate-masks masks loop-updates)))
       ;; NOTE: One reason we can't eliminate bindings from loop updates is because
       ;; we only check monotonicity on keys of loop-updates.  If we want to eliminate bindings,
       ;; even on variables whose masks are 0, then we have to ensure that those masks stay 0.
       (status (cwtime (check-masks-stats loop-updates masks next-masks)))
       (next-updates (cwtime (svex-alist-rewrite-under-masks loop-updates next-masks)))
       ((unless status)
        (cw "Masks stopped shrinking~%")
        (fast-alist-free next-masks)
        (mv next-masks ;; (svex-alist-fix loop-updates)
            ;; (cwtime (svex-alist-rewrite-under-masks loop-updates next-masks))
            next-updates
            ))
       ((unless (eq status t))
        (cw "Monotonicity violation: ~x0~%" status)
        (fast-alist-free next-masks)
        (mv next-masks ;; (svex-alist-fix loop-updates)
            next-updates))
       (next-loop-updates (cwtime (svex-alist-filter-nonzero-masks next-updates next-masks)))
       ((mv final-masks rest-composed)
        (cwtime (svex-alist-maskcompose-iter
                 next-masks next-loop-updates simpconf)))
       (composed (with-fast-alist rest-composed
                   (cwtime
                    (svex-maskcompose-step-alist-rw
                     ;;(cwtime (svex-alist-rewrite-under-masks loop-updates next-masks))
                     next-updates
                     masks next-masks
                     (make-svex-substconfig :simp simpconf
                                            :alist rest-composed))))))
    (clear-memoize-table 'svex-compose-rw-memo)
    (fast-alist-free next-masks)
    (mv final-masks composed))
  ///

  (defret alist-keys-of-<fn>
    (equal (svex-alist-keys new-updates) (svex-alist-keys loop-updates)))

  (local (defthmd svex-lookup-under-iff
           (iff (svex-lookup k a)
                (hons-assoc-equal (svar-fix k) (svex-alist-fix a)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (local (defthmd svex-alist-keys-is-alist-keys-of-svex-alist-fix
           (equal (svex-alist-keys x)
                  (alist-keys (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-fix alist-keys)))))

  (local (defthmd svex-env-lookup-is-hons-assoc-equal-of-svex-env-fix
           (equal (svex-env-lookup var env)
                  (4vec-fix (cdr (hons-assoc-equal (svar-fix var) (svex-env-fix env)))))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (local (defthmd hons-assoc-equal-when-not-member-keys
           (implies (not (member-equal key (alist-keys a)))
                    (not (hons-assoc-equal key a)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal-iff-member-alist-keys)))))

  (local (defthm svex-env-lookup-when-set-equiv-blah
           (implies (and (set-equiv (svex-alist-keys a)
                                    (alist-keys (svex-env-fix env)))
                         (not (svex-lookup var a)))
                    (equal (svex-env-lookup var env) (4vec-x)))
           :hints(("Goal" :in-theory (e/d (svex-lookup-under-iff
                                           hons-assoc-equal-iff-member-alist-keys
                                           hons-assoc-equal-when-not-member-keys
                                           svex-alist-keys-is-alist-keys-of-svex-alist-fix
                                           svex-env-lookup-is-hons-assoc-equal-of-svex-env-fix)
                                          (hons-assoc-equal-of-svex-env-fix))))))

  (local (defthmd rewrite-mask-expr-when-4vmask-subsumes
           (implies (and (4vmask-subsumes mask1 mask2)
                         (equal (4vec-mask mask1 a)
                                (4vec-mask mask1 b)))
                    (equal (4vec-mask mask2 a)
                           (4vec-mask mask2 b)))))


  (local (defthm rewrite-away-rewrite-under-masks-lookup-under-subsump
           (implies (and (equal (4vec-mask mask1 (svex-eval (svex-lookup var (svex-alist-rewrite-under-masks masks loop-updates)) env))
                                (4vec-mask mask1 other))
                         (4vmask-subsumes mask1 mask2))
                    (equal (4vec-mask mask2 (svex-eval (svex-lookup var (svex-alist-rewrite-under-masks masks loop-updates)) env))
                           (4vec-mask mask2 other)))))


  (local (include-book "std/util/termhints" :dir :system))

  (local
   (defthm check-masks-decreasing-implies-envs-agree-on-masks
     (let ((new-masks (svex-assigns-propagate-masks masks loop-updates)))
       (implies (and (booleanp (check-masks-decreasing (svex-alist-keys loop-updates) masks new-masks))
                     ;; (equal (svex-alist-keys loop-updates) (alist-keys (svex-env-fix orig-eval)))
                     (svex-envs-agree-on-masks
                      masks
                      (svex-alist-eval loop-updates env)
                      (svex-alist-eval (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates) env)))
                (svex-envs-agree-on-masks
                 new-masks
                 (svex-alist-eval
                  (svex-alist-filter-nonzero-masks
                   (svex-alist-rewrite-under-masks
                    loop-updates new-masks)
                   new-masks)
                  env)
                 (svex-alist-eval (svex-alist-filter-nonzero-masks
                                   (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates)
                                   new-masks)
                                  env))))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))
             (and stable-under-simplificationp
                  (let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                    `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var))))))
             (and stable-under-simplificationp
                  '(:use ((:instance svex-envs-agree-on-masks-necc
                           (env2 (svex-alist-eval (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates) env))
                           (env1 (svex-alist-eval loop-updates env)))
                          (:instance 4vmask-subsumes-by-check-masks-decreasing
                           (vars (svex-alist-keys loop-updates))
                           (new-masks (svex-assigns-propagate-masks masks loop-updates)))
                          (:instance lookup-of-svex-alist-rewrite-under-masks
                           (x loop-updates)
                           (masks (svex-assigns-propagate-masks masks loop-updates))
                           (verbosep nil))
                          (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                           (key var)
                           (assigns loop-updates)
                           (m (SVEX-MASK-LOOKUP (SVEX-VAR VAR)
                                                (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))))
                          ;; (:instance rewrite-mask-expr-when-4vmask-subsumes
                          ;;  (mask2 (SVEX-MASK-LOOKUP (SVEX-VAR VAR)
                          ;;                           (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)))
                          ;;  (a (SVEX-EVAL (SVEX-LOOKUP VAR LOOP-UPDATES)
                          ;;                ENV))
                          ;;  (b (SVEX-EVAL
                          ;;      (SVEX-LOOKUP VAR
                          ;;                   (SVEX-ALIST-REWRITE-UNDER-MASKS
                          ;;                    LOOP-UPDATES
                          ;;                    (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
                          ;;                    :VERBOSEP NIL))
                          ;;      ENV))
                          ;;  (mask1 (SVEX-MASK-LOOKUP (SVEX-LOOKUP VAR LOOP-UPDATES)
                          ;;                           (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))))
                          (:instance rewrite-mask-expr-when-4vmask-subsumes
                           (mask2 (SVEX-MASK-LOOKUP (SVEX-VAR VAR)
                                                    (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)))
                           (a (SVEX-EVAL (SVEX-LOOKUP VAR LOOP-UPDATES)
                                         ENV))
                           (b (SVEX-ENV-LOOKUP VAR (svex-alist-eval (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates) env)))
                           (mask1 (SVEX-MASK-LOOKUP (SVEX-VAR VAR) MASKS))))
                    :in-theory (disable svex-envs-agree-on-masks-necc
                                        lookup-of-svex-alist-rewrite-under-masks
                                        mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks)
                    :do-not-induct t)))
     :otf-flg t))


  (local
   (defthm check-masks-decreasing-implies-alists-agree-on-masks
     (let ((new-masks (svex-assigns-propagate-masks masks loop-updates)))
       (implies (and (booleanp (check-masks-decreasing (svex-alist-keys loop-updates) masks new-masks))
                     (subsetp-equal (svex-alist-keys loop-updates) (svex-alist-keys orig-updates))
                     (svex-alists-agree-on-masks
                      masks loop-updates (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates)))
                (svex-alists-agree-on-masks
                 new-masks
                 (svex-alist-filter-nonzero-masks
                  (svex-alist-rewrite-under-masks
                   loop-updates new-masks)
                  new-masks)
                 (svex-alist-filter-nonzero-masks
                  (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates)
                  new-masks))))
     :hints ((and stable-under-simplificationp
                  `(:expand ((:with svex-alists-agree-on-masks ,(car (last clause))))))
             (and stable-under-simplificationp
                  (let ((env (acl2::find-call-lst 'svex-alists-agree-on-masks-witness clause)))
                    `(:clause-processor (acl2::generalize-with-alist-cp clause '((,env . env))))))
             (and stable-under-simplificationp
                  `(:use ((:instance svex-alists-agree-on-masks-necc
                           (b (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates)) (a loop-updates)))
                    :in-theory (disable svex-alists-agree-on-masks-necc))))))

  ;; (local (defun smdvwsake-ind (a b)
  ;;          (declare (xargs :measure (+ (len a) (len b))
  ;;                          :ruler-extenders :all))
  ;;          (b* (((when (and (atom a) (atom b))) (list a b))
  ;;               ((when (atom a))
  ;;                (smdvwsake-ind a (cdr b)))
  ;;               ((when (atom b))
  ;;                (smdvwsake-ind (cdr a) b))
  ;;               ((mv next-a next-b)
  ;;                (if (and (consp (car a))
  ;;                         (svar-p (caar a)))
  ;;                    (if (and (consp (car b))
  ;;                             (svar-p (caar b)))
  ;;                        (mv (cdr a) (cdr b))
  ;;                      (mv a (cdr b)))
  ;;                  (if (and (consp (car b))
  ;;                           (svar-p (caar b)))
  ;;                      (mv (cdr a) b)
  ;;                    (mv (cdr a) (cdr b))))))
  ;;            (smdvwsake-ind next-a next-b))))

  ;; (local (defthmd svex-maskcompose-decreasing-vars-when-svex-alist-keys-equal
  ;;          (implies (equal (svex-alist-keys a) (svex-alist-keys b))
  ;;                   (equal (equal (svex-maskcompose-decreasing-vars a masks new-masks)
  ;;                                 (svex-maskcompose-decreasing-vars b masks new-masks))
  ;;                          t))
  ;;          :hints(("Goal" :in-theory (enable svex-maskcompose-decreasing-vars
  ;;                                            svex-alist-keys)
  ;;                  :induct (smdvwsake-ind a b)
  ;;                  :expand ((svex-maskcompose-decreasing-vars a masks new-masks)
  ;;                           (svex-maskcompose-decreasing-vars b masks new-masks))))))

  ;; (local (defthm svex-maskcompose-decreasing-vars-of-svex-alist-rewrite-under-masks
  ;;          (equal (svex-maskcompose-decreasing-vars (svex-alist-rewrite-under-masks a m :verbosep verb)
  ;;                                                   masks masks2)
  ;;                 (svex-maskcompose-decreasing-vars a masks masks2))
  ;;          :hints(("Goal" :in-theory (enable svex-maskcompose-decreasing-vars-when-svex-alist-keys-equal)))))
 

                    
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
                          enva envb)
                         (set-equiv (alist-keys (svex-env-fix enva))
                                    (alist-keys (svex-env-fix envb))))
                    (equal (4vec-mask (svex-mask-lookup (svex-var var) masks)
                                      (svex-eval (svex-lookup var updates)
                                                 (append enva env)))
                           (4vec-mask (svex-mask-lookup (svex-var var) masks)
                                      (svex-eval (svex-lookup var updates)
                                                 (append envb env)))))
           :hints (("goal"
                    :use ((:instance svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                           (masks (svex-assigns-propagate-masks masks updates))
                           (x (svex-lookup var updates))
                           (env1 (append enva env))
                           (env2 (append envb env)))
                          (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                           (assigns updates)
                           (key var)
                           (m (svex-mask-lookup (svex-var var) masks))))
                    :in-theory (disable svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
                                        mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks)
                    :do-not-induct t))))

  (local (defcong 4vmask-equal equal (4vec-mask mask vec) 1
           :hints(("Goal" :in-theory (enable 4vec-mask)))))


  (local (defthm member-maskcompose-decreasing-vars-when-not-svex-lookup
           (implies (not (svex-lookup var loop-updates))
                    (not (member-equal (svar-fix var)
                                       (svex-maskcompose-decreasing-vars
                                        (svex-alist-keys loop-updates)
                                        masks new-masks))))
           :hints(("Goal" :in-theory (enable svex-maskcompose-decreasing-vars
                                             svex-alist-keys
                                             svex-lookup-redef)))))

  (local (Defthm not-subsetp-alist-keys-by-lookup
           (implies (and (svex-lookup var loop-updates)
                         (not (svex-lookup var orig-updates)))
                    (not (subsetp-equal (svex-alist-keys loop-updates)
                                        (Svex-Alist-Keys orig-updates))))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup-redef)))))

  (local (Defthm not-set-equiv-alist-keys-by-lookup-1
           (implies (and (svex-lookup var loop-updates)
                         (not (svex-lookup var orig-updates)))
                    (not (set-equiv (svex-alist-keys loop-updates)
                                    (Svex-Alist-Keys orig-updates))))
           :hints(("Goal" :in-theory (enable set-equiv)))))

  (local (Defthm not-set-equiv-alist-keys-by-lookup-2
           (implies (and (svex-lookup var loop-updates)
                         (not (svex-lookup var orig-updates)))
                    (not (set-equiv (Svex-Alist-Keys orig-updates)
                                    (svex-alist-keys loop-updates))))
           :hints(("Goal" :in-theory (enable set-equiv)))))

  (local
   (defthm lemma
     (b* ((new-masks (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))
          (decr-vars (SVEX-MASKCOMPOSE-DECREASING-VARS
                      (SVEX-ALIST-KEYS LOOP-UPDATES)
                      MASKS
                      new-masks)))
       (IMPLIES
        (AND
         (EQUAL
          (CHECK-MASKS-DECREASING (svex-alist-keys LOOP-UPDATES) MASKS
                                  new-masks)
          T)
         (SVEX-ENVS-AGREE-ON-MASKS new-masks
                                   (SVEX-ALIST-EVAL RES ENV)
                                   (SVEX-ALIST-EVAL SPEC ENV))
         (svex-alists-agree-on-masks MASKS loop-updates
                                     (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates))
         (subsetp-EQUAL (SVEX-ALIST-KEYS LOOP-UPDATES)
                        (SVEX-ALIST-KEYS ORIG-UPDATES))
         (set-equiv (svex-alist-keys spec)
                    (svex-alist-keys res))
         (subsetp-equal (svex-alist-keys res)
                        (svex-alist-keys loop-updates))
         ;; (equal (svex-alist-keys res)
         ;;        (svex-alist-keys loop-updates))
         ;; (NO-DUPLICATESP-EQUAL (SVEX-ALIST-KEYS LOOP-UPDATES))
         )
        (SVEX-ENVS-AGREE-ON-MASKS
         MASKS
         (APPEND
          (SVEX-ENV-REDUCE
           decr-vars
           (SVEX-ALIST-EVAL
            (SVEX-ALIST-REWRITE-UNDER-MASKS
             LOOP-UPDATES
             new-masks
             :VERBOSEP NIL)
            (APPEND (SVEX-ALIST-EVAL RES ENV) ENV)))
          (SVEX-ENV-EXTRACT (SVEX-ALIST-KEYS LOOP-UPDATES)
                            (APPEND (SVEX-ALIST-EVAL RES ENV)
                                    ENV)))
         (APPEND
          (SVEX-ENV-REDUCE decr-vars
                           (SVEX-ALIST-EVAL ORIG-UPDATES
                                            (APPEND (SVEX-ALIST-EVAL SPEC ENV)
                                                    ENV)))
          (SVEX-ENV-EXTRACT (SVEX-ALIST-KEYS LOOP-UPDATES)
                            (APPEND (SVEX-ALIST-EVAL SPEC ENV)
                                    ENV))))))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))
             (and stable-under-simplificationp
                  (let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause))
                        (termhint
                         '(b* ((new-masks (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES))
                               (decr-vars (SVEX-MASKCOMPOSE-DECREASING-VARS
                                           (SVEX-ALIST-KEYS LOOP-UPDATES)
                                           MASKS
                                           new-masks))
                               ;; (?rw (svex-alist-rewrite-under-masks
                               ;;      loop-updates new-masks :verbosep nil))
                               ((when (member-equal (svar-fix var) decr-vars))
                                `(:use ((:instance acl2::mark-clause-is-true (x 'decreasing-var))
                                        (:instance lookup-of-svex-alist-rewrite-under-masks
                                         (x loop-updates)
                                         (masks ,(acl2::hq new-masks))
                                         (verbosep nil)
                                         (env (APPEND (SVEX-ALIST-EVAL RES ENV)
                                                      ENV)))
                                        ;; (:instance 4vmask-subsumes-by-check-masks-decreasing
                                        ;;  (new-masks ,(acl2::hq new-masks))
                                        ;;  (assigns loop-updates))
                                        (:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                                         (key var)
                                         (assigns loop-updates)
                                         (m (svex-mask-lookup (svex-var var) masks))))
                                  :in-theory (disable lookup-of-svex-alist-rewrite-under-masks
                                                      4vmask-subsumes-by-check-masks-decreasing
                                                      mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks))))
                            '(:use ((:instance acl2::mark-clause-is-true (x 'nondecreasing-var))
                                    (:instance mask-lookup-when-not-member-svex-maskcompose-decreasing-vars
                                     (assigns loop-updates)
                                     (new-masks (svex-assigns-propagate-masks masks loop-updates))
                                     (v var))
                                    (:instance svex-envs-agree-on-masks-necc
                                     (masks (svex-assigns-propagate-masks masks loop-updates))
                                     (env2 (svex-alist-eval spec env))
                                     (env1 (svex-alist-eval res env))))
                              :in-theory (disable mask-lookup-when-not-member-svex-maskcompose-decreasing-vars
                                                  svex-envs-agree-on-masks-necc
                                                  4vmask-equal)))))
                    `(:computed-hint-replacement
                      ((acl2::use-termhint
                        ,termhint))

                      :clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))
                      :do-not-induct t))))
                  
     :otf-flg t))

  (local
   (defthm lemma-3
     (IMPLIES
      (AND
       (SVEX-ALISTS-AGREE-ON-MASKS MASKS LOOP-UPDATES
                                   (svex-alist-reduce (svex-alist-keys loop-updates) ORIG-UPDATES))
       (subsetp-EQUAL (SVEX-ALIST-KEYS LOOP-UPDATES)
                      (SVEX-ALIST-KEYS ORIG-UPDATES))
       ;; (NO-DUPLICATESP-EQUAL (SVEX-ALIST-KEYS LOOP-UPDATES))
       )
      (SVEX-ENVS-AGREE-ON-MASKS
       MASKS
       (SVEX-ALIST-EVAL
        (SVEX-ALIST-REWRITE-UNDER-MASKS
         LOOP-UPDATES
         (SVEX-ASSIGNS-PROPAGATE-MASKS MASKS LOOP-UPDATES)
         :VERBOSEP NIL)
        ENV)
       (svex-env-reduce (svex-alist-keys loop-updates)
                        (SVEX-ALIST-EVAL ORIG-UPDATES ENV))))
     :hints ((and stable-under-simplificationp
                        `(:computed-hint-replacement
                          ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                             (and var
                                  `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
                          :expand (,(car (last clause)))
                          :do-not-induct t))
             (and stable-under-simplificationp
                  '(:use ((:instance mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                           (assigns loop-updates)
                           (m (svex-mask-lookup (svex-var var) masks))
                           (key var))
                          (:instance lookup-of-svex-alist-rewrite-under-masks
                           (x loop-updates)
                           (masks (svex-assigns-propagate-masks masks loop-updates))
                           (verbosep nil)))
                    :in-theory (disable mask-lookup-of-svex-lookup-of-svex-assigns-propagate-masks
                                        lookup-of-svex-alist-rewrite-under-masks))))
     :otf-flg t))
             
  (local
   (defret alist-keys-of-<fn>
     (equal (svex-alist-keys new-updates)
            (svex-alist-keys loop-updates))))


  (local (defthm svex-alist-reduce-keys-of-filter-nonzero-masks
           (implies (subsetp-equal (svex-alist-keys loop-updates)
                                   (svex-alist-keys orig-updates))
                    (equal (svex-alist-reduce
                            (svex-alist-keys
                             (svex-alist-filter-nonzero-masks loop-updates masks))
                            orig-updates)
                           (svex-alist-filter-nonzero-masks
                            (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates)
                            masks)))
           :hints(("Goal" :in-theory (enable svex-alist-keys
                                             svex-alist-filter-nonzero-masks
                                             svex-alist-reduce)))))
                             


  (local
   (defret <fn>-agrees-with-spec
     (implies (and (svex-alists-agree-on-masks
                    masks loop-updates
                    (svex-alist-reduce (svex-alist-keys loop-updates) orig-updates))
                   (subsetp-equal (svex-alist-keys loop-updates) (svex-alist-keys orig-updates))
                   (no-duplicatesp-equal (svex-alist-keys orig-updates)) ;; ???
                   (no-duplicatesp-equal (svex-alist-keys loop-updates)))
              (svex-envs-agree-on-masks
               masks
               (svex-alist-eval new-updates
                                env)
               (svex-alist-eval (svex-alist-maskcompose-iter-spec
                                 orig-updates masks loop-updates)
                                env)))
     :hints (("goal" :induct <call>
              :in-theory (disable (:d svex-alist-maskcompose-iter))
              :expand ((svex-alist-maskcompose-iter-spec
                        orig-updates masks loop-updates)
                       <call>))
             (and stable-under-simplificationp
                  (b* (((mv ok1 spec) (acl2::find-match-list '(svex-alist-maskcompose-iter-spec a b c) clause nil))
                       ((mv ok2 res) (acl2::find-match-list '(mv-nth '1 (svex-alist-maskcompose-iter a b c)) clause nil)))
                    (and ok1 ok2
                         `(:clause-processor
                           (acl2::generalize-with-alist-cp clause '((,res . res) (,spec . spec)))))))
             )))

  (local (defthm member-svarlist->svexes
           (iff (member-equal (svex-var var) (svarlist->svexes vars))
                (member-equal (svar-fix var) (svarlist-fix vars)))
           :hints(("Goal" :in-theory (enable svarlist->svexes)))))

  (local (defthmd svex-env-lookup-in-terms-of-svex-env-fix
           (equal (svex-env-lookup var env)
                  (4vec-fix (cdr (hons-assoc-equal (svar-fix var) (svex-env-fix env)))))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  ;; (local (defthmd svex-env-lookup-when-not-member
  ;;          (implies (not (member-equal (svar-fix var) (alist-keys (svex-env-fix env))))
  ;;                   (equal (svex-env-lookup var env) (4vec-x)))
  ;;          :hints(("Goal" :in-theory (e/d (svex-env-lookup-in-terms-of-svex-env-fix
  ;;                                          hons-assoc-equal-iff-member-alist-keys)
  ;;                                         (hons-assoc-equal-of-svex-env-fix))
  ;;                  :cases ((hons-assoc-equal (svar-fix var) (svex-env-fix env)))))))

  (local (defthmd svex-env-lookup-when-not-member
           (implies (not (member-equal (svar-fix var) (alist-keys (svex-env-fix env))))
                    (equal (svex-env-lookup var env) (4vec-x)))
           :hints(("Goal" :in-theory (e/d (svex-env-lookup-in-terms-of-svex-env-fix
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-env-fix))
                   :cases ((hons-assoc-equal (svar-fix var) (svex-env-fix env)))))))

  (local (defthmd svex-env-lookup-when-not-boundp
           (implies (not (svex-env-boundp var env))
                    (equal (svex-env-lookup var env) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup
                                             svex-env-boundp)))))

  ;; (local (defthmd svex-env-lookup-when-not-member-alist-keys
  ;;          (implies (not (member-equal (svar-fix var) (alist-keys (svex-env-fix env))))
  ;;                   (equal (svex-env-lookup var env) (4vec-x)))
  ;;          :hints(("Goal" :in-theory (enable svex-env-lookup)))))


  (defthmd svex-envs-agree-on-masks-of-neg1s
    (implies (and (set-equiv (svarlist-fix vars) (alist-keys (svex-env-fix env1)))
                  (set-equiv (svarlist-fix vars) (alist-keys (svex-env-fix env2))))
             (iff (svex-envs-agree-on-masks (svexlist-mask-acons (svarlist->svexes vars) -1 nil) env1 env2)
                  (svex-envs-equivalent env1 env2)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable svex-envs-equivalent)))
            (and stable-under-simplificationp
                 (let ((var (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                   `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var))))))
            (and stable-under-simplificationp
                 '(:use ((:instance svex-envs-agree-on-masks-necc
                          (masks (svexlist-mask-acons (svarlist->svexes vars) -1 nil))))
                   :in-theory (e/d (svex-env-lookup-when-not-boundp
                                    svex-env-lookup-when-not-member
                                    ;; member-alist-keys-iff-svex-env-boundp
                                    )
                                   (svex-envs-agree-on-masks-necc))))))


  (local (defthm svex-envs-equivalent-by-agree-on-masks
           (implies (and (svex-envs-agree-on-masks (svexlist-mask-acons (svarlist->svexes (alist-keys (svex-env-fix env1)))
                                                                        -1 nil)
                                                   env1 env2)
                         (set-equiv (alist-keys (svex-env-fix env1)) (alist-keys (svex-env-fix env2))))
                    (equal (svex-envs-equivalent env1 env2) t))
           :hints(("Goal" :in-theory (enable svex-envs-agree-on-masks-of-neg1s)))))

  (local (defthm svex-alist-reduce-of-svex-alist-keys
           (svex-alist-eval-equiv (svex-alist-reduce (svex-alist-keys x) x) x)
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))

  (local
   (defret composed-results-of-<fn>-correct-top
     :pre-bind ((masks (svexlist-mask-acons (svarlist->svexes (svex-alist-keys loop-updates)) -1 nil)))
     (b* ((spec-updates
           (svex-alist-maskcompose-iter-spec loop-updates masks loop-updates)))
       (implies (no-duplicatesp-equal (svex-alist-keys loop-updates))
                (svex-alist-eval-equiv new-updates spec-updates)))
     :hints (("goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))
             (and stable-under-simplificationp
                  (let ((env (acl2::find-call-lst 'svex-alist-eval-equiv-envs-equivalent-witness clause)))
                    `(:clause-processor (acl2::generalize-with-alist-cp clause '((,env . env))))))
             (and stable-under-simplificationp
                  '(:use ((:instance <fn>-agrees-with-spec
                           (orig-updates loop-updates)
                           (masks (svexlist-mask-acons (svarlist->svexes (svex-alist-keys loop-updates)) -1 nil))))
                    :in-theory (disable <fn>-agrees-with-spec))))))
  
  (defret netcomp-p-of-<fn>
    :pre-bind ((masks (svexlist-mask-acons (svarlist->svexes (svex-alist-keys loop-updates)) -1 nil)))
    (implies (no-duplicatesp-equal (svex-alist-keys loop-updates))
             (netcomp-p new-updates loop-updates)))

  (verify-guards svex-alist-maskcompose-iter))
