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

; (include-book "compose-theory-monotonicity")
(include-book "svex-lattice")

(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
;; (local (include-book "arithmetic/top" :Dir :system))
(local (include-book "alist-thms"))
;;(local (include-book "clause-processors/find-subterms" :dir :system))
;; (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (std::add-default-post-define-hook :fix))


;; (define svex-keys-bound-to-consts ((keys svarlist-p) (x svex-alist-p))
;;   (if (atom keys)
;;       t
;;     (and (let ((val (svex-lookup (car keys) x)))
;;            (and val
;;                 (svex-case val :quote)))
;;          (svex-keys-bound-to-consts (cdr keys) x)))
;;   ///
;;   (defthmd svex-lookup-when-keys-bound-to-consts
;;     (implies (and (svex-keys-bound-to-consts keys x)
;;                   (member-equal key keys))
;;              (and (svex-lookup key x)
;;                   (svex-case (svex-lookup key x) :quote)))))




(defthmd svex-alist-compose-when-svex-alist-constantp
  (implies (svex-alist-constantp x)
           (equal (svex-alist-compose x a)
                  (Svex-alist-fix x)))
  :hints(("Goal" :in-theory (enable svex-alist-compose svex-alist-fix svex-acons
                                    svex-alist-constantp)
          :induct t
          :expand ((svex-compose (cdar x) a)))))

(defthmd svex-alist-monotonic-p-when-svex-alist-constantp
  (implies (svex-alist-constantp x)
           (svex-alist-monotonic-p x))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-p
                                    svex-alist-constantp
                                    svex-alist-eval-when-svex-alist-constantp))))

(define svex-alist-constantp ((x svex-alist-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (svex-case (cdar x) :quote))
         (svex-alist-constantp (cdr x))))
  ///
  (defthmd svex-lookup-when-svex-alist-constantp
    (implies (and (svex-alist-constantp x)
                  (svex-lookup k x))
             (svex-case (svex-lookup k x) :quote))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defthmd svex-alist-compose-when-svex-alist-constantp
    (implies (svex-alist-constantp x)
             (equal (svex-alist-compose x a)
                    (Svex-alist-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-compose svex-alist-fix svex-acons)
            :induct t
            :expand ((svex-compose (cdar x) a)))))

  (defthm svex-alist-constantp-of-svex-alist-extract
    (implies (svex-alist-constantp x)
             (svex-alist-constantp (svex-alist-extract keys x)))
    :hints(("Goal" :in-theory (enable svex-alist-extract
                                      svex-lookup-when-svex-alist-constantp))))

  (defthmd svex-alist-eval-when-svex-alist-constantp
    (implies (and (syntaxp (not (equal env ''nil)))
                  (svex-alist-constantp x))
             (equal (svex-alist-eval x env)
                    (svex-alist-eval x nil)))
    :hints(("Goal" :in-theory (enable svex-alist-eval))))
  
  (local (in-theory (enable svex-alist-fix))))


;; Same as SVEX-ENV-TO-SUBST, blah.
(define svex-env-to-subst ((x svex-env-p))
  :verify-guards nil
  :returns (new-x svex-alist-p)
  (mbe :logic (if (atom x)
                  nil
                (if (not (mbt (and (consp (car x))
                                   (svar-p (caar x)))))
                    (svex-env-to-subst (cdr x))
                  (cons (cons (caar x) (svex-quote (cdar x)))
                        (svex-env-to-subst (cdr x)))))
       :exec x)
  ///
  (local (defthm svex-env-to-subst-id
           (implies (svex-env-p x)
                    (equal (svex-env-to-subst x) x))
           :hints(("Goal" :in-theory (enable svex-env-p svex-quote)))))
  (verify-guards svex-env-to-subst
    :hints(("Goal" :in-theory (enable svex-env-p svex-quote))))

  (defret svex-alist-constantp-of-<fn>
    (svex-alist-constantp new-x)
    :hints(("Goal" :in-theory (enable svex-alist-constantp))))

  (defret lookup-of-svex-env-to-subst
    (equal (svex-lookup k new-x)
           (and (svex-env-boundp k x)
                (svex-quote (svex-env-lookup k x))))
    :hints(("Goal" :in-theory (enable svex-env-boundp svex-lookup svex-env-lookup))))

  (defret svex-alist-eval-of-<fn>
    (equal (svex-alist-eval new-x env)
           (svex-env-fix x))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-fix))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys new-x)
           (alist-keys (svex-env-fix x)))
    :hints(("Goal" :in-theory (enable alist-keys svex-env-fix svex-alist-keys))))

  (local (in-theory (enable svex-env-fix))))

(local (defthm svex-lookup-when-member-key-subset
         (implies (and (subsetp-equal keys (svex-alist-keys x))
                       (member-equal key keys))
                  (svex-lookup key x))))


(local (defthm svex-compose-with-constant-alist
         (equal (svex-eval (svex-compose x (svex-env-to-subst env1)) env)
                (svex-eval x (append env1 env)))))





(local (Defthm svex-envs-similar-of-append-extract
         (svex-envs-similar (append (svex-env-extract keys env) env)
                            env)
         :hints(("Goal" :in-theory (enable svex-envs-similar)))))

(local (defthm consp-hons-assoc-equal
         (iff (consp (hons-assoc-equal k x))
              (hons-assoc-equal k x))))

(local (defthm member-svex-env-keys
         (iff (member-equal k (alist-keys (svex-env-fix x)))
              (and (svar-p k)
                   (hons-assoc-equal k x)))
         :hints(("Goal" :in-theory (enable svex-env-fix alist-keys)))))

(defsection svex-partial-monotonic
  (defun-sk svex-partial-monotonic (param-keys x)
    (forall setting
            (implies (and (svex-alist-constantp setting)
                          (subsetp (svarlist-fix param-keys) (svex-alist-keys setting)))
                     (svex-monotonic-p (svex-compose x setting))))
    :rewrite :direct)

  (in-theory (disable svex-partial-monotonic
                      svex-partial-monotonic-necc))

  (defthm eval-when-svex-partial-monotonic
    (implies (and (svex-partial-monotonic param-keys x)
                  (equal (svex-env-extract param-keys env1)
                         (svex-env-extract param-keys env2))
                  (svex-env-<<= env1 env2))
             (4vec-<<= (svex-eval x env1) (svex-eval x env2)))
    :hints (("goal" :use ((:instance svex-partial-monotonic-necc
                           (setting (svex-env-to-subst
                                     (svex-env-extract param-keys env1))))
                          (:instance svex-monotonic-p-necc
                           (x (svex-compose x (svex-env-to-subst
                                               (svex-env-extract param-keys env1))))
                           (env1 env1) (env2 env2))))))


  ;; (forall (setting env1 env2)
  ;;         (implies (and (svex-alist-constantp setting)
  ;;                       (subsetp (svarlist-fix param-keys) (svex-alist-keys setting))
  ;;                       (svex-env-<<= env1 env2))
  ;;                  (4vec-<<= (svex-eval x (append (svex-alist-eval setting nil) env1))
  ;;                            (svex-eval x (append (svex-alist-eval setting nil) env2)))
  

  
  (defun svex-partial-monotonic-eval-witness (param-keys x)
    (b* ((setting (svex-partial-monotonic-witness param-keys x))
         (compose (svex-compose x setting))
         ((mv env1 env2)
          (svex-monotonic-p-witness compose))
         (setting-ev (svex-alist-eval setting nil)))
      (mv (append setting-ev env1)
          (append setting-ev env2))))

  (local (defthm svex-env-extract-append-when-subset-of-first
           (implies (subsetp-equal (svarlist-fix keys) (alist-keys (svex-env-fix a)))
                    (equal (svex-env-extract keys (append a b))
                           (svex-env-extract keys a)))
           :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix subsetp-equal svex-env-boundp)))))
  
  (defthm svex-partial-monotonic-by-eval
    (equal (svex-partial-monotonic param-keys x)
           (b* (((mv env1 env2) (svex-partial-monotonic-eval-witness param-keys x)))
             (or (not (equal (svex-env-extract param-keys env1)
                             (svex-env-extract param-keys env2)))
                 (not (svex-env-<<= env1 env2))
                 (4vec-<<= (svex-eval x env1) (svex-eval x env2)))))
    :hints(("Goal" :cases ((svex-partial-monotonic param-keys x)))
           (And stable-under-simplificationp
                '(:in-theory (enable svex-partial-monotonic svex-monotonic-p
                                     svex-alist-eval-when-svex-alist-constantp))))
    :rule-classes ((:definition :install-body nil)))

  (in-theory (disable svex-partial-monotonic-eval-witness svex-partial-monotonic-by-eval))
  

  (fty::deffixcong svarlist-equiv equal (svex-partial-monotonic param-keys x) param-keys
    :hints (("goal" :cases ((svex-partial-monotonic param-keys x))
             :expand ((:free (param-keys) (svex-partial-monotonic param-keys x)))
             :use ((:instance svex-partial-monotonic-necc
                    (param-keys param-keys)
                    (setting (svex-partial-monotonic-witness (svarlist-fix param-keys) x)))
                   (:instance svex-partial-monotonic-necc
                    (param-keys (svarlist-fix param-keys))
                    (setting (svex-partial-monotonic-witness param-keys x)))))))

  (defcong set-equiv equal (svex-partial-monotonic param-keys x) 1
    :hints (("goal" :cases ((svex-partial-monotonic param-keys x))
             :expand ((:free (param-keys) (svex-partial-monotonic param-keys x)))
             :use ((:instance svex-partial-monotonic-necc
                    (param-keys param-keys)
                    (setting (svex-partial-monotonic-witness param-keys-equiv x)))
                   (:instance svex-partial-monotonic-necc
                    (param-keys param-keys-equiv)
                    (setting (svex-partial-monotonic-witness param-keys x)))))))

  (defcong svex-eval-equiv equal (svex-partial-monotonic param-keys x) 2
    :hints (("goal" :cases ((svex-partial-monotonic param-keys x))
             :expand ((:free (x) (svex-partial-monotonic param-keys x)))
             :use ((:instance svex-partial-monotonic-necc
                    (param-keys param-keys) (x x)
                    (setting (svex-partial-monotonic-witness param-keys x-equiv)))
                   (:instance svex-partial-monotonic-necc
                    (param-keys param-keys) (x x-equiv)
                    (setting (svex-partial-monotonic-witness param-keys x))))))))


(defsection svexlist-partial-monotonic
  (defun-sk svexlist-partial-monotonic (param-keys x)
    (forall setting
            (implies (and (svex-alist-constantp setting)
                          (subsetp (svarlist-fix param-keys) (svex-alist-keys setting)))
                     (svexlist-monotonic-p (svexlist-compose x setting))))
    :rewrite :direct)

  (in-theory (disable svexlist-partial-monotonic
                      svexlist-partial-monotonic-necc))

  (defthm eval-when-svexlist-partial-monotonic
    (implies (and (svexlist-partial-monotonic param-keys x)
                  (equal (svex-env-extract param-keys env1)
                         (svex-env-extract param-keys env2))
                  (svex-env-<<= env1 env2))
             (4veclist-<<= (svexlist-eval x env1) (svexlist-eval x env2)))
    :hints (("goal" :use ((:instance svexlist-partial-monotonic-necc
                           (setting (svex-env-to-subst
                                     (svex-env-extract param-keys env1))))
                          (:instance svexlist-monotonic-p-necc
                           (x (svexlist-compose x (svex-env-to-subst
                                                   (svex-env-extract param-keys env1))))
                           (env1 env1) (env2 env2))))))


  (defun svexlist-partial-monotonic-eval-witness (param-keys x)
    (b* ((setting (svexlist-partial-monotonic-witness param-keys x))
         (compose (svexlist-compose x setting))
         ((mv env1 env2)
          (svexlist-monotonic-p-witness compose))
         (setting-ev (svex-alist-eval setting nil)))
      (mv (append setting-ev env1)
          (append setting-ev env2))))

  (local (defthm svex-env-extract-append-when-subset-of-first
           (implies (subsetp-equal (svarlist-fix keys) (alist-keys (svex-env-fix a)))
                    (equal (svex-env-extract keys (append a b))
                           (svex-env-extract keys a)))
           :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix subsetp-equal svex-env-boundp)))))
  
  (defthm svexlist-partial-monotonic-by-eval
    (equal (svexlist-partial-monotonic param-keys x)
           (b* (((mv env1 env2) (svexlist-partial-monotonic-eval-witness param-keys x)))
             (or (not (equal (svex-env-extract param-keys env1)
                             (svex-env-extract param-keys env2)))
                 (not (svex-env-<<= env1 env2))
                 (4veclist-<<= (svexlist-eval x env1) (svexlist-eval x env2)))))
    :hints(("Goal" :cases ((svexlist-partial-monotonic param-keys x)))
           (And stable-under-simplificationp
                '(:in-theory (enable svexlist-partial-monotonic svexlist-monotonic-p
                                     svex-alist-eval-when-svex-alist-constantp))))
    :rule-classes ((:definition :install-body nil)))

  (in-theory (disable svexlist-partial-monotonic-eval-witness svexlist-partial-monotonic-by-eval))
  
  (fty::deffixcong svarlist-equiv equal (svexlist-partial-monotonic param-keys x) param-keys
    :hints (("goal" :cases ((svexlist-partial-monotonic param-keys x))
             :expand ((:free (param-keys) (svexlist-partial-monotonic param-keys x)))
             :use ((:instance svexlist-partial-monotonic-necc
                    (param-keys param-keys)
                    (setting (svexlist-partial-monotonic-witness (svarlist-fix param-keys) x)))
                   (:instance svexlist-partial-monotonic-necc
                    (param-keys (svarlist-fix param-keys))
                    (setting (svexlist-partial-monotonic-witness param-keys x)))))))

  (defcong set-equiv equal (svexlist-partial-monotonic param-keys x) 1
    :hints (("goal" :cases ((svexlist-partial-monotonic param-keys x))
             :expand ((:free (param-keys) (svexlist-partial-monotonic param-keys x)))
             :use ((:instance svexlist-partial-monotonic-necc
                    (param-keys param-keys)
                    (setting (svexlist-partial-monotonic-witness param-keys-equiv x)))
                   (:instance svexlist-partial-monotonic-necc
                    (param-keys param-keys-equiv)
                    (setting (svexlist-partial-monotonic-witness param-keys x)))))))

  ;; doesn't belong here
  (defcong svexlist-eval-equiv svexlist-eval-equiv (svexlist-compose x a) 1
    :hints (("goal" :Expand ((svexlist-eval-equiv (svexlist-compose x a) (svexlist-compose x-equiv a))))))
  
  (defcong svexlist-eval-equiv equal (svexlist-partial-monotonic param-keys x) 2
    :hints (("goal" :cases ((svexlist-partial-monotonic param-keys x))
             :expand ((:free (x) (svexlist-partial-monotonic param-keys x)))
             :use ((:instance svexlist-partial-monotonic-necc
                    (param-keys param-keys) (x x)
                    (setting (svexlist-partial-monotonic-witness param-keys x-equiv)))
                   (:instance svexlist-partial-monotonic-necc
                    (param-keys param-keys) (x x-equiv)
                    (setting (svexlist-partial-monotonic-witness param-keys x))))))))


(defsection svex-constantp
  (defun-sk svex-constantp (x)
    (forall env
            (implies (syntaxp (not (equal env ''nil)))
                     (equal (svex-eval x env)
                            (svex-eval x nil))))
    :rewrite :direct)

  (in-theory (disable svex-constantp
                      svex-constantp-necc))

  (defthm svex-constantp-when-quote
    (implies (svex-case x :quote)
             (svex-constantp x))
    :hints(("Goal" :in-theory (enable svex-constantp))))

  (defthmd svex-compose-when-svex-constantp
    (implies (svex-constantp x)
             (svex-eval-equiv (svex-compose x a) x))
    :hints(("Goal" :in-theory (enable svex-eval-equiv
                                      svex-constantp-necc)))))

;; Sufficient condition for composition to preserve partial monotonicity.
;; This is implied by (not (intersectp-equal (svarlist-fix keys) (svex-alist-keys x))).
(define svex-compose-alist-const/selfbound-keys-p ((keys svarlist-p)
                                                   (x svex-alist-p))
  (if (atom keys)
      t
    (and (let ((look (svex-compose-lookup (car keys) x)))
           (or (ec-call (svex-eval-equiv look (svex-var (car keys))))
               (ec-call (svex-constantp look))))
         (svex-compose-alist-const/selfbound-keys-p (cdr keys) x)))
  ///
  (defthmd svex-compose-lookup-when-svex-compose-alist-const/selfbound-keys-p
    (implies (and (svex-compose-alist-const/selfbound-keys-p keys x)
                  (member-equal (svar-fix k) (svarlist-fix keys))
                  (case-split (not (svex-constantp (svex-compose-lookup k x)))))
             (svex-eval-equiv (svex-compose-lookup k x) (svex-var k))))

  (defthmd svex-lookup-when-svex-compose-alist-const/selfbound-keys-p
    (implies (and (svex-compose-alist-const/selfbound-keys-p keys x)
                  (member-equal (svar-fix k) (svarlist-fix keys))
                  (case-split (svex-lookup k x))
                  (case-split (not (svex-constantp (Svex-lookup k x)))))
             (svex-eval-equiv (svex-lookup k x) (svex-var k)))))


(define svex-compose-alist-selfbound-keys-p ((keys svarlist-p)
                                             (x svex-alist-p))
  (if (atom keys)
      t
    (and (let ((look (svex-compose-lookup (car keys) x)))
           (ec-call (svex-eval-equiv look (svex-var (car keys)))))
         (svex-compose-alist-selfbound-keys-p (cdr keys) x)))
  ///
  (defthmd svex-compose-lookup-when-svex-compose-alist-selfbound-keys-p
    (implies (and (svex-compose-alist-selfbound-keys-p keys x)
                  (member-equal (svar-fix k) (svarlist-fix keys)))
             (svex-eval-equiv (svex-compose-lookup k x) (svex-var k))))

  (defthmd svex-lookup-when-svex-compose-alist-selfbound-keys-p
    (implies (and (svex-compose-alist-selfbound-keys-p keys x)
                  (member-equal (svar-fix k) (svarlist-fix keys))
                  (case-split (svex-lookup k x)))
             (svex-eval-equiv (svex-lookup k x) (svex-var k))))


  (defthm svex-compose-alist-const/selfbound-keys-p-when-selfbound-keys-p
    (implies (svex-compose-alist-selfbound-keys-p keys x)
             (svex-compose-alist-const/selfbound-keys-p keys x))
    :hints(("Goal" :in-theory (enable svex-compose-alist-const/selfbound-keys-p)))))

(defsection svex-alist-partial-monotonic
  (defun-sk svex-alist-partial-monotonic (param-keys x)
    (forall setting
            (implies (and (svex-alist-constantp setting)
                          (subsetp (svarlist-fix param-keys) (svex-alist-keys setting)))
                     (svex-alist-monotonic-p (svex-alist-compose x setting))))
    :rewrite :direct)

  (in-theory (disable svex-alist-partial-monotonic
                      svex-alist-partial-monotonic-necc))
  
  (defthm eval-when-svex-alist-partial-monotonic
    (implies (and (svex-alist-partial-monotonic param-keys x)
                  (equal (svex-env-extract param-keys env1)
                         (svex-env-extract param-keys env2))
                  (svex-env-<<= env1 env2))
             (svex-env-<<= (svex-alist-eval x env1) (svex-alist-eval x env2)))
    :hints (("goal" :use ((:instance svex-alist-partial-monotonic-necc
                           (setting (svex-env-to-subst
                                     (svex-env-extract param-keys env1))))
                          (:instance svex-alist-monotonic-p-necc
                           (x (svex-alist-compose x (svex-env-to-subst
                                                     (svex-env-extract param-keys env1))))
                           (env1 env1) (env2 env2))))))

  (defun svex-alist-partial-monotonic-eval-witness (param-keys x)
    (b* ((setting (svex-alist-partial-monotonic-witness param-keys x))
         (compose (svex-alist-compose x setting))
         ((mv env1 env2)
          (svex-alist-monotonic-p-witness compose))
         (setting-ev (svex-alist-eval setting nil)))
      (mv (append setting-ev env1)
          (append setting-ev env2))))

  (local (defthm svex-env-extract-append-when-subset-of-first
           (implies (subsetp-equal (svarlist-fix keys) (alist-keys (svex-env-fix a)))
                    (equal (svex-env-extract keys (append a b))
                           (svex-env-extract keys a)))
           :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix subsetp-equal svex-env-boundp)))))
  
  (defthm svex-alist-partial-monotonic-by-eval
    (equal (svex-alist-partial-monotonic param-keys x)
           (b* (((mv env1 env2) (svex-alist-partial-monotonic-eval-witness param-keys x)))
             (or (not (equal (svex-env-extract param-keys env1)
                             (svex-env-extract param-keys env2)))
                 (not (svex-env-<<= env1 env2))
                 (svex-env-<<= (svex-alist-eval x env1) (svex-alist-eval x env2)))))
    :hints(("Goal" :cases ((svex-alist-partial-monotonic param-keys x)))
           (And stable-under-simplificationp
                '(:in-theory (enable svex-alist-partial-monotonic svex-alist-monotonic-p
                                     svex-alist-eval-when-svex-alist-constantp))))
    :rule-classes ((:definition :install-body nil)))

  (in-theory (disable svex-alist-partial-monotonic-eval-witness svex-alist-partial-monotonic-by-eval))

  (defthm lookup-when-svex-alist-partial-monotonic
    (implies (svex-alist-partial-monotonic param-keys x)
             (svex-partial-monotonic param-keys (svex-lookup k x)))
    :hints(("Goal" :expand ((svex-partial-monotonic param-keys (svex-lookup k x))
                            (svex-partial-monotonic param-keys nil)
                            (:free (a) (svex-compose (svex-x) a)))
            :use ((:instance svex-alist-partial-monotonic-necc
                   (setting (svex-partial-monotonic-witness param-keys (svex-lookup k x))))
                  (:instance svex-monotonic-p-of-svex-lookup-when-svex-alist-monotonic-p
                   (x (svex-alist-compose x (svex-partial-monotonic-witness param-keys (svex-lookup k x)))))))))
  
  (defthm svex-compose-lookup-when-svex-alist-partial-monotonic
    (implies (svex-alist-partial-monotonic param-keys x)
             (svex-partial-monotonic param-keys (svex-compose-lookup k x)))
    :hints(("Goal" :expand ((svex-partial-monotonic param-keys (svex-lookup k x))
                            (svex-partial-monotonic param-keys (svex-var k))
                            (:free (a) (svex-compose (svex-var k) a)))
            :in-theory (enable svex-compose-lookup)
            :use ((:instance svex-alist-partial-monotonic-necc
                   (setting (svex-partial-monotonic-witness param-keys (svex-compose-lookup k x))))
                  (:instance svex-monotonic-p-of-svex-lookup-when-svex-alist-monotonic-p
                   (x (svex-alist-compose x (svex-partial-monotonic-witness param-keys (svex-compose-lookup k x)))))))))

  (fty::deffixcong svarlist-equiv equal (svex-alist-partial-monotonic param-keys x) param-keys
    :hints (("goal" :cases ((svex-alist-partial-monotonic param-keys x))
             :expand ((:free (param-keys) (svex-alist-partial-monotonic param-keys x)))
             :use ((:instance svex-alist-partial-monotonic-necc
                    (param-keys param-keys)
                    (setting (svex-alist-partial-monotonic-witness (svarlist-fix param-keys) x)))
                   (:instance svex-alist-partial-monotonic-necc
                    (param-keys (svarlist-fix param-keys))
                    (setting (svex-alist-partial-monotonic-witness param-keys x)))))))

  (defcong set-equiv equal (svex-alist-partial-monotonic param-keys x) 1
    :hints (("goal" :cases ((svex-alist-partial-monotonic param-keys x))
             :expand ((:free (param-keys) (svex-alist-partial-monotonic param-keys x)))
             :use ((:instance svex-alist-partial-monotonic-necc
                    (param-keys param-keys)
                    (setting (svex-alist-partial-monotonic-witness param-keys-equiv x)))
                   (:instance svex-alist-partial-monotonic-necc
                    (param-keys param-keys-equiv)
                    (setting (svex-alist-partial-monotonic-witness param-keys x)))))))

  ;; (local (defthm svex-alist-eval-equiv-of-append-extract-blah
  ;;          (implies (and (svex-compose-alist-const/selfbound-keys-p keys a)
  ;;                        (subsetp-equal (svarlist-fix keys) (svex-alist-keys w)))
  ;;                   (svex-alist-eval-equiv (append (svex-alist-extract keys w)
  ;;                                                  (svex-alist-compose a w)
  ;;                                                  w)
  ;;                                          (append (svex-alist-compose a w) w)))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
  ;;                                            svex-lookup-when-svex-compose-alist-const/selfbound-keys-p
  ;;                                            svex-compose-when-svex-constantp)
  ;;                  :expand ((:free (x a) (svex-compose (svex-var x) a)))))))

  (local (defthm svex-alist-monotonic-p-of-append
           (implies (and (svex-alist-monotonic-p x)
                         (svex-alist-monotonic-p y))
                    (svex-alist-monotonic-p (append x y)))
           :hints (("goal" :expand ((:with svex-alist-monotonic-in-terms-of-lookup
                                     (svex-alist-monotonic-p (append x y))))))))

  (local (defthm svex-alist-keys-of-svex-alist-extract
           (equal (svex-alist-keys (svex-alist-extract keys x))
                  (svarlist-fix keys))
           :hints(("Goal" :in-theory (enable svex-alist-extract svex-alist-keys)))))

  (local (defthm len-of-svex-env-extract
           (equal (len (svex-env-extract keys x))
                  (len keys))
           :hints(("Goal" :in-theory (enable svex-env-extract)))))

  (local (defun append-ind (a c)
           (if (atom a)
               c
             (append-ind (cdr a) (cdr c)))))
  
  (local (defthm equal-of-append
           (implies (equal (len a) (len c))
                    (equal (equal (append a b) (append c d))
                           (and (equal (true-list-fix a) (true-list-fix c))
                                (equal b d))))
           :hints(("Goal" :in-theory (enable true-list-fix)
                   :induct (append-ind a c)))))

  (local (defthm svex-env-extract-of-append-equivalents
           (implies (and (equal (svex-env-extract keys x) (svex-env-extract keys y))
                         (svex-compose-alist-const/selfbound-keys-p keys a))
                    (equal (equal (svex-env-extract keys (append (svex-alist-eval a x) x))
                                  (svex-env-extract keys (append (svex-alist-eval a y) y)))
                           t))
           :hints(("Goal" :in-theory (enable svex-env-extract
                                             svex-constantp-necc
                                             svex-compose-alist-const/selfbound-keys-p)
                   :induct t
                   :expand ((:free (v x) (svex-eval (svex-var v) x)))))))

  
  
  (defthm svex-compose-preserves-svex-partial-monotonic
    (implies (and (svex-partial-monotonic params x)
                  (svex-alist-partial-monotonic params2 a)
                  (svex-compose-alist-const/selfbound-keys-p params a))
             (svex-partial-monotonic (append params params2)
                                     (svex-compose x a)))
    :hints (("Goal" :expand ((:with svex-partial-monotonic-by-eval
                              (svex-partial-monotonic (append params params2)
                                                      (svex-compose x a))))
             :use ((:instance eval-when-svex-partial-monotonic
                    (param-keys params)
                    (env1 (let ((env (mv-nth 0 (svex-partial-monotonic-eval-witness
                                                (append params params2) (svex-compose x a)))))
                            (append (svex-alist-eval a env) env)))
                    (env2 (let ((env (mv-nth 1 (svex-partial-monotonic-eval-witness
                                                (append params params2) (svex-compose x a)))))
                            (append (svex-alist-eval a env) env))))
                   (:instance eval-when-svex-alist-partial-monotonic
                    (x a) (param-keys params2)
                    (env1 (mv-nth 0 (svex-partial-monotonic-eval-witness
                                     (append params params2) (svex-compose x a))))
                    (env2 (mv-nth 1 (svex-partial-monotonic-eval-witness
                                     (append params params2) (svex-compose x a))))))
             :in-theory (disable eval-when-svex-partial-monotonic
                                 eval-when-svex-alist-partial-monotonic)
             :do-not-induct t))
    :otf-flg t)

  (local (Defthm svexlist-compose-of-compose
           (svexlist-eval-equiv (svexlist-compose (svexlist-compose x a) b)
                                (svexlist-compose x (append (svex-alist-compose a b) b)))
           :hints(("Goal" :in-theory (enable svexlist-eval-equiv)))))

  (defcong svex-alist-eval-equiv svexlist-eval-equiv (svexlist-compose x a) 2
    :hints(("Goal" :in-theory (enable svexlist-eval-equiv))))
  
  (defthm svexlist-compose-preserves-svexlist-partial-monotonic
    (implies (and (svexlist-partial-monotonic params x)
                  (svex-alist-partial-monotonic params2 a)
                  (svex-compose-alist-const/selfbound-keys-p params a))
             (svexlist-partial-monotonic (append params params2)
                                         (svexlist-compose x a)))
    :hints (("Goal" :expand ((:with svexlist-partial-monotonic-by-eval
                              (svexlist-partial-monotonic (append params params2)
                                                      (svexlist-compose x a))))
             :use ((:instance eval-when-svexlist-partial-monotonic
                    (param-keys params)
                    (env1 (let ((env (mv-nth 0 (svexlist-partial-monotonic-eval-witness
                                                (append params params2) (svexlist-compose x a)))))
                            (append (svex-alist-eval a env) env)))
                    (env2 (let ((env (mv-nth 1 (svexlist-partial-monotonic-eval-witness
                                                (append params params2) (svexlist-compose x a)))))
                            (append (svex-alist-eval a env) env))))
                   (:instance eval-when-svex-alist-partial-monotonic
                    (x a) (param-keys params2)
                    (env1 (mv-nth 0 (svexlist-partial-monotonic-eval-witness
                                     (append params params2) (svexlist-compose x a))))
                    (env2 (mv-nth 1 (svexlist-partial-monotonic-eval-witness
                                     (append params params2) (svexlist-compose x a))))))
             :in-theory (disable eval-when-svexlist-partial-monotonic
                                 eval-when-svex-alist-partial-monotonic)
             :do-not-induct t)))

  (defthm svex-alist-compose-preserves-svex-alist-partial-monotonic
    (implies (and (svex-alist-partial-monotonic params x)
                  (svex-alist-partial-monotonic params2 a)
                  (svex-compose-alist-const/selfbound-keys-p params a))
             (svex-alist-partial-monotonic (append params params2)
                                           (svex-alist-compose x a)))
    :hints (("Goal" :expand ((:with svex-alist-partial-monotonic-by-eval
                              (svex-alist-partial-monotonic (append params params2)
                                                      (svex-alist-compose x a))))
             :use ((:instance eval-when-svex-alist-partial-monotonic
                    (param-keys params)
                    (env1 (let ((env (mv-nth 0 (svex-alist-partial-monotonic-eval-witness
                                                (append params params2) (svex-alist-compose x a)))))
                            (append (svex-alist-eval a env) env)))
                    (env2 (let ((env (mv-nth 1 (svex-alist-partial-monotonic-eval-witness
                                                (append params params2) (svex-alist-compose x a)))))
                            (append (svex-alist-eval a env) env))))
                   (:instance eval-when-svex-alist-partial-monotonic
                    (x a) (param-keys params2)
                    (env1 (mv-nth 0 (svex-alist-partial-monotonic-eval-witness
                                     (append params params2) (svex-alist-compose x a))))
                    (env2 (mv-nth 1 (svex-alist-partial-monotonic-eval-witness
                                     (append params params2) (svex-alist-compose x a))))))
             :in-theory (disable eval-when-svex-alist-partial-monotonic)
             :do-not-induct t)))
  
  (defcong svex-alist-eval-equiv equal (svex-alist-partial-monotonic param-keys x) 2
    :hints (("goal" :cases ((svex-alist-partial-monotonic param-keys x))
             :expand ((:free (x) (svex-alist-partial-monotonic param-keys x)))
             :use ((:instance svex-alist-partial-monotonic-necc
                    (param-keys param-keys) (x x)
                    (setting (svex-alist-partial-monotonic-witness param-keys x-equiv)))
                   (:instance svex-alist-partial-monotonic-necc
                    (param-keys param-keys) (x x-equiv)
                    (setting (svex-alist-partial-monotonic-witness param-keys x))))))))
                                  
