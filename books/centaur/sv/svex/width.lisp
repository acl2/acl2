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

(include-book "alist-equiv")
(include-book "std/util/define-sk" :dir :system)
(local (include-book "alist-thms"))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable signed-byte-p)))
(local (std::add-default-post-define-hook :fix))



(define 4vec-width-p ((n posp) (x 4vec-p))
  (and (signed-byte-p (pos-fix n) (4vec->upper x))
       (signed-byte-p (pos-fix n) (4vec->lower x)))
  ///
  
  (local (defthm signed-byte-p-of-1
           (implies (and (posp n) (<= 2 n))
                    (signed-byte-p n 1))
           :hints(("Goal" :in-theory (enable signed-byte-p)))))

  (defthm 4vec-width-p-of-consts
    (and (4vec-width-p n (4vec-x))
         (4vec-width-p n (4vec-z))
         (4vec-width-p n 0)
         (4vec-width-p n -1)
         (implies (<= 2 (pos-fix n))
                  (and (4vec-width-p n (4vec-1x))
                       (4vec-width-p n (4vec-1z))
                       (4vec-width-p n 1))))
    :hints(("Goal" :in-theory (enable pos-fix))))

  (defthm 4vec-width-p-implies-greater
    (implies (and (4vec-width-p n x)
                  (<= (pos-fix n) (pos-fix m)))
             (4vec-width-p m x))))




(std::define-sk svex-width-limited-p ((width posp)
                                      (x svex-p))
  (forall env
          (4vec-width-p width (ec-call (svex-eval x env))))
  ///
  (defcong svex-eval-equiv equal (svex-width-limited-p width x) 2
    :hints (("goal" :use ((:instance svex-width-limited-p-necc
                           (x x-equiv)
                           (env (svex-width-limited-p-witness width x)))
                          (:instance svex-width-limited-p-necc
                           (x x)
                           (env (svex-width-limited-p-witness width x-equiv))))
             :in-theory (disable svex-width-limited-p-necc))))
  (local (defthm pos-fix-equal-forward
           (implies (equal (pos-fix x) (pos-fix y))
                    (pos-equiv x y))
           :rule-classes :forward-chaining))
  (defcong pos-equiv equal (svex-width-limited-p width x) 1
    :hints (("goal" :use ((:instance svex-width-limited-p-necc
                           (width width-equiv)
                           (env (svex-width-limited-p-witness width x)))
                          (:instance svex-width-limited-p-necc
                           (width width)
                           (env (svex-width-limited-p-witness width-equiv x))))
             :in-theory (e/d ()
                             (svex-width-limited-p-necc)))))

  (defthm svex-width-limited-p-implies-greater
    (implies (and (svex-width-limited-p width x)
                  (<= (pos-fix width) (pos-fix width2)))
             (svex-width-limited-p width2 x))
    :hints(("Goal" :use ((:instance svex-width-limited-p-necc
                          (width width)
                          (env (svex-width-limited-p-witness width2 x))))
            :in-theory (disable svex-width-limited-p-necc)))))

(std::define-sk svex-width-lower-boundp ((width posp)
                                         (x svex-p))
  (forall width2
          (implies (< (pos-fix width2) (pos-fix width))
                   (not (ec-call (svex-width-limited-p width2 x)))))
  ///
  (defcong svex-eval-equiv equal (svex-width-lower-boundp width x) 2
    :hints (("goal" :use ((:instance svex-width-lower-boundp-necc
                           (x x-equiv)
                           (width2 (svex-width-lower-boundp-witness width x)))
                          (:instance svex-width-lower-boundp-necc
                           (x x)
                           (width2 (svex-width-lower-boundp-witness width x-equiv))))
             :in-theory (disable svex-width-lower-boundp-necc))))
  (local (defthm pos-fix-equal-forward
           (implies (equal (pos-fix x) (pos-fix y))
                    (pos-equiv x y))
           :rule-classes :forward-chaining))
  (defcong pos-equiv equal (svex-width-lower-boundp width x) 1
    :hints (("goal" :use ((:instance svex-width-lower-boundp-necc
                           (width width-equiv)
                           (width2 (svex-width-lower-boundp-witness width x)))
                          (:instance svex-width-lower-boundp-necc
                           (width width)
                           (width2 (svex-width-lower-boundp-witness width-equiv x))))
             :in-theory (e/d ()
                             (svex-width-lower-boundp-necc)))))

  (defthm svex-width-lower-boundp-of-1
    (svex-width-lower-boundp 1 x))

  (defthm svex-width-lower-boundp-when-not-svex-width-limited-p-of-decrement
    (implies (not (svex-width-limited-p (+ -1 (pos-fix width)) x))
             (svex-width-lower-boundp width x))))




(defsection svex-width
  (defchoose svex-width-choose (width) (x)
    (svex-width-limited-p width x))

  (local (defthm posp-decr
           (implies (and (posp x)
                         (not (equal x 1)))
                    (posp (+ -1 x)))))
  
  (define minimize-svex-width ((known-width posp)
                               (x svex-p))
    :non-executable t
     :measure (pos-fix known-width)
    (if (eql (pos-fix known-width) 1)
        1
      (if (svex-width-limited-p (+ -1 (pos-fix known-width)) x)
          (minimize-svex-width (+ -1 (pos-fix known-width)) x)
        (pos-fix known-width)))
    ///
    (defthm minimize-svex-width-lower-boundp
      (svex-width-lower-boundp (minimize-svex-width known-width x) x))

    (defthm svex-width-limited-p-of-minimize-svex-width
      (implies (svex-width-limited-p known-width x)
               (svex-width-limited-p (minimize-svex-width known-width x) x)))

    (deffixequiv minimize-svex-width)

    (defthm minimize-svex-width-bound
      (<= (minimize-svex-width width x) (pos-fix width))
      :rule-classes :linear)
    
    (defthm minimize-svex-width-unique
      (implies (and (svex-width-limited-p width x)
                    (svex-width-lower-boundp width x)
                    (<= (pos-fix width) (pos-fix known-width)))
               (equal (minimize-svex-width known-width x) (pos-fix width)))
      :hints(("Goal" :in-theory (enable svex-width-lower-boundp-necc))))

    (defcong svex-eval-equiv equal (minimize-svex-width known-width x) 2))

  (define svex-width ((x svex-p))
    :non-executable t
    :returns (width maybe-posp :rule-classes :type-prescription)
    (b* ((w (pos-fix (svex-width-choose x))))
      (and (svex-width-limited-p w x)
           (minimize-svex-width w x)))
    ///
    (defthm not-limited-p-when-not-svex-width
      (implies (not (svex-width x))
               (not (svex-width-limited-p width x)))
      :hints (("goal" :use svex-width-choose)))

    (defthm svex-width-when-limited
      (implies (svex-width x)
               (and (svex-width-limited-p (svex-width x) x)
                    (svex-width-lower-boundp (svex-width x) x))))

    (defthmd svex-width-unique
      (implies (and (svex-width-limited-p width x)
                    (svex-width-lower-boundp width x))
               (equal (svex-width x) (pos-fix width)))
      :hints (("goal" :use not-limited-p-when-not-svex-width
               :in-theory (enable svex-width-lower-boundp-necc)
               :cases ((<= (pos-fix width) (pos-fix (svex-width-choose x)))))))
    
    (local (defthm pos-fix-equal-forward
             (implies (equal (pos-fix x) (pos-fix y))
                      (pos-equiv x y))
             :rule-classes :forward-chaining))
  
    (defcong svex-eval-equiv equal (svex-width x) 1
      :hints (("goal" :in-theory (e/d (svex-width)
                                      (minimize-svex-width-unique))
               :use ((:instance svex-width-choose (width (svex-width-choose x-equiv)))
                     (:instance svex-width-choose (x x-equiv) (width (svex-width-choose x)))
                     (:instance minimize-svex-width-unique
                      (x x) (width (minimize-svex-width (svex-width-choose x-equiv) x))
                      (known-width (svex-width-choose x)))
                     (:instance minimize-svex-width-unique
                      (x x-equiv) (width (minimize-svex-width (svex-width-choose x) x))
                      (known-width (svex-width-choose x-equiv))))
               :cases ((< (pos-fix (svex-width-choose x)) (pos-fix (svex-width-choose x-equiv)))
                       (< (pos-fix (svex-width-choose x-equiv)) (pos-fix (svex-width-choose x)))))))

    (defthm 4vec-width-p-of-svex-width-eval
      (implies (svex-width x)
               (4vec-width-p (svex-width x) (svex-eval x env)))
      :hints (("goal" :use svex-width-when-limited
               :in-theory (e/d (svex-width-limited-p-necc)
                               (svex-width-when-limited)))))))


(fty::defmap svar-width-map :key-type svar :val-type posp :true-listp t)




(define svex-env-width-limited-p-aux ((widths svar-width-map-p)
                                      (x svex-env-p))
  :returns (limitedp)
  (if (atom x)
      t
    (and (if (mbt (and (consp (car x))
                       (svar-p (caar x))))
             (b* ((width (cdr (hons-get (caar x) (svar-width-map-fix widths)))))
               (and width
                    (4vec-width-p width (cdar x))))
           t)
         (svex-env-width-limited-p-aux widths (cdr x))))
  ///
  (defret 4vec-width-p-lookup-when-<fn>
    (implies limitedp
             (b* ((width (cdr (hons-assoc-equal (svar-fix var) (svar-width-map-fix widths)))))
               (4vec-width-p width (svex-env-lookup var x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (defret keys-subset-of-widths-when-<fn>
    (implies limitedp
             (subsetp-equal (alist-keys (svex-env-fix x))
                            (alist-keys (svar-width-map-fix widths))))
    :hints(("Goal" :in-theory (enable alist-keys svex-env-fix))))
  
  (local (in-theory (enable svex-env-fix))))

(define svex-env-width-limited-p-aux-badguy ((widths svar-width-map-p)
                                             (x svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (b* ((width (cdr (hons-get (caar x) (svar-width-map-fix widths)))))
          (if (and width
                   (4vec-width-p width (cdar x)))
              (svex-env-width-limited-p-aux-badguy widths (cdr x))
            (caar x)))
      (svex-env-width-limited-p-aux-badguy widths (cdr x))))
  ///
  (defret boundp-when-<fn>
    (implies badguy
             (svex-env-boundp badguy x))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))
  
  (defret 4vec-width-p-when-<fn>
    (implies (and badguy
                  (no-duplicatesp-equal (alist-keys (svex-env-fix x))))
             (b* ((width (cdr (hons-assoc-equal badguy (svar-width-map-fix widths)))))
               (implies width
                        (not (4vec-width-p width (svex-env-lookup badguy x))))))
    :hints(("Goal" :in-theory (enable svex-env-lookup alist-keys svex-env-fix)
            :induct t)
           (and stable-under-simplificationp
                '(:use boundp-when-<fn>
                  :in-theory (e/d (svex-env-boundp)
                                  (boundp-when-<fn>))))))

  (defret svex-env-width-limited-p-aux-when-not-badguy
    (implies (not badguy)
             (svex-env-width-limited-p-aux widths x))
    :hints(("Goal" :in-theory (enable svex-env-width-limited-p-aux))))

  (defret svex-env-width-limited-p-aux-when-badguy
    (implies badguy
             (not (svex-env-width-limited-p-aux widths x)))
    :hints(("Goal" :in-theory (enable svex-env-width-limited-p-aux))))

  (local (in-theory (enable svex-env-fix))))
  
(local (in-theory (disable fast-alist-clean)))

(local (defthm no-duplicate-keys-of-fast-alist-fork
         (implies (no-duplicatesp-equal (alist-keys y))
                  (no-duplicatesp-equal (alist-keys (fast-alist-fork x y))))
         :hints(("Goal" :in-theory (enable fast-alist-fork alist-keys)))))

(local (defthm no-duplicate-keys-of-fast-alist-clean
         (no-duplicatesp-equal (alist-keys (fast-alist-clean x)))
         :hints(("Goal" :in-theory (enable fast-alist-clean alist-keys)))))

(define svex-env-width-limited-p-badguy ((widths svar-width-map-p)
                                         (x svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (svex-env-width-limited-p-aux-badguy widths (fast-alist-clean (svex-env-fix x)))
  ///
  (defret 4vec-width-p-when-<fn>
    (implies (and badguy)
             (b* ((width (cdr (hons-assoc-equal badguy (svar-width-map-fix widths)))))
               (implies width
                        (not (4vec-width-p width (svex-env-lookup badguy x))))))
    :hints(("Goal" :use ((:instance 4vec-width-p-when-svex-env-width-limited-p-aux-badguy
                          (x (fast-alist-clean (svex-env-fix x)))))
            :in-theory (disable 4vec-width-p-when-svex-env-width-limited-p-aux-badguy))))

  (defret boundp-when-<fn>
    (implies badguy
             (svex-env-boundp badguy x))
    :hints(("Goal" :use ((:instance boundp-when-svex-env-width-limited-p-aux-badguy
                          (x (fast-alist-clean (svex-env-fix x)))))
            :in-theory (disable boundp-when-svex-env-width-limited-p-aux-badguy)))))

(local (defthm alist-keys-fast-alist-clean-under-set-equiv
         (set-equiv (alist-keys (fast-alist-clean x))
                    (alist-keys x))
         :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-correct)))))


(define svex-env-width-limited-p ((widths svar-width-map-p)
                                  (x svex-env-p))
  :returns (limitedp)
  (svex-env-width-limited-p-aux widths (fast-alist-clean (svex-env-fix x)))
  ///
  (defret 4vec-width-p-lookup-when-<fn>
    (implies limitedp
             (b* ((width (cdr (hons-assoc-equal (svar-fix var) (svar-width-map-fix widths)))))
               (4vec-width-p width (svex-env-lookup var x))))
    :hints (("Goal" :use ((:instance 4vec-width-p-lookup-when-svex-env-width-limited-p-aux
                           (x (fast-alist-clean (svex-env-fix x)))))
             :in-theory (disable 4vec-width-p-lookup-when-svex-env-width-limited-p-aux))))


  
  (defret keys-subset-of-widths-when-<fn>
    (implies limitedp
             (subsetp-equal (alist-keys (svex-env-fix x))
                            (alist-keys (svar-width-map-fix widths))))
    :hints (("goal" :use ((:instance keys-subset-of-widths-when-svex-env-width-limited-p-aux
                           (x (fast-alist-clean (svex-env-fix x))))))))

  (local (defretd lookup-in-x-implies-lookup-in-widths-when-<fn>
           (implies (and limitedp
                         (svex-env-boundp k x)
                         (svar-p k))
                    (hons-assoc-equal k widths))
           :hints (("Goal" :in-theory (e/d (svex-env-boundp)
                                           (acl2::subsetp-member
                                            svex-env-width-limited-p))
                    :use ((:instance acl2::subsetp-member
                           (a k)
                           (x (alist-keys (svex-env-fix x)))
                           (y (alist-keys (svar-width-map-fix widths)))))))))
  
  (local (in-theory (enable svex-env-width-limited-p-badguy)))
  
  (defret <fn>-by-badguy
    (implies (not (svex-env-width-limited-p-badguy widths x))
             (svex-env-width-limited-p widths x)))

  (defret badguy-when-not-<fn>
    (implies (not (svex-env-width-limited-p widths x))
             (svex-env-width-limited-p-badguy widths x)))

  (defret <fn>-when-badguy
    (implies (svex-env-width-limited-p-badguy widths x)
             (not (svex-env-width-limited-p widths x)))
    :hints (("goal" :use 4vec-width-p-when-svex-env-width-limited-p-badguy
             :in-theory (disable 4vec-width-p-when-svex-env-width-limited-p-badguy))))

  

  (defcong svex-envs-equivalent equal (svex-env-width-limited-p widths x) 2
    :hints(("Goal" :in-theory (e/d () (svex-env-width-limited-p))
            :cases ((svex-env-width-limited-p widths x)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'svex-env-width-limited-p clause))
                     (?lit-x (caddr lit))
                     (?other-x (if (eq lit-x 'x) 'x-equiv 'x))
                     (?wit `(svex-env-width-limited-p-badguy . ,(cdr lit))))
                  `(:use ((:instance 4vec-width-p-when-svex-env-width-limited-p-badguy
                           (x ,lit-x))
                          (:instance lookup-in-x-implies-lookup-in-widths-when-svex-env-width-limited-p
                           (x ,other-x) (k ,wit))
                          (:instance boundp-when-svex-env-width-limited-p-badguy
                           (x ,lit-x))
                          (:instance 4vec-width-p-lookup-when-svex-env-width-limited-p
                           (x ,other-x) (var ,wit)))
                    :in-theory (disable svex-env-width-limited-p
                                        svex-env-width-limited-p-badguy
                                        4vec-width-p-lookup-when-svex-env-width-limited-p
                                        4vec-width-p-when-svex-env-width-limited-p-badguy
                                        boundp-when-svex-env-width-limited-p-badguy
                                        )))))))



;; (std::define-sk svex-alist-width-limited-p ((widths svar-width-map-p)
;;                                             (x svex-alist-p))
;;   :Returns (limitedp)
;;   (forall key
;;           (b* ((width (cdr (hons-assoc-equal (ec-call (svar-fix key)) (svar-width-map-fix widths))))
;;                (expr (ec-call (svex-lookup key x))))
;;             (implies expr
;;                      (and width
;;                           (svex-width-limited-p width expr)))))
;;   ///

;;   (local (in-theory (disable svex-alist-width-limited-p
;;                              svex-alist-width-limited-p-necc)))
  
;;   (defthm svex-env-width-limited-p-of-eval-when-svex-alist-width-limted-p
;;     (implies (svex-alist-width-limited-p widths x)
;;              (svex-env-width-limited-p widths (svex-alist-eval x env)))
;;     :hints (("Goal" :use ((:instance svex-alist-width-limited-p-necc
;;                            (key (svex-env-width-limited-p-badguy widths (svex-alist-eval x env))))
;;                           (:instance 4vec-width-p-when-svex-env-width-limited-p-badguy
;;                            (x (svex-alist-eval x env)))
;;                           (:instance boundp-when-svex-env-width-limited-p-badguy
;;                            (x (svex-alist-eval x env))))
;;              :in-theory (e/d (svex-width-limited-p-necc)
;;                              (4vec-width-p-when-svex-env-width-limited-p-badguy
;;                               boundp-when-svex-env-width-limited-p-badguy)))))

;;   (defcong svex-alist-eval-equiv equal (svex-alist-width-limited-p widths x) 2
;;     :hints (("goal" :cases ((svex-alist-width-limited-p widths x)))
;;             (and stable-under-simplificationp
;;                  (b* ((lit (assoc 'svex-alist-width-limited-p clause))
;;                       (wit `(svex-alist-width-limited-p-witness . ,(cdr lit)))
;;                       (lit-x (caddr lit))
;;                       (other-x (if (Eq lit-x 'x) 'x-equiv 'x)))
;;                    `(:expand (,lit)
;;                      :use ((:instance svex-alist-width-limited-p-necc
;;                             (x ,other-x) (key ,wit)))))))))




(local (defthm svex-alist-removekey-when-eval-equiv
         (implies (and (svex-alist-eval-equiv x y)
                       (svex-alist-p x)
                       (consp x)
                       (no-duplicatesp-equal (svex-alist-keys x)))
                  (svex-alist-eval-equiv
                   (svex-alist-removekeys (list (caar x)) y)
                   (cdr x)))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                           svex-lookup-redef
                                           svex-alist-keys)))))

(local (defun svex-alist-removekeys-equiv-ind (x y)
         (declare (Xargs :measure (len x)))
         (if (atom x)
             y
           (svex-alist-removekeys-equiv-ind
            (cdr x)
            (if (and (consp (car x))
                     (svar-p (caar x)))
                (svex-alist-removekeys (list (caar x)) y)
              y)))))

(local (defthm svex-alist-eval-equiv-of-cdr-when-bad-car
         (implies (or (not (consp (car x)))
                      (not (svar-p (caar x))))
                  (svex-alist-eval-equiv (cdr x) x))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                           svex-lookup-redef)))))
  

(local (defthm no-duplicatesp-set-diff
         (implies (no-duplicatesp-equal x)
                  (no-duplicatesp-equal (set-difference-equal x y)))
         :hints(("Goal" :in-theory (enable set-difference-equal)))))



(define svex-alist-width-limited-p-aux ((widths svar-width-map-p)
                                        (x svex-alist-p))
  :returns (limitedp)
  (if (atom x)
      t
    (and (if (mbt (and (consp (car x))
                       (svar-p (caar x))))
             (b* ((width (cdr (hons-get (caar x) (svar-width-map-fix widths)))))
               (and width (svex-width-limited-p width (cdar x))))
           t)
         (svex-alist-width-limited-p-aux widths (cdr x))))
  ///

  (defret svex-env-width-limited-p-aux-of-eval-when-<fn>
    (implies limitedp
             (svex-env-width-limited-p-aux widths (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-width-limited-p-aux svex-alist-eval
                                      svex-width-limited-p-necc))))

  (deffixequiv svex-alist-width-limited-p-aux
    :hints(("Goal" :in-theory (enable svex-alist-fix))))

  (local
   (defthmd svex-alist-width-limited-p-aux-of-removekey
     (implies (and (no-duplicatesp-equal (svex-alist-keys x))
                   (svex-lookup k x))
              (equal (svex-alist-width-limited-p-aux widths x)
                     (and (svex-alist-width-limited-p-aux widths (svex-alist-removekeys (list k) x))
                          (hons-get (svar-fix k) (svar-width-map-fix widths))
                          (svex-width-limited-p
                           (cdr (hons-get (svar-fix k) (svar-width-map-fix widths)))
                           (svex-lookup k x)))))
     :hints(("Goal" :in-theory (enable svex-alist-removekeys
                                       svex-alist-keys
                                       svex-lookup-redef)))))


  (local (defthm equal-x-svar-fix-x
           (equal (equal x (svar-fix x))
                  (svar-p x))))

  (local (defthm svex-alist-width-limited-p-aux-when-equiv-atom
           (implies (and (svex-alist-eval-equiv x y)
                         (not (consp x)))
                    (svex-alist-width-limited-p-aux widths y))
           :hints (("goal" :induct (svex-alist-width-limited-p-aux widths y))
                   '(:use ((:instance svex-alist-eval-equiv-necc
                            (var (caar y))))
                     :in-theory (e/d (svex-lookup-redef)
                                     (svex-alist-eval-equiv-necc
                                      svex-alist-same-keys-implies-iff-svex-lookup-2
                                      svex-alist-eval-equiv-implies-iff-svex-lookup-2))))))
  
  (defthmd svex-alist-width-limited-p-aux-eval-equiv-congruence-when-no-duplicate-keys
    (implies (and (svex-alist-eval-equiv x y)
                  (no-duplicatesp-equal (svex-alist-keys x))
                  (no-duplicatesp-equal (svex-alist-keys y)))
             (equal (svex-alist-width-limited-p-aux widths x)
                    (svex-alist-width-limited-p-aux widths y)))
    :hints (("goal" :induct (svex-alist-removekeys-equiv-ind x y)
             :in-theory (enable svex-alist-keys
                                svex-alist-removekeys
                                svex-lookup-redef))
            '(:use ((:instance svex-alist-width-limited-p-aux-of-removekey (x y)
                     (k (caar x)))))))
             
  (local (in-theory (enable svex-alist-fix))))

(defthm fast-alist-clean-under-svex-alist-eval-equiv
  (svex-alist-eval-equiv (fast-alist-clean x) x)
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))

(defthm no-duplicate-svex-alist-keys-of-fast-alist-fork
  (implies (and (no-duplicatesp-equal (svex-alist-keys y)))
           (no-duplicatesp-equal (svex-alist-keys (fast-alist-fork x y))))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup))))

(defthm svex-alist-keys-of-cdr-last
  (equal (svex-alist-keys (cdr (last x))) nil)
  :hints(("Goal" :in-theory (enable svex-alist-keys))))

(defthm no-duplicate-svex-alist-keys-of-fast-alist-clean
  (no-duplicatesp-equal (svex-alist-keys (fast-alist-clean x)))
  :hints(("Goal" :in-theory (enable fast-alist-clean
                                    svex-alist-keys))))
  



(define svex-alist-width-limited-p ((widths svar-width-map-p)
                                    (x svex-alist-p))
  :returns (limitedp)
  (svex-alist-width-limited-p-aux widths (fast-alist-clean (svex-alist-fix x)))
  ///
  (defret svex-env-width-limited-p-of-eval-when-<fn>
    (implies limitedp
             (svex-env-width-limited-p widths (svex-alist-eval x env)))
    :hints(("Goal" :use ((:instance svex-env-width-limited-p-aux-of-eval-when-svex-alist-width-limited-p-aux
                          (x (fast-alist-clean (svex-alist-fix x)))))
            :in-theory (e/d (svex-env-width-limited-p)
                            (svex-env-width-limited-p-aux-of-eval-when-svex-alist-width-limited-p-aux)))))

  (defcong svex-alist-eval-equiv equal (svex-alist-width-limited-p widths x) 2
    :hints (("goal" :use ((:instance svex-alist-width-limited-p-aux-eval-equiv-congruence-when-no-duplicate-keys
                           (x (fast-alist-clean (svex-alist-fix x)))
                           (y (fast-alist-clean (svex-alist-fix x-equiv))))))))

  
  (local (defthmd svex-alist-width-limited-p-is-aux-when-no-duplicate-keys
           (implies (no-duplicatesp-equal (svex-alist-keys x))
                    (equal (svex-alist-width-limited-p widths x)
                           (svex-alist-width-limited-p-aux widths x)))
           :hints (("goal" :use ((:instance
                                  svex-alist-width-limited-p-aux-eval-equiv-congruence-when-no-duplicate-keys
                                  (y (fast-alist-clean (svex-alist-fix x)))))))))

  (defthmd svex-alist-width-limited-p-rec-when-no-duplicate-keys
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal (svex-alist-width-limited-p widths x)
                    (if (atom x)
                        t
                      (and (if (mbt (and (consp (car x))
                                         (svar-p (caar x))))
                               (b* ((width (cdr (hons-get (caar x) (svar-width-map-fix widths)))))
                                 (and width (svex-width-limited-p width (cdar x))))
                             t)
                           (svex-alist-width-limited-p widths (cdr x))))))
    :hints(("Goal" :in-theory (e/d (svex-alist-width-limited-p-is-aux-when-no-duplicate-keys
                                    svex-alist-width-limited-p-aux
                                    svex-alist-keys)
                                   (svex-alist-width-limited-p))))
    :rule-classes ((:definition :controller-alist ((svex-alist-width-limited-p nil t))
                    :install-body nil))))


(local (defthm maybe-posp-fix-when-nonnil
         (implies x
                  (equal (acl2::maybe-posp-fix x) (pos-fix x)))
         :hints(("Goal" :in-theory (enable acl2::maybe-posp-fix
                                           pos-fix)))))

(local (defthm maybe-natp-fix-when-nonnil
         (implies x
                  (equal (acl2::maybe-natp-fix x) (nfix x)))
         :hints(("Goal" :in-theory (enable acl2::maybe-natp-fix
                                           nfix)))))

(define svex-width-sum ((x maybe-posp)
                        (y maybe-natp))
  :Returns (sum maybe-posp :rule-classes :type-prescription)
  (and x y (+ (lposfix x) (lnfix y)))
  ///
  (defthm svex-width-sum-of-nil
    (and (equal (svex-width-sum nil y) nil)
         (equal (svex-width-sum x nil) nil))))


            



(define svex-alist-width-aux ((x svex-alist-p))
  :returns (width maybe-natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (svex-width-sum (svex-width (cdar x))
                        (svex-alist-width-aux (cdr x)))
      (svex-alist-width-aux (cdr x))))
  ///
  (defthm svex-alist-width-aux-when-width-limited-p
    (implies (and (svex-alist-width-limited-p-aux widths x)
                  (no-duplicatesp-equal (svex-alist-keys x)))
             (svex-alist-width-aux x))
    :hints(("Goal" :in-theory (enable svex-width-sum
                                      svex-alist-keys
                                      svex-alist-width-limited-p-aux)
            :induct t)))


  (deffixequiv svex-alist-width-aux
    :hints(("Goal" :in-theory (enable svex-alist-fix))))
  
  (local (defthm equal-x-svar-fix-x
           (equal (equal x (svar-fix x))
                  (svar-p x))))


  (local
   (defthmd svex-alist-width-aux-of-removekey
     (implies (and (no-duplicatesp-equal (svex-alist-keys x))
                   (svex-lookup k x))
              (equal (svex-alist-width-aux x)
                     (and (svex-width (svex-lookup k x))
                          (svex-alist-width-aux (svex-alist-removekeys (list k) x))
                          (+ (svex-alist-width-aux (svex-alist-removekeys (list k) x))
                             (svex-width (svex-lookup k x))))))
     :hints(("Goal" :in-theory (enable svex-alist-removekeys
                                       svex-alist-keys
                                       svex-width-sum
                                       svex-lookup-redef)))))

  (local (defthm svex-alist-width-aux-when-equiv-atom
           (implies (and (svex-alist-eval-equiv x y)
                         (not (consp x)))
                    (equal (svex-alist-width-aux y) 0))
           :hints (("goal" :induct (svex-alist-width-aux y))
                   '(:use ((:instance svex-alist-eval-equiv-necc
                            (var (caar y))))
                     :in-theory (e/d (svex-lookup-redef)
                                     (svex-alist-eval-equiv-necc
                                      svex-alist-same-keys-implies-iff-svex-lookup-2
                                      svex-alist-eval-equiv-implies-iff-svex-lookup-2))))))
  
  (defthmd svex-alist-width-aux-eval-equiv-congruence-when-no-duplicate-keys
    (implies (and (svex-alist-eval-equiv x y)
                  (no-duplicatesp-equal (svex-alist-keys x))
                  (no-duplicatesp-equal (svex-alist-keys y)))
             (equal (svex-alist-width-aux x)
                    (svex-alist-width-aux y)))
    :hints (("goal" :induct (svex-alist-removekeys-equiv-ind x y)
             :in-theory (enable svex-alist-keys
                                svex-alist-removekeys
                                svex-lookup-redef
                                svex-width-sum))
            '(:use ((:instance svex-alist-width-aux-of-removekey (x y)
                     (k (caar x)))))))
                       
                        
  (local (in-theory (enable svex-alist-fix))))

(define svex-alist-width ((x svex-alist-p))
  :returns (width maybe-natp :rule-classes :type-prescription)
  (svex-alist-width-aux (fast-alist-clean (svex-alist-fix x)))
  ///
  (local (defthmd svex-alist-width-is-aux-when-no-duplicate-keys
           (implies (no-duplicatesp-equal (svex-alist-keys x))
                    (equal (svex-alist-width x)
                           (svex-alist-width-aux x)))
           :hints (("goal" :use ((:instance
                                  svex-alist-width-aux-eval-equiv-congruence-when-no-duplicate-keys
                                  (y (fast-alist-clean (svex-alist-fix x)))))))))

  (defthmd svex-alist-width-rec-when-no-duplicate-keys
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal (svex-alist-width x)
                    (if (atom x)
                        0
                      (if (mbt (and (consp (car x))
                                    (svar-p (caar x))))
                          (svex-width-sum (svex-width (cdar x))
                                          (svex-alist-width (cdr x)))
                        (svex-alist-width (cdr x))))))
    :hints(("Goal" :in-theory (e/d (svex-alist-width-is-aux-when-no-duplicate-keys
                                    svex-alist-width-aux
                                    svex-alist-keys)
                                   (svex-alist-width))))
    :rule-classes ((:definition :controller-alist ((svex-alist-width t))
                    :install-body nil)))
  
  (defthm svex-alist-width-when-width-limited-p
    (implies (and (svex-alist-width-limited-p widths x))
             (svex-alist-width x))
    :hints(("Goal" :in-theory (enable svex-alist-width-limited-p))))

  (defcong svex-alist-eval-equiv equal (svex-alist-width x) 1
    :hints (("Goal" :use ((:instance svex-alist-width-aux-eval-equiv-congruence-when-no-duplicate-keys
                           (x (fast-alist-clean (svex-alist-fix x)))
                           (y (fast-alist-clean (svex-alist-fix x-equiv)))))))))


;; (define svex-alist-svar-width-map ((x svex-alist-p))
;;   :returns (map svar-width-map-p)
;;   (if (atom x)
;;       nil
;;     (if (mbt (and (consp (car x))
;;                   (svar-p (caar x))))
;;         (b* ((rest (svex-alist-svar-width-map (cdr x)))
;;              (width-look (hons-get (caar x) rest))
;;              (width (svex-width (cdar x))))
;;           (if width
;;               (cons (cons (caar x)
;;                           (if width-look
;;                               (max (cdr width-look) width)
;;                             width))
;;                     rest)
;;             rest))
;;       (svex-alist-svar-width-map (cdr x))))
;;   ///
;;   (local (defthm svex-alist-width-limited-p-when-cons-wider
;;            (implies (and (svex-alist-width-limited-p map x)
;;                          (or (not (hons-assoc-equal v (svar-width-map-fix map)))
;;                              (<= (cdr (hons-assoc-equal v (svar-width-map-fix map))) (pos-fix width))))
;;                     (svex-alist-width-limited-p
;;                      (cons (cons v width) map) x))
;;            :hints(("Goal" :in-theory (enable svex-alist-width-limited-p)))))
  
;;   (local (defthm svex-alist-width-limited-p-when-cons-wider
;;            (implies (and (svex-alist-width-limited-p map x)
;;                          (or (not (hons-assoc-equal v (svar-width-map-fix map)))
;;                              (<= (cdr (hons-assoc-equal v (svar-width-map-fix map))) (pos-fix width))))
;;                     (svex-alist-width-limited-p
;;                      (cons (cons v width) map) x))
;;            :hints(("Goal" :in-theory (enable svex-alist-width-limited-p)))))

;;   (local (defthm svex-width-limited-p-implies-greater-corr
;;            (implies (and (< width width2)
;;                          (posp width) (posp width2)
;;                          (svex-width-limited-p width x))
;;                     (svex-width-limited-p width2 x))))
  
;;   (defthm svex-alist-width-limited-p-when-svex-alist-width
;;     (implies (svex-alist-width x)
;;              (svex-alist-width-limited-p (svex-alist-svar-width-map x) x))
;;     :hints(("Goal" :in-theory (e/d (svex-alist-width svex-alist-width-limited-p
;;                                                      svex-width-sum))
;;             :induct t :do-not-induct t)))

;;   (local (in-theory (enable svex-alist-fix))))


