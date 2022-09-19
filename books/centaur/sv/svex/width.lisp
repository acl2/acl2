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

(include-book "svex-equivs")
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


(include-book "std/util/define-sk" :dir :system)


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

(define svex-env-width-limited-p ((widths svar-width-map-p)
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
         (svex-env-width-limited-p widths (cdr x))))
  ///
  (defret 4vec-width-p-lookup-when-<fn>
    (implies limitedp
             (b* ((width (cdr (hons-assoc-equal (svar-fix var) (svar-width-map-fix widths)))))
               (4vec-width-p width (svex-env-lookup var x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))
  
  (local (in-theory (enable svex-env-fix))))

(define svex-alist-width-limited-p ((widths svar-width-map-p)
                                    (x svex-alist-p))
  :returns (limitedp)
  (if (atom x)
      t
    (and (if (mbt (and (consp (car x))
                       (svar-p (caar x))))
             (b* ((width (cdr (hons-get (caar x) (svar-width-map-fix widths)))))
               (and width (svex-width-limited-p width (cdar x))))
           t)
         (svex-alist-width-limited-p widths (cdr x))))
  ///

  (defret svex-env-width-limited-p-of-eval-when-<fn>
    (implies limitedp
             (svex-env-width-limited-p widths (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-width-limited-p svex-alist-eval
                                      svex-width-limited-p-necc))))

  (local (in-theory (enable svex-alist-fix))))


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

(define svex-alist-width ((x svex-alist-p))
  :returns (width maybe-natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (svex-width-sum (svex-width (cdar x))
                        (svex-alist-width (cdr x)))
      (svex-alist-width (cdr x))))
  ///
  (defthm svex-alist-width-when-width-limited-p
    (implies (svex-alist-width-limited-p widths x)
             (svex-alist-width x))
    :hints(("Goal" :in-theory (enable svex-alist-width-limited-p svex-width-sum))))

  (local (in-theory (enable svex-alist-fix))))


(define svex-alist-svar-width-map ((x svex-alist-p))
  :returns (map svar-width-map-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (b* ((rest (svex-alist-svar-width-map (cdr x)))
             (width-look (hons-get (caar x) rest))
             (width (svex-width (cdar x))))
          (if width
              (cons (cons (caar x)
                          (if width-look
                              (max (cdr width-look) width)
                            width))
                    rest)
            rest))
      (svex-alist-svar-width-map (cdr x))))
  ///
  (local (defthm svex-alist-width-limited-p-when-cons-wider
           (implies (and (svex-alist-width-limited-p map x)
                         (or (not (hons-assoc-equal v (svar-width-map-fix map)))
                             (<= (cdr (hons-assoc-equal v (svar-width-map-fix map))) (pos-fix width))))
                    (svex-alist-width-limited-p
                     (cons (cons v width) map) x))
           :hints(("Goal" :in-theory (enable svex-alist-width-limited-p)))))

  (local (defthm svex-width-limited-p-implies-greater-corr
           (implies (and (< width width2)
                         (posp width) (posp width2)
                         (svex-width-limited-p width x))
                    (svex-width-limited-p width2 x))))
  
  (defthm svex-alist-width-limited-p-when-svex-alist-width
    (implies (svex-alist-width x)
             (svex-alist-width-limited-p (svex-alist-svar-width-map x) x))
    :hints(("Goal" :in-theory (e/d (svex-alist-width svex-alist-width-limited-p
                                                     svex-width-sum))
            :induct t :do-not-induct t)))

  (local (in-theory (enable svex-alist-fix))))


