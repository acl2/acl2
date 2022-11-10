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

(include-book "compose-theory-base")
(include-book "depends")
(local (include-book "alist-thms"))
(local (include-book "std/lists/sets" :dir :System))
(local (include-book "std/alists/alist-keys" :dir :System))
(local (std::add-default-post-define-hook :fix))


(defsection vars-of-neteval-ordering-compile


  (defthm-neteval-ordering-compile-flag
    (defthm svex-vars-of-non-network-of-neteval-ordering-compile
      (implies (and (not (svex-lookup v network))
                    (hons-assoc-equal (svar-fix v) (neteval-ordering-fix x))
                    (not (equal v2 (svar-fix v))))
               (not (member-equal v2 (svex-vars (svex-lookup v (neteval-ordering-compile x network))))))
      :hints ('(:expand ((neteval-ordering-compile x network))
                :in-theory (enable svex-lookup-of-cons)))
      :flag neteval-ordering-compile)

    (defthm svex-vars-of-non-network-of-neteval-sigordering-compile
      (implies (and (not (svex-lookup v network))
                    (not (equal v2 (svar-fix v)))
                    (svar-equiv signal v))
               (not (member-equal v2 (svex-vars (neteval-sigordering-compile x signal offset network)))))
      :hints ('(:expand ((neteval-sigordering-compile x signal offset network))))
      :flag neteval-sigordering-compile)

    (defthm svex-vars-of-non-network-of-neteval-ordering-or-null-compile
      (implies (and (not (svex-lookup v network))
                    (not (equal v2 (svar-fix v)))
                    (svar-equiv signal v))
               (not (member-equal v2 (svex-vars (neteval-ordering-or-null-compile x signal network)))))
      :hints ('(:expand ((neteval-ordering-or-null-compile x signal network)
                         (:free (a) (svex-compose (svex-var signal) a)))
                :in-theory (enable svex-compose-lookup)))
      :flag neteval-ordering-or-null-compile))

  (local (defthm svex-lookup-of-neteval-ordering-compile-under-iff
           (iff (svex-lookup var (neteval-ordering-compile ord network))
                (hons-assoc-equal (svar-fix var) (neteval-ordering-fix ord)))))

  (local (defthm not-var-of-lookup-when-not-var-of-reduce
           (implies (and (NOT (MEMBER-EQUAL V (SVEX-ALIST-VARS (SVEX-ALIST-REDUCE keys x))))
                         (member-equal (svar-fix key) (svarlist-fix keys)))
                    (NOT (MEMBER-EQUAL V (SVEX-VARS (SVEX-LOOKUP key x)))))
           :hints(("Goal" :in-theory (enable svex-alist-vars
                                             svex-alist-reduce
                                             svex-lookup-of-cons)))))

  
  (defthm-svex-vars-flag vars-of-svex-compose-neteval-ordering-compile
    (defthm vars-of-svex-compose-neteval-ordering-compile
      (implies (and (not (member-equal v (set-difference-equal (svex-vars x)
                                                               (intersection-equal (svex-alist-keys network)
                                                                                   (alist-keys (neteval-ordering-fix ord)))
                                                               )))
                    (not (member-equal v (svex-alist-vars (svex-alist-reduce (svex-alist-keys network)
                                                                             (neteval-ordering-compile ord network))))))
               (not (member-equal v (svex-vars (svex-compose x (neteval-ordering-compile ord network))))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (a) (svex-compose x a)))
                     :in-theory (disable svex-lookup-of-neteval-ordering-compile))))
      :flag svex-vars)
    (defthm vars-of-svexlist-compose-neteval-ordering-compile
      (implies (and (not (member-equal v (set-difference-equal (svexlist-vars x)
                                                               (intersection-equal (svex-alist-keys network)
                                                                                   (alist-keys (neteval-ordering-fix ord))))))
                    (not (member-equal v (svex-alist-vars (svex-alist-reduce (svex-alist-keys network)
                                                                             (neteval-ordering-compile ord network))))))
               (not (member-equal v (svexlist-vars (svexlist-compose x (neteval-ordering-compile ord network))))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (a) (svexlist-compose x a))))))
      :flag svexlist-vars))


  (local (defthm svex-alist-reduce-of-nil
           (equal (svex-alist-reduce vars nil) nil)
           :hints(("Goal" :in-theory (enable svex-alist-reduce)))))

  (local (defthm svex-alist-vars-of-svex-alist-reduce-cons
           (implies (and (not (and (svar-p var)
                                   (member-equal var (svarlist-fix vars))
                                   (member-equal v (svex-vars val))))
                         (not (member-equal v (svex-alist-vars (svex-alist-reduce vars rest)))))
                    (not (member-equal v (svex-alist-vars (svex-alist-reduce vars (cons (cons var val) rest))))))
           :hints(("Goal" :in-theory (enable svex-alist-vars svex-alist-reduce svarlist-fix
                                             svex-lookup-of-cons)))))

    
  (defthm-neteval-ordering-compile-flag
    (defthm member-svex-alist-vars-of-neteval-ordering-compile
      (implies (and (not (member-equal v (svex-alist-vars network)))
                    (not (member-equal v (svex-alist-keys network))))
               (not (member-equal v (svex-alist-vars (svex-alist-reduce (svex-alist-keys network)
                                                                        (neteval-ordering-compile x network))))))
      :hints ('(:expand ((neteval-ordering-compile x network))))
      :flag neteval-ordering-compile)

    (defthm member-svex-alist-vars-of-neteval-sigordering-compile
      (implies (and (not (member-equal v (svex-alist-vars network)))
                    (not (member-equal v (svex-alist-keys network)))
                    (not (svar-equiv v signal)))
               (not (member-equal v (svex-vars (neteval-sigordering-compile x signal offset network)))))
      :hints ('(:expand ((neteval-sigordering-compile x signal offset network))))
      :flag neteval-sigordering-compile)

    (defthm member-svex-alist-vars-of-neteval-ordering-or-null-compile
      (implies (and (not (member-equal v (svex-alist-vars network)))
                    (not (member-equal v (svex-alist-keys network)))
                    (not (svar-equiv v signal)))
               (not (member-equal v (svex-vars (neteval-ordering-or-null-compile x signal network)))))
      :hints ('(:expand ((neteval-ordering-or-null-compile x signal network))
                :in-theory (enable svex-compose-lookup)))
      :flag neteval-ordering-or-null-compile))
  
  )


;; (defsection deps-of-neteval-ordering-compile


;;   (defthm-neteval-ordering-compile-flag
;;     (defthm svex-deps-of-non-network-of-neteval-ordering-compile
;;       (implies (and (not (svex-lookup v network))
;;                     (hons-assoc-equal (svar-fix v) (neteval-ordering-fix x))
;;                     (not (equal v2 (svar-fix v))))
;;                (not (svex-depends-on v2 (svex-lookup v (neteval-ordering-compile x network)))))
;;       :hints ('(:expand ((neteval-ordering-compile x network))
;;                 :in-theory (enable svex-lookup-of-cons)))
;;       :flag neteval-ordering-compile)

;;     (defthm svex-deps-of-non-network-of-neteval-sigordering-compile
;;       (implies (and (not (svex-lookup v network))
;;                     (not (equal v2 (svar-fix v)))
;;                     (svar-equiv signal v))
;;                (not (svex-depends-on v2 (neteval-sigordering-compile x signal offset network))))
;;       :hints ('(:expand ((neteval-sigordering-compile x signal offset network))))
;;       :flag neteval-sigordering-compile)

;;     (defthm svex-deps-of-non-network-of-neteval-ordering-or-null-compile
;;       (implies (and (not (svex-lookup v network))
;;                     (not (equal v2 (svar-fix v)))
;;                     (svar-equiv signal v))
;;                (not (svex-depends-on v2 (neteval-ordering-or-null-compile x signal network))))
;;       :hints ('(:expand ((neteval-ordering-or-null-compile x signal network)
;;                          (:free (a) (svex-compose (svex-var signal) a)))
;;                 :in-theory (enable svex-compose-lookup)))
;;       :flag neteval-ordering-or-null-compile))

;;   (local (defthm svex-lookup-of-neteval-ordering-compile-under-iff
;;            (iff (svex-lookup var (neteval-ordering-compile ord network))
;;                 (hons-assoc-equal (svar-fix var) (neteval-ordering-fix ord)))))

;;   (local (defthm not-var-of-lookup-when-not-var-of-reduce
;;            (implies (and (NOT (MEMBER-EQUAL V (SVEX-ALIST-DEPS (SVEX-ALIST-REDUCE keys x))))
;;                          (member-equal (svar-fix key) (svarlist-fix keys)))
;;                     (NOT (MEMBER-EQUAL V (SVEX-DEPS (SVEX-LOOKUP key x)))))
;;            :hints(("Goal" :in-theory (enable svex-alist-deps
;;                                              svex-alist-reduce
;;                                              svex-lookup-of-cons)))))

  
;;   (defthm-svex-deps-flag deps-of-svex-compose-neteval-ordering-compile
;;     (defthm svex-compose-of-svex-compalist-normalize
;;       (implies (and (not (member-equal v (set-difference-equal (svex-dependencies x)
;;                                                                (intersection-equal (svex-alist-keys network)
;;                                                                                    (alist-keys (neteval-ordering-fix ord)))
;;                                                                )))
;;                     (not (member-equal v (svex-alist-deps (svex-alist-reduce (svex-alist-keys network)
;;                                                                              (neteval-ordering-compile ord network))))))
;;                (not (member-equal v (svex-deps (svex-compose x (neteval-ordering-compile ord network))))))
;;       :hints ((and stable-under-simplificationp
;;                    '(:expand ((:free (a) (svex-compose x a)))
;;                      :in-theory (disable svex-lookup-of-neteval-ordering-compile))))
;;       :flag svex-deps)
;;     (defthm svexlist-compose-of-svexlist-compalist-normalize
;;       (implies (and (not (member-equal v (set-difference-equal (svexlist-deps x)
;;                                                                (intersection-equal (svex-alist-keys network)
;;                                                                                    (alist-keys (neteval-ordering-fix ord))))))
;;                     (not (member-equal v (svex-alist-deps (svex-alist-reduce (svex-alist-keys network)
;;                                                                              (neteval-ordering-compile ord network))))))
;;                (not (member-equal v (svexlist-deps (svexlist-compose x (neteval-ordering-compile ord network))))))
;;       :hints ((and stable-under-simplificationp
;;                    '(:expand ((:free (a) (svexlist-compose x a))))))
;;       :flag svexlist-deps))


;;   (local (defthm svex-alist-reduce-of-nil
;;            (equal (svex-alist-reduce deps nil) nil)
;;            :hints(("Goal" :in-theory (enable svex-alist-reduce)))))

;;   (local (defthm svex-alist-deps-of-svex-alist-reduce-cons
;;            (implies (and (not (and (svar-p var)
;;                                    (member-equal var (svarlist-fix deps))
;;                                    (member-equal v (svex-deps val))))
;;                          (not (member-equal v (svex-alist-deps (svex-alist-reduce deps rest)))))
;;                     (not (member-equal v (svex-alist-deps (svex-alist-reduce deps (cons (cons var val) rest))))))
;;            :hints(("Goal" :in-theory (enable svex-alist-deps svex-alist-reduce svarlist-fix
;;                                              svex-lookup-of-cons)))))

    
;;   (defthm-neteval-ordering-compile-flag
;;     (defthm member-svex-alist-deps-of-neteval-ordering-compile
;;       (implies (and (not (member-equal v (svex-alist-deps network)))
;;                     (not (member-equal v (svex-alist-keys network))))
;;                (not (member-equal v (svex-alist-deps (svex-alist-reduce (svex-alist-keys network)
;;                                                                         (neteval-ordering-compile x network))))))
;;       :hints ('(:expand ((neteval-ordering-compile x network))))
;;       :flag neteval-ordering-compile)

;;     (defthm member-svex-alist-deps-of-neteval-sigordering-compile
;;       (implies (and (not (member-equal v (svex-alist-deps network)))
;;                     (not (member-equal v (svex-alist-keys network)))
;;                     (not (svar-equiv v signal)))
;;                (not (member-equal v (svex-deps (neteval-sigordering-compile x signal offset network)))))
;;       :hints ('(:expand ((neteval-sigordering-compile x signal offset network))))
;;       :flag neteval-sigordering-compile)

;;     (defthm member-svex-alist-deps-of-neteval-ordering-or-null-compile
;;       (implies (and (not (member-equal v (svex-alist-deps network)))
;;                     (not (member-equal v (svex-alist-keys network)))
;;                     (not (svar-equiv v signal)))
;;                (not (member-equal v (svex-deps (neteval-ordering-or-null-compile x signal network)))))
;;       :hints ('(:expand ((neteval-ordering-or-null-compile x signal network))
;;                 :in-theory (enable svex-compose-lookup)))
;;       :flag neteval-ordering-or-null-compile))
  
;;   )


(local (defthmd svex-lookup-when-not-member-svex-alist-keys
         (implies (not (member-equal (svar-fix k) (svex-alist-keys x)))
                  (not (svex-lookup k x)))))

(local (defthm svex-alist-reduce-superset-under-svex-alist-eval-equiv
         (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix keys))
                  (svex-alist-eval-equiv (svex-alist-reduce keys x) x))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                           svex-lookup-when-not-member-svex-alist-keys)))))


(defthm svex-alist-not-depends-on-neteval-ordering-compile-when-keys-subset-of-network
  (implies (and (not (member-equal (svar-fix v) (svex-alist-vars network)))
                (not (member-equal (svar-fix v) (svex-alist-keys network)))
                (subsetp-equal (alist-keys (neteval-ordering-fix x))
                               (svex-alist-keys network)))
           (not (svex-alist-depends-on v (neteval-ordering-compile x network))))
  :hints (("goal" :use ((:instance svex-alist-not-depends-on-when-not-member-vars
                         (var v) (x (svex-alist-reduce (svex-alist-keys network)
                                                       (neteval-ordering-compile x network)))))
           :in-theory (disable svex-alist-not-depends-on-when-not-member-vars)
           :do-not-induct t))
  :otf-flg t)



(local (defthm svex-lookup-of-svarlist-x-subst-iff
         (iff (svex-lookup v (svarlist-x-subst vars))
              (member-equal (svar-fix v) (svarlist-fix vars)))
         :hints(("Goal" :in-theory (enable svarlist-x-subst
                                           svex-lookup-of-cons)))))

(local (defthm svex-alist-depends-on-of-svex-alist-compose-strong-split
         (implies (and (case-split (or (not (svex-alist-depends-on v x))
                                       (svex-lookup v a)))
                       (not (svex-alist-depends-on v a)))
                  (not (svex-alist-depends-on v (svex-alist-compose x a))))
         :hints (("goal" :expand ((svex-alist-depends-on v (svex-alist-compose x a))))
                 '(:cases ((svex-lookup v a))))))

(defthm svex-alist-not-depends-on-neteval-ordering-compile-x-subst
  (implies (and (not (member-equal (svar-fix v) (set-difference-equal (svex-alist-vars network)
                                                                      (svex-alist-keys network))))
                (subsetp-equal (alist-keys (neteval-ordering-fix x))
                               (svex-alist-keys network)))
           (not (svex-alist-depends-on v (svex-alist-compose
                                          (neteval-ordering-compile x network)
                                          (svarlist-x-subst (svex-alist-keys network))))))
  :hints (("goal"
           :do-not-induct t))
  :otf-flg t)

(local
 (defthm svex-alist-not-depends-on-neteval-ordering-compile-x-subst-free
   (implies (and (svex-alist-eval-equiv comp
                                        (svex-alist-compose
                                         (neteval-ordering-compile x network)
                                         (svarlist-x-subst (svex-alist-keys network))))
                 (not (member-equal (svar-fix v) (set-difference-equal (svex-alist-vars network)
                                                                       (svex-alist-keys network))))
                 (subsetp-equal (alist-keys (neteval-ordering-fix x))
                                (svex-alist-keys network)))
           (not (svex-alist-depends-on v comp)))))


(local (defthm rewrite-svex-alist-keys-when-eval-equiv
         (implies (and (svex-alist-eval-equiv comp x)
                       (equal res (svex-alist-keys x))
                       (syntaxp (not (equal res `(svex-alist-keys ,comp)))))
                  (set-equiv (svex-alist-keys comp) res))))

(defthmd svex-alist-not-depends-on-of-netevalcomp
  (implies (and (netevalcomp-p comp network)
                (subsetp-equal (svex-alist-keys comp) (svex-alist-keys network))
                (not (member-equal (svar-fix v) (set-difference-equal (svex-alist-vars network)
                                                                      (svex-alist-keys network)))))
           (not (svex-alist-depends-on v comp)))
  :hints(("Goal" :in-theory (enable netevalcomp-p))))


(defthm svex-alist-dependencies-of-netevalcomp
  (implies (and (netevalcomp-p comp network)
                (subsetp-equal (svex-alist-keys comp) (svex-alist-keys network)))
           (subsetp-equal (svex-alist-dependencies comp)
                          (set-difference-equal (svex-alist-vars network)
                                                (svex-alist-keys network))))
  :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw
                                    svex-alist-not-depends-on-of-netevalcomp))))
           


                                       
                
