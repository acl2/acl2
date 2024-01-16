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

(include-book "../svex/env-ops")
(include-book "centaur/meta/variable-free" :dir :system)
(include-book "../svex/lattice")
(include-book "../svex/override-types")
(include-book "../svex/override-mux")
(include-book "probe")
(include-book "std/alists/alist-defuns" :dir :System)
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "name-lhs-map-inverse")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :System))
(local (std::add-default-post-define-hook :fix))

(defthmd alist-keys-of-svex-env-fix-when-known-keys
  (implies (and (equal keys (alist-keys x))
                (syntaxp (quotep keys)))
           (equal (alist-keys (svex-env-fix x))
                  (svarlist-filter keys)))
  :hints(("Goal" :in-theory (enable svex-env-fix alist-keys svarlist-filter))))


(defthmd alist-keys-of-cons
  (equal (alist-keys (cons a b))
         (if (consp a)
             (cons (car a) (alist-keys b))
           (alist-keys b)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(defthmd alist-keys-of-append
  (equal (alist-keys (append a b))
         (append (alist-keys a) (alist-keys b)))
  :hints(("Goal" :in-theory (enable alist-keys))))


(defthmd svex-env-reduce-of-known-keys
  (implies (and (syntaxp (and (not (quotep keys))
                              (cmr::term-variable-free-p keys)))
                (equal env-keys (alist-keys env))
                (syntaxp (quotep env-keys))
                (equal new-keys (acl2::hons-intersection env-keys (svarlist-fix keys)))
                (syntaxp (quotep new-keys)))
           (svex-envs-similar (svex-env-reduce keys env)
                              (svex-env-extract new-keys env)))
  :hints (("goal" :in-theory (enable svex-envs-similar))
          (and stable-under-simplificationp
               '(:in-theory (enable svex-env-lookup
                                    acl2::alist-keys-member-hons-assoc-equal)))))

;; the following are all duplicated in svtv-fsm-override
(defthmd svex-env-extract-of-cons
  (equal (svex-env-extract (cons key keys) env)
         (cons (cons (svar-fix key) (svex-env-lookup key env))
               (svex-env-extract keys env)))
  :hints(("Goal" :in-theory (enable svex-env-extract))))

(defthm svex-env-extract-of-nil
    (equal (svex-env-extract nil env) nil)
    :hints(("Goal" :in-theory (enable svex-env-extract))))


(cmr::def-force-execute hons-intersection-force-execute
  acl2::hons-intersection)


(define svex-env-<<=-each ((x svex-env-p)
                           (y svex-env-p))
  ;; Like svex-env-<<=, but iterates over the pairs in x rather than
  ;; quantifying over the keys.  So it's the same as svex-env-<<= as long as x
  ;; has no duplicate keys (or at least no duplicated keys bound to different
  ;; values).
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (4vec-<<= (cdar x) (svex-env-lookup (caar x) y)))
         (svex-env-<<=-each (cdr x) y)))
  ///
  (local (defthm svex-env-<<=-each-implies-4vec-<<=
           (implies (svex-env-<<=-each x y)
                    (4vec-<<= (svex-env-lookup k x)
                              (svex-env-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (local (defthm svex-env-<<=-each-implies-svex-env-<<=
           (implies (svex-env-<<=-each x y)
                    (svex-env-<<= x y))
           :hints(("Goal" :expand ((svex-env-<<= x y))))))

  (local (defthm svex-env-<<=-cdr-when-first-key-not-repeated
           (implies (and (or (not (consp (car x)))
                             (not (svar-p (caar x)))
                             (not (svex-env-boundp (caar x) (cdr x))))
                         (svex-env-<<= x y))
                    (svex-env-<<= (cdr x) y))
           :hints (("Goal" :expand ((svex-env-<<= (cdr x) y))
                    :use ((:instance svex-env-<<=-necc
                           (var (svex-env-<<=-witness (cdr x) y))))
                    :in-theory (e/d (svex-env-lookup
                                     svex-env-boundp)
                                    (svex-env-<<=-necc))))))

  (local (defthm svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each
           (implies (and (svex-env-<<= x y)
                         (no-duplicatesp-equal (alist-keys (svex-env-fix x))))
                    (svex-env-<<=-each x y))
           :hints(("Goal" :in-theory (e/d (svex-env-lookup
                                           svex-env-boundp
                                           acl2::alist-keys-member-hons-assoc-equal
                                           svex-env-fix)
                                          (svex-env-<<=-necc))
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance svex-env-<<=-necc
                                (var (caar x)))))))))

  (defthm svex-env-<<=-each-of-cons
    (equal (svex-env-<<=-each (cons pair x) y)
           (and (or (not (consp pair))
                    (not (svar-p (car pair)))
                    (4vec-<<= (cdr pair) (svex-env-lookup (car pair) y)))
                (svex-env-<<=-each x y))))

  (defthm svex-env-<<=-each-of-nil
    (equal (svex-env-<<=-each nil y) t))

  (local (defthm svarlist-filter-of-alist-keys
           (equal (svarlist-filter (alist-keys x))
                  (alist-keys (svex-env-fix x)))
           :hints(("Goal" :in-theory (enable svarlist-filter alist-keys svex-env-fix)))))

  (defthmd svex-env-<<=-is-svex-env-<<=-each-when-no-duplicate-keys
    (implies (and (equal keys (alist-keys x))
                  (syntaxp (quotep keys))
                  (not (acl2::hons-dups-p (svarlist-filter keys))))
             (equal (svex-env-<<= x y)
                    (svex-env-<<=-each x y)))
    :hints(("Goal" :in-theory (disable acl2::hons-dups-p
                                       svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each)
            :use (svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each)
            :do-not-induct t)))

  (local (in-theory (enable svex-env-fix))))


(defthmd 4vec-<<=-when-integerp
  (implies (integerp x)
           (equal (4vec-<<= x y)
                  (equal (4vec-fix y) x)))
  :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix)))))

(defthmd svex-env-lookup-when-integerp-and-<<=
  (implies (and (svex-env-<<= env1 env2)
                (integerp (svex-env-lookup k env1)))
           (equal (svex-env-lookup k env2)
                  (svex-env-lookup k env1)))
  :hints (("goal" :use ((:instance svex-env-<<=-necc
                         (x env1) (y env2) (var k)))
           :in-theory (e/d (4vec-<<=-when-integerp)
                           (svex-env-<<=-necc)))))


(fty::defoption maybe-svar-p svar-p)

(defprod svtv-override-triple
  ((test svex-p)
   (val svex-p)
   (refvar maybe-svar-p))
  :layout :list)

(fty::defmap svtv-override-triplemap :key-type svar :val-type svtv-override-triple :true-listp t)

(fty::deflist svtv-override-triplemaplist :elt-type svtv-override-triplemap :true-listp t)

(fty::deflist svtv-override-triplelist :elt-type svtv-override-triple :true-listp t)

(define svtv-override-triplemap-to-triplelist ((x svtv-override-triplemap-p))
  :returns (triples svtv-override-triplelist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-override-triplemap-to-triplelist (cdr x))))
    (cons (svtv-override-triple-fix (cdar x))
          (svtv-override-triplemap-to-triplelist (cdr x))))
  ///
  (local (in-theory (enable svtv-override-triplemap-fix))))


(define svtv-override-triplemaplist-to-triplelist ((x svtv-override-triplemaplist-p))
  :returns (triples svtv-override-triplelist-p)
  (b* (((when (atom x)) nil))
    (append (svtv-override-triplemap-to-triplelist (car x))
            (svtv-override-triplemaplist-to-triplelist (cdr x)))))

(define svar-override-triple-to-svtv-override-triple ((x svar-override-triple-p))
  :returns (trip svtv-override-triple-p)
  (b* (((svar-override-triple x)))
    (make-svtv-override-triple :test (svex-var x.testvar)
                               :val (svex-var x.valvar)
                               :refvar x.refvar)))

(define svar-override-triplelist-to-svtv-override-triplelist ((x svar-override-triplelist-p))
  :returns (trips svtv-override-triplelist-p)
  (if (atom x)
      nil
    (cons (svar-override-triple-to-svtv-override-triple (car x))
          (svar-override-triplelist-to-svtv-override-triplelist (cdr x)))))


(define svtv-override-triplelist-val-alist ((x svtv-override-triplelist-p))
  :returns (triplemap svtv-override-triplemap-p) ;; but not the regular kind!
  (b* (((when (atom x)) nil)
       ((svtv-override-triple x1) (car x))
       ((unless (svex-case x1.val :var))
        (svtv-override-triplelist-val-alist (cdr x))))
    (cons (cons (svex-var->name x1.val) (svtv-override-triple-fix x1))
          (svtv-override-triplelist-val-alist (cdr x)))))




(defsection 4vec-override-mux-<<=-extra-facts

  (local (defthm 4vec-bit?!-else-4vec-bit?!-same-test
           (equal (4vec-bit?! test then1 (4vec-bit?! test then2 else2))
                  (4vec-bit?! test then1 else2))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))
                  (acl2::logbitp-reasoning)
                  (and stable-under-simplificationp
                       '(:in-theory (enable b-ite))))))

  (local (defthm logeqv-is-lognot-logxor
           (equal (logeqv x y)
                  (lognot (logxor x y)))
           :hints(("Goal" :in-theory (e/d (logxor) (logeqv))))))

  (local
   (defthm 4vec-<=-4vec-bit?!-same-test-same-else
     (implies (4vec-<<= (4vec-bit?! a b1 c1)
                        (4vec-bit?! a b2 c1))
              (4vec-<<= (4vec-bit?! a b1 c2)
                        (4vec-bit?! a b2 c2)))
     :hints(("Goal" :in-theory (e/d (4vec-bit?! 4vec-<<= 4vec-bitmux)
                                    (logeqv
                                     bitops::logior-<-0-linear-2
                                     bitops::logand-natp-type-2
                                     bitops::logior-<-0-linear-1
                                     bitops::logior-<-0-linear-2
                                     bitops::logior->=-0-linear))
             :do-not '(eliminate-destructors))
            (acl2::logbitp-reasoning
             :add-hints (:in-theory (enable* logbitp-case-splits)))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-xor b-ite))))
     :otf-flg t))


  (defthmd 4vec-<=-4vec-bit?!-same-test-same-else-normalize
    (implies (syntaxp (not (equal c1 ''0)))
             (equal (4vec-<<= (4vec-bit?! a b1 c1)
                              (4vec-bit?! a b2 c1))
                    (4vec-<<= (4vec-bit?! a b1 0)
                              (4vec-bit?! a b2 0))))
    :hints (("goal" :cases
             ((4vec-<<= (4vec-bit?! a b1 c1)
                        (4vec-bit?! a b2 c1))))))
  
  (defthmd 4vec-override-mux-<<=-same
    (equal (4vec-override-mux-<<= test val1 test val2 ref)
           (4vec-<<= (4vec-bit?! test val1 0)
                     (4vec-bit?! test val2 0)))
    :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=)
            :cases ((4vec-<<= (4vec-bit?! test val1 0)
                              (4vec-bit?! test val2 0)))))))

(local (in-theory (enable 4vec-<=-4vec-bit?!-same-test-same-else-normalize
                          4vec-override-mux-<<=-same)))


(define 4vec-override-mux-ok ((impl-test 4vec-p)
                              (impl-val 4vec-p)
                              (spec-test 4vec-p)
                              (spec-val 4vec-p)
                              (ref-p)
                              (ref-val 4vec-p))
  :returns (ok)
  (if ref-p
      (and (4vec-override-mux-<<= impl-test impl-val spec-test spec-val ref-val)
           (4vec-muxtest-subsetp spec-test impl-test))
    (and (4vec-1mask-equiv spec-test impl-test)
         (4vec-<<= impl-val spec-val) ))
  ///
  (defret 4vec-override-mux-<<=-when-<fn>
    (implies ok
             (4vec-override-mux-<<= impl-test
                                    impl-val
                                    spec-test
                                    spec-val
                                    ref-val))
    ;; :hints ((and stable-under-simplificationp
    ;;              '(:in-theory (enable 4vec-override-mux-<<=))))
    )

  (defret 4vec-muxtest-subsetp-when-<fn>
    (implies ok
             (4vec-muxtest-subsetp spec-test impl-test))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable 4vec-muxtest-subsetp)))))

  
  (defret <fn>-of-greater-refval
    (implies (and ok
                  (4vec-<<= ref-val ref-val2))
             (4vec-override-mux-ok impl-test impl-val spec-test spec-val ref-p ref-val2)))

  (defretd <fn>-redef
    (equal ok
           (and (4vec-override-mux-<<= impl-test impl-val spec-test spec-val ref-val)
                (4vec-muxtest-subsetp spec-test impl-test)
                (implies (not ref-p)
                         (and (4vec-1mask-equiv spec-test impl-test)
                              (4vec-<<= impl-val spec-val)))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable 4vec-muxtest-subsetp)))))

  (defthm <fn>-normalize-ref-val-when-not-ref-p
    (implies (syntaxp (not (equal ref-val ''0)))
             (equal (4vec-override-mux-ok impl-test impl-val spec-test spec-val nil ref-val)
                    (4vec-override-mux-ok impl-test impl-val spec-test spec-val nil 0)))))

(define svtv-override-triple-envs-ok ((triple svtv-override-triple-p)
                                      (pipe-env svex-env-p)
                                      (spec-env svex-env-p)
                                      (spec-run svex-env-p))
  :returns (ok)
  (b* (((svtv-override-triple triple)))
    (mbe :logic
         (4vec-override-mux-ok (svex-eval triple.test pipe-env)
                          (svex-eval triple.val pipe-env)
                          (svex-eval triple.test spec-env)
                          (svex-eval triple.val spec-env)
                          triple.refvar
                          (svex-env-lookup triple.refvar spec-run))
         :exec
         (4vec-override-mux-ok (svex-eval triple.test pipe-env)
                          (svex-eval triple.val pipe-env)
                          (svex-eval triple.test spec-env)
                          (svex-eval triple.val spec-env)
                          triple.refvar
                          (if triple.refvar
                              (svex-env-lookup triple.refvar spec-run)
                            0))))
  ///
  

  (defthm svtv-override-triple-envs-ok-when-<<=
    (implies (and (svtv-override-triple-envs-ok x pipe-env spec-env spec-run1)
                  (svex-env-<<= spec-run1 spec-run2))
             (svtv-override-triple-envs-ok x pipe-env spec-env spec-run2)))


  (defcong svex-envs-similar equal (svtv-override-triple-envs-ok x impl-env spec-env ref-env) 2)
  (defcong svex-envs-similar equal (svtv-override-triple-envs-ok x impl-env spec-env ref-env) 3)
  (defcong svex-envs-similar equal (svtv-override-triple-envs-ok x impl-env spec-env ref-env) 4)


  

  
  (defret 4vec-override-mux-<<=-when-<fn>
    (implies ok
             (b* (((svtv-override-triple triple)))
               (4vec-override-mux-<<= (svex-eval triple.test pipe-env)
                                      (svex-eval triple.val pipe-env)
                                      (svex-eval triple.test spec-env)
                                      (svex-eval triple.val spec-env)
                                      (svex-env-lookup triple.refvar spec-run))))
    ;; :hints ((and stable-under-simplificationp
    ;;              '(:in-theory (enable 4vec-override-mux-<<=))))
    )

  (defret 4vec-muxtest-subsetp-when-<fn>
    (implies ok
             (b* (((svtv-override-triple triple)))
               (4vec-muxtest-subsetp (svex-eval triple.test spec-env)
                                     (svex-eval triple.test pipe-env))))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable 4vec-muxtest-subsetp))))))


(define svtv-override-triplemap-envs-ok ((triplemap svtv-override-triplemap-p)
                                         (pipe-env svex-env-p)
                                         (spec-env svex-env-p)
                                         (spec-run svex-env-p))
  :returns (ok)
  (if (atom triplemap)
      t
    (and (or (not (mbt (and (consp (car triplemap))
                            (svar-p (caar triplemap)))))
             (svtv-override-triple-envs-ok (cdar triplemap) pipe-env spec-env spec-run))
         (svtv-override-triplemap-envs-ok (cdr triplemap) pipe-env spec-env spec-run)))
  ///
  (defret svtv-override-triple-envs-ok-of-lookup-when-<fn>
    (implies (and ok
                  (hons-assoc-equal key triplemap)
                  (svar-p key))
             (svtv-override-triple-envs-ok (cdr (hons-assoc-equal key triplemap))
                                           pipe-env spec-env spec-run)))

  (defthm svtv-override-triplemap-envs-ok-when-<<=
    (implies (and (svtv-override-triplemap-envs-ok triplemaps pipe-env spec-env spec-run1)
                  (svex-env-<<= spec-run1 spec-run2))
             (svtv-override-triplemap-envs-ok triplemaps pipe-env spec-env spec-run2)))
  
  (defcong svex-envs-similar equal (svtv-override-triplemap-envs-ok x impl-env spec-env ref-env) 2)
  (defcong svex-envs-similar equal (svtv-override-triplemap-envs-ok x impl-env spec-env ref-env) 3)
  (defcong svex-envs-similar equal (svtv-override-triplemap-envs-ok x impl-env spec-env ref-env) 4)

  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist-envs-ok ((triplemaps svtv-override-triplemaplist-p)
                                             (pipe-env svex-env-p)
                                             (spec-env svex-env-p)
                                             (spec-run svex-env-p))
  :returns (ok)
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-envs-ok (car triplemaps) pipe-env spec-env spec-run)
         (svtv-override-triplemaplist-envs-ok (cdr triplemaps) pipe-env spec-env spec-run)))
  ///

  (defthm svtv-override-triplemaplist-envs-ok-when-<<=
    (implies (and (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run1)
                  (svex-env-<<= spec-run1 spec-run2))
             (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run2)))

  (defcong svex-envs-similar equal (svtv-override-triplemaplist-envs-ok x impl-env spec-env ref-env) 2)
  (defcong svex-envs-similar equal (svtv-override-triplemaplist-envs-ok x impl-env spec-env ref-env) 3)
  (defcong svex-envs-similar equal (svtv-override-triplemaplist-envs-ok x impl-env spec-env ref-env) 4))



  
;; (define svtv-override-triple-mux-<<= ((triple svtv-override-triple-p)
;;                                       (pipe-env svex-env-p)
;;                                       (spec-env svex-env-p)
;;                                       (spec-run svex-env-p))
;;   :returns (ok)
;;   (b* (((svtv-override-triple triple)))
;;     (4vec-override-mux-<<= (svex-eval triple.test pipe-env)
;;                            (svex-eval triple.val pipe-env)
;;                            (svex-eval triple.test spec-env)
;;                            (svex-eval triple.val spec-env)
;;                            (svex-env-lookup triple.refvar spec-run)))
;;   ///
;;   ;; (defthm 4vec-override-mux-<<=-when-spec-ref-<<=
;;   ;;   (implies (and (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref1)
;;   ;;                 (4vec-<<= spec-ref1 spec-ref2))
;;   ;;            (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref2))
;;   ;;   :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=
;;   ;;                                     4vec-bit?!
;;   ;;                                     4vec-<<=))))
;;   (defthm svtv-override-triple-mux-<<=-when-<<=
;;     (implies (and (svtv-override-triple-mux-<<= triple pipe-env spec-env spec-run1)
;;                   (svex-env-<<= spec-run1 spec-run2))
;;              (svtv-override-triple-mux-<<= triple pipe-env spec-env spec-run2))))

;; (define svtv-override-triplemap-muxes-<<= ((triplemap svtv-override-triplemap-p)
;;                                            (pipe-env svex-env-p)
;;                                            (spec-env svex-env-p)
;;                                            (spec-run svex-env-p))
;;   :returns (ok)
;;   (if (atom triplemap)
;;       t
;;     (and (or (not (mbt (and (consp (car triplemap))
;;                             (svar-p (caar triplemap)))))
;;              (svtv-override-triple-mux-<<= (cdar triplemap) pipe-env spec-env spec-run))
;;          (svtv-override-triplemap-muxes-<<= (cdr triplemap) pipe-env spec-env spec-run)))
;;   ///
;;   (defret svtv-override-triple-mux-<<=-of-lookup-when-<fn>
;;     (implies (and ok
;;                   (hons-assoc-equal key triplemap)
;;                   (svar-p key))
;;              (svtv-override-triple-mux-<<= (cdr (hons-assoc-equal key triplemap))
;;                                            pipe-env spec-env spec-run)))

;;   (defthm svtv-override-triplemap-muxes-<<=-when-<<=
;;     (implies (and (svtv-override-triplemap-muxes-<<= triplemaps pipe-env spec-env spec-run1)
;;                   (svex-env-<<= spec-run1 spec-run2))
;;              (svtv-override-triplemap-muxes-<<= triplemaps pipe-env spec-env spec-run2)))
  
;;   (local (in-theory (enable svtv-override-triple-mux-<<=)))
;;   (defcong svex-envs-similar equal (svtv-override-triplemap-muxes-<<= x impl-env spec-env ref-env) 2)
;;   (defcong svex-envs-similar equal (svtv-override-triplemap-muxes-<<= x impl-env spec-env ref-env) 3)
;;   (defcong svex-envs-similar equal (svtv-override-triplemap-muxes-<<= x impl-env spec-env ref-env) 4)
;;   (local (in-theory (e/d (svtv-override-triplemap-fix) (svtv-override-triple-mux-<<=)))))


;; (define svtv-override-triplemaplist-muxes-<<= ((triplemaps svtv-override-triplemaplist-p)
;;                                                (pipe-env svex-env-p)
;;                                                (spec-env svex-env-p)
;;                                                (spec-run svex-env-p))
;;   :returns (ok)
;;   (if (atom triplemaps)
;;       t
;;     (and (svtv-override-triplemap-muxes-<<= (car triplemaps) pipe-env spec-env spec-run)
;;          (svtv-override-triplemaplist-muxes-<<= (cdr triplemaps) pipe-env spec-env spec-run)))
;;   ///

;;   (defthm svtv-override-triplemaplist-muxes-<<=-when-<<=
;;     (implies (and (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-env spec-run1)
;;                   (svex-env-<<= spec-run1 spec-run2))
;;              (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-env spec-run2)))

;;   (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env ref-env) 2)
;;   (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env ref-env) 3)
;;   (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env ref-env) 4))

;; (define svtv-override-triplemap->tests ((triplemap svtv-override-triplemap-p))
;;   :returns (tests svexlist-p)
;;   (if (atom triplemap)
;;       nil
;;     (if (mbt (and (consp (car triplemap))
;;                   (svar-p (caar triplemap))))
;;         (cons (svtv-override-triple->test (cdar triplemap))
;;               (svtv-override-triplemap->tests (cdr triplemap)))
;;       (svtv-override-triplemap->tests (cdr triplemap))))
;;   ///
;;   (local (in-theory (enable svtv-override-triplemap-fix))))

;; (define svex-envs-svexlist-muxtests-subsetp ((tests svexlist-p)
;;                                              (spec-env svex-env-p)
;;                                              (impl-env svex-env-p))
;;   :returns (ok)
;;   (if (atom tests)
;;       t
;;     (and (4vec-muxtest-subsetp (svex-eval (car tests) spec-env)
;;                                (svex-eval (car tests) impl-env))
;;          (svex-envs-svexlist-muxtests-subsetp (cdr tests) spec-env impl-env)))
;;   ///
;;   (defret <fn>-implies-4vec-muxtest-subsetp-when-member-tests
;;     (implies (and ok
;;                   (member-equal (svex-fix test) (Svexlist-fix tests)))
;;              (4vec-muxtest-subsetp (svex-eval test spec-env)
;;                                    (svex-eval test impl-env)))
;;     :hints(("Goal" :in-theory (enable svexlist-fix))))

;;   (defcong svex-envs-similar equal (svex-envs-svexlist-muxtests-subsetp tests spec-env impl-env) 2)
;;   (defcong svex-envs-similar equal (svex-envs-svexlist-muxtests-subsetp tests spec-env impl-env) 3))

;; (define svtv-override-triplemaplist-muxtests-subsetp ((triplemaps svtv-override-triplemaplist-p)
;;                                                       (spec-env svex-env-p)
;;                                                       (impl-env svex-env-p))
;;   (if (atom triplemaps)
;;       t
;;     (and (svex-envs-svexlist-muxtests-subsetp (svtv-override-triplemap->tests (car triplemaps))
;;                                               spec-env impl-env)
;;          (svtv-override-triplemaplist-muxtests-subsetp (cdr triplemaps) spec-env impl-env)))
;;   ///
;;   (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-env impl-env) 2)
;;   (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-env impl-env) 3))





;; ;; (define svtv-override-triple-ok ((triple svtv-override-triple-p)
;; ;;                                  (pipe-env svex-env-p)
;; ;;                                  (ref-env svex-env-p))
;; ;;   :returns (ok)
;; ;;   (b* (((svtv-override-triple triple)))
;; ;;     (4vec-override-values-ok-<<= (svex-eval triple.test pipe-env)
;; ;;                                  (svex-eval triple.val pipe-env)
;; ;;                                  (svex-env-lookup triple.refvar ref-env)))
;; ;;   ///
;; ;;   (defthm svtv-override-triple-ok-when-<<=
;; ;;     (implies (and (svtv-override-triple-ok triple pipe-env ref-env1)
;; ;;                   (svex-env-<<= ref-env1 ref-env2))
;; ;;              (svtv-override-triple-ok triple pipe-env ref-env2))))

;; ;; (define svtv-override-triplemap-ok ((triplemap svtv-override-triplemap-p)
;; ;;                                     (pipe-env svex-env-p)
;; ;;                                     (ref-env svex-env-p))
;; ;;   :returns (ok)
;; ;;   (if (atom triplemap)
;; ;;       t
;; ;;     (and (or (not (mbt (and (consp (car triplemap))
;; ;;                             (svar-p (caar triplemap)))))
;; ;;              (svtv-override-triple-ok (cdar triplemap) pipe-env ref-env))
;; ;;          (svtv-override-triplemap-ok (cdr triplemap) pipe-env ref-env)))
;; ;;   ///
;; ;;   (defret svtv-override-triple-ok-of-lookup-when-<fn>
;; ;;     (implies (and ok
;; ;;                   (hons-assoc-equal key triplemap)
;; ;;                   (svar-p key))
;; ;;              (svtv-override-triple-ok (cdr (hons-assoc-equal key triplemap))
;; ;;                                       pipe-env ref-env)))

;; ;;   (defthm svtv-override-triplemap-ok-when-<<=
;; ;;     (implies (and (svtv-override-triplemap-ok triplemaps pipe-env ref-env1)
;; ;;                   (svex-env-<<= ref-env1 ref-env2))
;; ;;              (svtv-override-triplemap-ok triplemaps pipe-env ref-env2)))
  
;; ;;   (local (in-theory (enable svtv-override-triplemap-fix))))
                  
                  




(define svtv-override-triplemap-key-check ((key svar-p)
                                        (phase natp)
                                        (test-alist svex-alist-p)
                                        (val-alist svex-alist-p)
                                        (probes svtv-probealist-p)
                                        (triplemap svtv-override-triplemap-p))
  :short "Checks that the given key either isn't bound the test alist, or else
has a triple in the triplemap such that the test of the triple is the key's
binding in the test-alist, the val of the triple is the key's binding in the
val-alist, and the refvar of the triple is bound in probes to a probe whose
signal is the key and time is the current phase."
  :parents (svtv-idealize-internals)
  :returns (ok)
  (b* ((test (svex-fastlookup key test-alist))
       ((unless test) t)
       (val (or (svex-fastlookup key val-alist) (svex-x)))
       ;; ((unless val) t)
       (triple (cdr (hons-get (svar-fix key) (svtv-override-triplemap-fix triplemap))))
       ((unless triple)
        nil)
       ((svtv-override-triple triple))
       ((unless (and (equal triple.test test)
                     (equal triple.val val)))
        nil)
       ((unless triple.refvar) t)
       (probe (cdr (hons-get triple.refvar (svtv-probealist-fix probes))))
       ((unless probe) nil)
       ((svtv-probe probe)))
    (and (equal probe.signal (svar-fix key))
         (equal probe.time (lnfix phase))))
  ///

  ;; (local (defthm equal-of-svar-fix
  ;;          (implies (equal x (svar-fix y))
  ;;                   (svar-equiv x y))
  ;;          :rule-classes :forward-chaining))
  ;; (local (defthm equal-of-svar-fix
  ;;          (implies (equal x (svar-fix y))
  ;;                   (svar-equiv x y))
  ;;          :rule-classes :forward-chaining))
  
  ;; (defret <fn>-implies
  ;;   (implies (and ok
  ;;                 (svtv-override-triple-ok (cdr (hons-assoc-equal (svar-fix key) triplemap))
  ;;                                          pipe-env
  ;;                                          (svtv-probealist-extract probes ref-envs)))
  ;;            (4vec-override-values-ok-<<=
  ;;             (svex-eval (svex-lookup key test-alist) pipe-env)
  ;;             (svex-eval (svex-lookup key val-alist) pipe-env)
  ;;             (svex-env-lookup key (nth phase ref-envs))))
  ;;   :hints(("Goal" :in-theory (enable svtv-override-triple-ok))))

  (local (defthm 4vec-override-mux-<<=-when-impl-test-x
           (4vec-override-mux-<<= (4vec-x) impl-val spec-test spec-val spec-ref)
           :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=)))))

  (local (defthm 4vec-override-mux-<<=-when-impl-val-x
           (4vec-override-mux-<<= impl-test (4vec-x) spec-test spec-val spec-ref)
           :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=)))))
  
  (defret <fn>-implies-4vec-override-mux-<<=
    (implies (and ok
                  (svtv-override-triple-envs-ok (cdr (hons-assoc-equal (svar-fix key) triplemap))
                                                pipe-env spec-env
                                                (svtv-probealist-extract probes ref-envs)))
             (4vec-override-mux-<<=
              (svex-eval (svex-lookup key test-alist) pipe-env)
              (svex-eval (svex-lookup key val-alist) pipe-env)
              (svex-eval (svex-lookup key test-alist) spec-env)
              (svex-eval (svex-lookup key val-alist) spec-env)
              (svex-env-lookup key (nth phase ref-envs))))
    :hints(("Goal" :in-theory (enable svtv-override-triple-envs-ok
                                      4vec-override-mux-ok))))

  (defret <fn>-implies-4vec-muxtest-subsetp
    (implies (and ok
                  (svtv-override-triple-envs-ok (cdr (hons-assoc-equal (svar-fix key) triplemap))
                                                pipe-env spec-env ref-env))
             (4vec-muxtest-subsetp
              (svex-eval (svex-lookup key test-alist) spec-env)
              (svex-eval (svex-lookup key test-alist) pipe-env)))
    :hints(("Goal" :in-theory (enable svtv-override-triple-envs-ok))))


  ;; (defret <fn>-implies-4vec-muxtest-subsetp
  ;;   (implies (and ok
  ;;                 (svtv-override-triple-mux-<<= (cdr (hons-assoc-equal (svar-fix key) triplemap))
  ;;                                               pipe-env spec-env
  ;;                                               (svtv-probealist-extract probes ref-envs)))
  ;;            (4vec-muxtest-subsetp
  ;;             (svex-eval (svex-lookup key test-alist) spec-env)
  ;;             (svex-eval (svex-lookup key test-alist) pipe-env)))
  ;;   :hints(("Goal" :in-theory (enable svtv-override-triple-mux-<<=))))

  ;; (local (defthm member-triplemap-tests-when-lookup-lemma
  ;;          (implies (and (hons-assoc-equal key triplemap)
  ;;                        (svar-p key))
  ;;                   (member-equal (svtv-override-triple->test (cdr (hons-assoc-equal key triplemap)))
  ;;                                 (svtv-override-triplemap->tests triplemap)))
  ;;          :hints(("Goal" :in-theory (enable svtv-override-triplemap->tests)))))

  ;; (local (defthm member-triplemap-tests-when-lookup
  ;;          (implies (and (equal val (svtv-override-triple->test (cdr (hons-assoc-equal key triplemap))))
  ;;                        (hons-assoc-equal key triplemap)
  ;;                        (svar-p key))
  ;;                   (member-equal val
  ;;                                 (svtv-override-triplemap->tests triplemap)))))
           
  
  ;; (defret member-tests-when-<fn>
  ;;   (implies (and ok
  ;;                 (svex-lookup key test-alist))
  ;;            (member-equal (svex-lookup key test-alist)
  ;;                          (svtv-override-triplemap->tests triplemap))))
  
  (defretd <fn>-implies-lookup-in-triplemap
    (implies (and ok
                  (case-split (svex-lookup key test-alist))
                  ;; (case-split (svex-lookup key val-alist))
                  )
             (hons-assoc-equal (svar-fix key) triplemap))))
              
         


(define svtv-override-triplemap-syntax-check ((keys svarlist-p)
                                              (phase natp)
                                              (test-alist svex-alist-p)
                                              (val-alist svex-alist-p)
                                              (probes svtv-probealist-p)
                                              (triplemap svtv-override-triplemap-p))
  :returns (ok)
  (if (atom keys)
      t
    (and (svtv-override-triplemap-key-check (car keys) phase test-alist val-alist probes triplemap)
         (svtv-override-triplemap-syntax-check (cdr keys) phase test-alist val-alist probes triplemap))))




;; (define svtv-override-triplemaplist-ok ((triplemaps svtv-override-triplemaplist-p)
;;                                         (pipe-env svex-env-p)
;;                                         (ref-env svex-env-p))
;;   :returns (ok)
;;   (if (atom triplemaps)
;;       t
;;     (and (svtv-override-triplemap-ok (car triplemaps) pipe-env ref-env)
;;          (svtv-override-triplemaplist-ok (cdr triplemaps) pipe-env ref-env)))
;;   ///

;;   (defthm svtv-override-triplemaplist-ok-when-<<=
;;     (implies (and (svtv-override-triplemaplist-ok triplemaps pipe-env ref-env1)
;;                   (svex-env-<<= ref-env1 ref-env2))
;;              (svtv-override-triplemaplist-ok triplemaps pipe-env ref-env2))))

(define svtv-override-triplemaplist-syntax-check-aux ((phase natp)
                                                      (test-alists svex-alistlist-p)
                                                      (val-alists svex-alistlist-p)
                                                      (probes svtv-probealist-p)
                                                      (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  :measure (len test-alists)
  (if (atom test-alists)
      t
    (and (b* ((test-alist (car test-alists))
              (val-alist (car val-alists))
              (triplemap (car triplemaps))
              ((acl2::with-fast test-alist val-alist triplemap)))
           (svtv-override-triplemap-syntax-check (svex-alist-keys test-alist)
                                                 phase
                                                 test-alist
                                                 val-alist
                                                 probes
                                                 (car triplemaps)))
         (svtv-override-triplemaplist-syntax-check-aux (1+ (lnfix phase))
                                                   (cdr test-alists)
                                                   (cdr val-alists)
                                                   probes
                                                   (cdr triplemaps)))))


(define svtv-override-triplemaplist-syntax-check ((test-alists svex-alistlist-p)
                                                  (val-alists svex-alistlist-p)
                                                  (probes svtv-probealist-p)
                                                  (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  (acl2::with-fast-alist probes
    (svtv-override-triplemaplist-syntax-check-aux 0 test-alists val-alists probes triplemaps)))


;; now, we need to show how to find a triplemaplist that satisfies the syntactic check above.


;; REDUNDANT with svtv-fsm-override
(fty::defmap svtv-rev-probealist :key-type svtv-probe :val-type svar :true-listp t)

(define svtv-construct-triplemap ((keys svarlist-p)
                                  (phase natp)
                                  (test-alist svex-alist-p)
                                  (val-alist svex-alist-p)
                                  (rev-probes svtv-rev-probealist-p))
  :returns (triplemap svtv-override-triplemap-p)
  (b* (((when (atom keys)) nil)
       (key (svar-fix (car keys)))
       (test (svex-fastlookup key test-alist))
       (val (svex-fastlookup key val-alist))
       ((unless (and test val))
        (svtv-construct-triplemap (cdr keys) phase test-alist val-alist rev-probes))
       (probevar-look (hons-get (make-svtv-probe :signal key :time phase)
                                (svtv-rev-probealist-fix rev-probes))))
    (cons (cons key (make-svtv-override-triple
                     :test test
                     :val val
                     :refvar (cdr probevar-look)))
          (svtv-construct-triplemap (cdr keys) phase test-alist val-alist rev-probes))))

(define svtv-construct-triplemaplist-aux ((phase natp)
                                          (test-alists svex-alistlist-p)
                                          (val-alists svex-alistlist-p)
                                          (rev-probes svtv-rev-probealist-p))
  :returns (triplemaplist svtv-override-triplemaplist-p)
  (if (atom val-alists)
      nil
    (cons (b* ((test-alist (car test-alists))
               (val-alist (car val-alists))
               ((acl2::with-fast test-alist val-alist)))
            (svtv-construct-triplemap (svex-alist-keys val-alist) phase test-alist val-alist rev-probes))
          (svtv-construct-triplemaplist-aux (1+ (lnfix phase))
                                            (cdr test-alists)
                                            (cdr val-alists)
                                            rev-probes))))

(define svtv-construct-triplemaplist ((test-alists svex-alistlist-p)
                                      (val-alists svex-alistlist-p)
                                      (probes svtv-probealist-p))
  :returns (triplemaplist svtv-override-triplemaplist-p)
  :prepwork
  ((local (defthm svtv-rev-probealist-p-of-pair-vals-keys
            (implies (svtv-probealist-p x)
                     (svtv-rev-probealist-p (pairlis$ (alist-vals x) (alist-keys x))))
            :hints(("Goal" :in-theory (enable svtv-rev-probealist-p svtv-probealist-p pairlis$ alist-keys alist-vals))))))
  (b* ((probes (svtv-probealist-fix probes))
       (rev-probes (make-fast-alist (pairlis$ (alist-vals probes) (alist-keys probes))))
       (triplemaplist (svtv-construct-triplemaplist-aux 0 test-alists val-alists rev-probes)))
    (fast-alist-free rev-probes)
    triplemaplist))



;; bozo same as svex-alistlist-key-lists (def in fsm.lisp)
(define svex-alist-keys-list ((x svex-alistlist-p))
  :returns (keys svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-alist-keys (car x))
          (svex-alist-keys-list (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len keys)
           (len x))))


(local (defthm svarlist-p-alist-keys-of-svex-env
         (implies (svex-env-p x)
                  (svarlist-p (alist-keys x)))
         :hints(("Goal" :in-theory (enable svex-env-p)))))

(define svex-env-keys-list ((x svex-envlist-p))
  :returns (keys svarlist-list-p)
  (if (atom x)
      nil
    (cons (alist-keys (svex-env-fix (car x)))
          (svex-env-keys-list (cdr x))))
  ///
  (defthm svex-env-keys-list-of-svex-alistlist-eval
    (equal (svex-env-keys-list (svex-alistlist-eval x env))
           (svex-alist-keys-list x))
    :hints(("Goal" :in-theory (enable svex-alist-keys-list
                                      svex-alistlist-eval)))))

(local (in-theory (disable hons-dups-p)))

(define no-duplicatesp-each (x)
  (if (atom x)
      t
    (and (mbe :logic (no-duplicatesp-equal (car x))
              :exec (not (hons-dups-p (car x))))
         (no-duplicatesp-each (cdr x))))
  ///
  (defthm no-duplicatesp-each-of-take
    (implies (no-duplicatesp-each x)
             (no-duplicatesp-each (take n x)))
    :hints(("Goal" :in-theory (disable acl2::take-of-too-many acl2::take-when-atom)))))


(fty::deflist svtv-name-lhs-map-list :elt-type svtv-name-lhs-map :true-listp t)

(defthm svarlist-p-alist-keys-of-svtv-name-lhs-map-fix
  (svarlist-p (alist-keys (svtv-name-lhs-map-fix x)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix alist-keys))))

(define svtv-name-lhs-map-list-all-keys ((x svtv-name-lhs-map-list-p))
  :returns (keys svarlist-p)
  (if (atom x)
      nil
    (append (alist-keys (svtv-name-lhs-map-fix (car x)))
            (svtv-name-lhs-map-list-all-keys (cdr x)))))

(define svtv-name-lhs-map-inverse-list ((x svtv-name-lhs-map-list-p))
  :returns (invlist svtv-name-lhs-map-list-p)
  (if (atom x)
      nil
    (cons (b* (((mv ?collision inverse)
                (svtv-name-lhs-map-inverse (car x))))
            inverse)
          (svtv-name-lhs-map-inverse-list (cdr x)))))

(define svtv-name-lhs-map-extract-list ((keyslist svarlist-list-p)
                                        (x svtv-name-lhs-map-p))
  :returns (maplist svtv-name-lhs-map-list-p)
  (if (atom keyslist)
      nil
    (cons (acl2::fal-extract (Svarlist-fix (car keyslist)) (svtv-name-lhs-map-fix x))
          (svtv-name-lhs-map-extract-list (cdr keyslist) x))))

