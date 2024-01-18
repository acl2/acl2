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

(include-book "../svex/svex")
(include-book "std/util/defenum" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (std::add-default-post-define-hook :fix))  


(define svar->override-val ((x svar-p))
  (logbitp 0 (svar->bits x)))

(define svar->override-test ((x svar-p))
  (logbitp 1 (svar->bits x)))


(defenum svar-overridetype-p
  ( nil :val :test 3 4 5 6 7))

(fty::deflist svar-overridetypelist :elt-type svar-overridetype-p :true-listp t)

(local
 (defthm equal-of-svar-overridetype-fix
   (implies (Equal (svar-overridetype-fix x) (svar-overridetype-fix y))
            (svar-overridetype-equiv x y))
   :rule-classes :forward-chaining))


(defthmd svar-overridetype-fix-possibilities
  (or (not (svar-overridetype-fix x))
      (equal (svar-overridetype-fix x) :val)
      (equal (svar-overridetype-fix x) :test)
      (and (integerp (svar-overridetype-fix x))
           (<= 3 (svar-overridetype-fix x))
           (<= (svar-overridetype-fix x) 7)))
  :hints(("Goal" :in-theory (enable svar-overridetype-fix
                                    svar-overridetype-p)))
  :rule-classes ((:forward-chaining :trigger-terms ((svar-overridetype-fix x)))))


(define svar-override-p ((x svar-p)
                         (type svar-overridetype-p))
  (b* (((svar x))
       (bits (loghead 3 x.bits))
       (type (svar-overridetype-fix type)))
    (case type
      ((nil) (eql bits 0))
      (:val (eql bits 1))
      (:test (eql bits 2))
      (t (eql bits type))))
  ///
  

  (defthmd svar-override-p-when-other
    (implies (and (svar-override-p x type2)
                  (not (svar-overridetype-equiv type1 type2)))
             (not (svar-override-p x type1)))
    :hints(("Goal" :in-theory (enable svar-override-p)))))

(define svar-override-p* ((x svar-p)
                          (types svar-overridetypelist-p))
  (if (atom types)
      nil
    (or (svar-override-p x (car types))
        (svar-override-p* x (cdr types))))
  ///
  (defthm svar-override-p*-when-svar-override-p
    (implies (svar-override-p x type)
             (iff (svar-override-p* x types)
                  (member-equal (svar-overridetype-fix type)
                                (svar-overridetypelist-fix types))))
    :hints(("Goal" :in-theory (enable svar-overridetypelist-fix
                                      svar-override-p-when-other)))))

(define svarlist-override-p ((x svarlist-p)
                             (type svar-overridetype-p))
  (if (atom x)
      t
    (and (svar-override-p (car x) type)
         (svarlist-override-p (cdr x) type)))
  ///
  (defthm svarlist-override-p-of-append
    (iff (svarlist-override-p (append x y) type)
         (and (svarlist-override-p x type)
              (svarlist-override-p y type))))

  (defcong set-equiv equal (svarlist-override-p x type) 1
  :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                    (acl2::element-p (lambda (x) (svar-override-p x type)))
                                    (acl2::element-list-final-cdr-p (lambda (x) t))
                                    (acl2::element-list-p (lambda (x) (svarlist-override-p x type))))
                         (x x) (y x-equiv)))
           :in-theory (enable svarlist-override-p)))))

(define svarlist-override-p* ((x svarlist-p)
                              (types svar-overridetypelist-p))
  (if (atom x)
      t
    (and (svar-override-p* (car x) types)
         (svarlist-override-p* (cdr x) types)))
  ///
  (defthm svarlist-override-p*-of-append
    (iff (svarlist-override-p* (append x y) types)
         (and (svarlist-override-p* x types)
              (svarlist-override-p* y types))))

  (defcong set-equiv equal (svarlist-override-p* x types) 1
  :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                    (acl2::element-p (lambda (x) (svar-override-p* x types)))
                                    (acl2::element-list-final-cdr-p (lambda (x) t))
                                    (acl2::element-list-p (lambda (x) (svarlist-override-p* x types))))
                         (x x) (y x-equiv)))
           :in-theory (enable svarlist-override-p*)))))


(define svarlist-nonoverride-p ((x svarlist-p)
                             (type svar-overridetype-p))
  (if (atom x)
      t
    (and (not (svar-override-p (car x) type))
         (svarlist-nonoverride-p (cdr x) type)))
  ///
  (defthm svarlist-nonoverride-p-of-append
    (iff (svarlist-nonoverride-p (append x y) type)
         (and (svarlist-nonoverride-p x type)
              (svarlist-nonoverride-p y type))))

  (defcong set-equiv equal (svarlist-nonoverride-p x type) 1
  :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                    (acl2::element-p (lambda (x) (not (svar-override-p x type))))
                                    (acl2::element-list-final-cdr-p (lambda (x) t))
                                    (acl2::element-list-p (lambda (x) (svarlist-nonoverride-p x type))))
                         (x x) (y x-equiv)))
           :in-theory (enable svarlist-nonoverride-p)))))

(define svarlist-nonoverride-p* ((x svarlist-p)
                              (types svar-overridetypelist-p))
  (if (atom x)
      t
    (and (not (svar-override-p* (car x) types))
         (svarlist-nonoverride-p* (cdr x) types)))
  ///
  (defthm svarlist-nonoverride-p*-of-append
    (iff (svarlist-nonoverride-p* (append x y) types)
         (and (svarlist-nonoverride-p* x types)
              (svarlist-nonoverride-p* y types))))

  (defcong set-equiv equal (svarlist-nonoverride-p* x types) 1
  :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                    (acl2::element-p (lambda (x) (not (svar-override-p* x types))))
                                    (acl2::element-list-final-cdr-p (lambda (x) t))
                                    (acl2::element-list-p (lambda (x) (svarlist-nonoverride-p* x types))))
                         (x x) (y x-equiv)))
           :in-theory (enable svarlist-nonoverride-p*)))))
  

(define svar-change-override ((x svar-p)
                              (type svar-overridetype-p))
  :returns (new-x svar-p)
  (b* ((type (svar-overridetype-fix type))
       ((svar x))
       (new-bits (case type
                   (:val 1)
                   (:test 2)
                   ((nil) 0)
                   (t type))))
    (change-svar x :bits (logapp 3 new-bits (logtail 3 x.bits))))
  ///
  (local (in-theory (enable svar->override-test
                            svar->override-val)))

  (local (defthm unsigned-byte-3-when-<=-7
           (implies (and (<= x 7)
                         (<= 3 x)
                         (integerp x))
                    (unsigned-byte-p 3 x))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))))
  
  (defret svar-override-p-of-<fn>
    (iff (svar-override-p new-x other-type)
         (svar-overridetype-equiv other-type type))
    :hints(("Goal" :in-theory (enable svar-override-p
                                      bitops::loghead-identity
                                      svar-overridetype-fix-possibilities))))

  (defret svar-override-p*-of-<fn>
    (iff (svar-override-p* new-x types)
         (member-equal (svar-overridetype-fix type)
                       (svar-overridetypelist-fix types)))
    :hints(("Goal" :in-theory (e/d (svar-overridetypelist-fix
                                    svar-override-p*)
                                   (<fn>))
            :induct (svar-overridetypelist-fix types))))

  (local (in-theory (disable bitops::logapp-of-i-0)))

  (local (defthm equal-of-logapp
           (equal (equal (logapp n x y) z)
                  (and (integerp z)
                       (equal (loghead n x) (loghead n z))
                       (equal (ifix y) (logtail n z))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))
  
  (defthmd equal-of-svar-change-override
    (implies (syntaxp (not (and (equal type ''nil))))
             (equal (equal v1 (svar-change-override v2 type))
                    (and (svar-p v1)
                         (svar-override-p v1 type)
                         (equal (svar-change-override v1 nil)
                                (svar-change-override v2 nil)))))
    :hints(("Goal" :in-theory (enable svar-change-override
                                      svar-override-p
                                      bitops::equal-logcons-strong
                                      svar-overridetype-fix-possibilities))))

  (defthm svar-change-override-of-svar-change-override
    (equal (svar-change-override (svar-change-override x type1) type2)
           (svar-change-override x type2)))

  (defthm svar-change-override-when-svar-override-p
    (implies (svar-override-p x type)
             (equal (svar-change-override x type)
                    (svar-fix x)))
    :hints(("Goal" :in-theory (enable svar-override-p)))))


(define svarlist-change-override ((x svarlist-p)
                                  (type svar-overridetype-p))
  :returns (new-x svarlist-p)
  (if (atom x)
      nil
    (cons (svar-change-override (car x) type)
          (svarlist-change-override (cdr x) type)))
  ///
  (defret svarlist-override-p-of-<fn>
    (iff (svarlist-override-p new-x other-type)
         (or (atom x)
             (svar-overridetype-equiv other-type type)))
    :hints(("Goal" :in-theory (enable svarlist-override-p))))

  
  (defthm svarlist-change-override-when-override-p
    (implies (svarlist-override-p x type)
             (equal (svarlist-change-override x type) (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-fix
                                      svarlist-change-override
                                      svarlist-override-p))))

  (defthm svarlist-change-override-of-svarlist-change-override
    (equal (svarlist-change-override (svarlist-change-override x type1) type2)
           (svarlist-change-override x type2))))


(defprod svex-override-triple
  ((testvar svar-p)
   (valvar svar-p)
   (valexpr svex-p))
  :layout :list)

(deflist svex-override-triplelist :elt-type svex-override-triple :true-listp t)

(define svex-override-triplelist-lookup ((test svar-p) (table svex-override-triplelist-p))
  :returns (val (iff (svex-override-triple-p val) val))
  :verify-guards nil
  (mbe :logic (b* (((when (atom table)) nil)
                   ((svex-override-triple x1) (svex-override-triple-fix (car table)))
                   ((when (equal (svar-fix test) x1.testvar)) x1))
                (svex-override-triplelist-lookup test (cdr table)))
       :exec (assoc-equal test table))
  ///
  (local (defthmd svex-override-triplelist-lookup-is-assoc-equal
           (implies (and (svar-p test) (svex-override-triplelist-p table))
                    (equal (svex-override-triplelist-lookup test table)
                           (assoc-equal test table)))
           :hints (("goal" :in-theory (enable svex-override-triple->testvar
                                              svex-override-triplelist-p
                                              svex-override-triple-p)))))
  (local (defthm alistp-when-svex-override-triplelist-p
           (implies (svex-override-triplelist-p x)
                    (alistp x))
           :hints (("goal" :in-theory (enable svex-override-triplelist-p
                                              svex-override-triple-p)))))

  (defret test-var-of-<fn>
    (implies val
             (equal (svex-override-triple->testvar val) (svar-fix test))))

  (verify-guards svex-override-triplelist-lookup
    :hints (("goal" :use svex-override-triplelist-lookup-is-assoc-equal)))

  (defret member-of-<fn>
    (implies val
             (member-equal val (svex-override-triplelist-fix table))))

  (defthm svex-override-triplelist-lookup-of-append
    (equal (svex-override-triplelist-lookup key (append x y))
           (or (svex-override-triplelist-lookup key x)
               (svex-override-triplelist-lookup key y)))))


(define svex-override-triplelist-lookup-valvar ((valvar svar-p) (table svex-override-triplelist-p))
  :returns (val (iff (svex-override-triple-p val) val))
  (b* (((when (atom table)) nil)
       ((svex-override-triple x1) (svex-override-triple-fix (car table)))
       ((when (equal (svar-fix valvar) x1.valvar)) x1))
    (svex-override-triplelist-lookup-valvar valvar (cdr table)))
  ///

  (defret valvar-of-<fn>
    (implies val
             (equal (svex-override-triple->valvar val) (svar-fix valvar))))





  (defthm triplelist-lookup-valvar-of-lookup-test
    (implies (svex-override-triplelist-lookup test triples)
             (svex-override-triplelist-lookup-valvar
              (svex-override-triple->valvar (svex-override-triplelist-lookup test triples))
              triples))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup
                                      svex-override-triplelist-lookup-valvar))))

  (defthm triplelist-lookup-test-of-lookup-valvar
    (implies (svex-override-triplelist-lookup-valvar valvar triples)
             (svex-override-triplelist-lookup
              (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar triples))
              triples))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup
                                      svex-override-triplelist-lookup-valvar))))


  (defthm triplelist-lookup-valvar-of-lookup-test-free
    (implies (and (equal valvar (svex-override-triple->valvar (svex-override-triplelist-lookup test triples)))
                  (svex-override-triplelist-lookup test triples))
             (svex-override-triplelist-lookup-valvar valvar triples)))

  (defthm triplelist-lookup-test-of-lookup-valvar-free
    (implies (and (equal testvar (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar triples)))
                  (svex-override-triplelist-lookup-valvar valvar triples))
             (svex-override-triplelist-lookup
              testvar
              triples)))

  (defthm triplelist-lookup-equal-triplelist-lookup-valvar
    (implies (svex-override-triplelist-lookup test triples)
             (equal (equal (svex-override-triplelist-lookup test triples)
                           (svex-override-triplelist-lookup-valvar valvar triples))
                    (and (equal (svar-fix test) (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar triples)))
                         (equal (svar-fix valvar) (svex-override-triple->valvar (svex-override-triplelist-lookup test triples)))
                         (equal (svex-override-triple->valexpr (svex-override-triplelist-lookup test triples))
                                (svex-override-triple->valexpr (svex-override-triplelist-lookup-valvar valvar triples))))))
    :hints(("Goal" :in-theory (e/d (svex-override-triplelist-lookup-valvar
                                    svex-override-triplelist-lookup
                                    svex-override-triple-fix-redef)
                                   (svex-override-triple-of-fields)))))

  (defret member-of-<fn>
    (implies val
             (member-equal val (svex-override-triplelist-fix table))))

  (defthm svex-override-triplelist-lookup-valvar-of-append
    (equal (svex-override-triplelist-lookup-valvar key (append x y))
           (or (svex-override-triplelist-lookup-valvar key x)
               (svex-override-triplelist-lookup-valvar key y)))))


(define svex-override-triplelist-vars ((x svex-override-triplelist-p))
  :returns (vars svarlist-p)
  (b* (((when (atom x)) nil)
       ((svex-override-triple trip) (car x)))
    (cons trip.testvar (cons trip.valvar (svex-override-triplelist-vars (cdr x)))))
  ///
  (local (in-theory (enable svex-override-triplelist-lookup
                            svex-override-triplelist-lookup-valvar)))
  (defret valvar-not-test-var-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup test x))
             (not (equal (svex-override-triple->valvar
                          (svex-override-triplelist-lookup test x))
                         (svar-fix test)))))

  (defret test-var-not-valvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup-valvar valvar x))
             (not (equal (svex-override-triple->testvar
                          (svex-override-triplelist-lookup-valvar valvar x))
                         (svar-fix valvar)))))

  (defret not-lookup-when-not-member-<fn>
    (implies (not (member-equal (svar-fix var) vars))
             (and (not (svex-override-triplelist-lookup var x))
                  (not (svex-override-triplelist-lookup-valvar var x)))))

  (defret valvar-not-lookup-testvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup-valvar valvar x))
             (not (svex-override-triplelist-lookup valvar x))))

  (defret testvar-not-lookup-valvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar x))
             (not (svex-override-triplelist-lookup-valvar testvar x))))

  (defret valvar-lookup-of-testvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar x))
             (equal (svex-override-triplelist-lookup-valvar
                     (svex-override-triple->valvar (svex-override-triplelist-lookup testvar x))
                     x)
                    (svex-override-triplelist-lookup testvar x))))

  (defret testvar-lookup-of-valvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup-valvar valvar x))
             (equal (svex-override-triplelist-lookup
                     (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar x))
                     x)
                    (svex-override-triplelist-lookup-valvar valvar x))))


  (defret valvar-not-equal-test-lookup-name-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar x)
                  (svar-p testvar))
             (not (equal (svex-override-triple->valvar
                          (svex-override-triplelist-lookup testvar x))
                         testvar))))

  (defret not-valvar-of-lookup-when-not-member-<fn>
    (implies (and (not (member-equal var vars))
                  (svar-p var)
                  (svex-override-triplelist-lookup test x))
             (not (equal (svex-override-triple->valvar (svex-override-triplelist-lookup test x))
                         var))))

  (defret equal-valvar-of-lookup-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar1 x)
                  (svex-override-triplelist-lookup testvar2 x))
             (equal (equal (svex-override-triple->valvar
                            (svex-override-triplelist-lookup testvar1 x))
                           (svex-override-triple->valvar
                            (svex-override-triplelist-lookup testvar2 x)))
                    (equal (svar-fix testvar1) (svar-fix testvar2)))))


  

  (local (Defthm member-vars-when-member-has-test-var
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal var (svex-override-triple->testvar trip)))
                    (member-equal var (svex-override-triplelist-vars x)))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             svex-override-triplelist-fix)))))

  (local (defret lookup-by-member
           (implies (and (no-duplicatesp-equal vars)
                         (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->testvar trip)))
                    (equal (svex-override-triplelist-lookup var x) trip))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup)))))

  (local (defthm lookup-exists-by-member
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->testvar trip)))
                    (svex-override-triplelist-lookup var x))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup)))))

  (defretd lookup-test-when-set-equiv-and-no-duplicate-vars
    (implies (and (no-duplicatesp-equal vars)
                  (set-equiv (svex-override-triplelist-fix x)
                             (svex-override-triplelist-fix y)))
             (equal (svex-override-triplelist-lookup var y)
                    (svex-override-triplelist-lookup var x)))
    :hints (("goal" :use ((:instance member-of-svex-override-triplelist-lookup
                           (table x) (test var))
                          (:instance member-of-svex-override-triplelist-lookup
                           (table y) (test var))
                          (:instance lookup-exists-by-member
                           (x y) (trip (svex-override-triplelist-lookup var x))))
             :cases ((svex-override-triplelist-lookup var y))
             :in-theory (disable member-of-svex-override-triplelist-lookup
                                 lookup-exists-by-member))))

  (defcong set-equiv set-equiv (svex-override-triplelist-fix x) 1
    :hints (("goal" :use ((:instance
                           (:functional-instance acl2::set-equiv-congruence-over-elementlist-projection
                            (acl2::element-p (lambda (x) t))
                            (acl2::outelement-p (lambda (x) t))
                            (acl2::element-xformer svex-override-triple-fix)
                            (acl2::elementlist-projection svex-override-triplelist-fix))
                           (y x-equiv))))))


  (defthm svex-override-triplelist-lookup-of-mergesort
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (equal (svex-override-triplelist-lookup var (mergesort x))
                    (svex-override-triplelist-lookup var x)))
    :hints (("goal" :use ((:instance lookup-test-when-set-equiv-and-no-duplicate-vars
                           (y (mergesort x)))))))
  


  (local (Defthm member-vars-when-member-has-val-var
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal var (svex-override-triple->valvar trip)))
                    (member-equal var (svex-override-triplelist-vars x)))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             svex-override-triplelist-fix)))))

  (local (defret lookup-valvar-by-member
           (implies (and (no-duplicatesp-equal vars)
                         (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->valvar trip)))
                    (equal (svex-override-triplelist-lookup-valvar var x) trip))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar)))))

  (local (defthm lookup-valvar-exists-by-member
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->valvar trip)))
                    (svex-override-triplelist-lookup-valvar var x))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar)))))


  (defretd lookup-val-when-set-equiv-and-no-duplicate-vars
    (implies (and (no-duplicatesp-equal vars)
                  (set-equiv (svex-override-triplelist-fix x)
                             (svex-override-triplelist-fix y)))
             (equal (svex-override-triplelist-lookup-valvar var y)
                    (svex-override-triplelist-lookup-valvar var x)))
    :hints (("goal" :use ((:instance member-of-svex-override-triplelist-lookup-valvar
                           (table x) (valvar var))
                          (:instance member-of-svex-override-triplelist-lookup-valvar
                           (table y) (valvar var))
                          (:instance lookup-valvar-exists-by-member
                           (x y) (trip (svex-override-triplelist-lookup-valvar var x))))
             :cases ((svex-override-triplelist-lookup-valvar var y))
             :in-theory (disable member-of-svex-override-triplelist-lookup-valvar
                                 lookup-valvar-exists-by-member))))

  (defthm svex-override-triplelist-lookup-valvar-of-mergesort
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (equal (svex-override-triplelist-lookup-valvar var (mergesort x))
                    (svex-override-triplelist-lookup-valvar var x)))
    :hints (("goal" :use ((:instance lookup-val-when-set-equiv-and-no-duplicate-vars
                           (y (mergesort x)))))))

  (local (defthm member-svex-override-triplelist-vars-of-insert
           (iff (member k (svex-override-triplelist-vars (insert trip x)))
                (b* (((svex-override-triple trip)))
                  (or (equal k trip.testvar)
                      (equal k trip.valvar)
                      (member k (svex-override-triplelist-vars (sfix x))))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             insert head empty tail sfix setp)))))

  (local (defthm insert-preserves-no-duplicate-vars
           (implies (b* (((svex-override-triple trip))
                         (rest-vars  (svex-override-triplelist-vars x)))
                      (and (no-duplicatesp-equal rest-vars)
                           (not (equal trip.testvar trip.valvar))
                           (not (member-equal trip.testvar rest-vars))
                           (not (member-equal trip.valvar rest-vars))))
                    (no-duplicatesp-equal (svex-override-triplelist-vars (insert trip x))))
           :hints(("Goal" :in-theory (enable insert
                                             svex-override-triplelist-vars
                                             head empty tail)))))

  (defthm mergesort-preserves-member-vars
    (iff (member k (svex-override-triplelist-vars (mergesort x)))
         (member k (svex-override-triplelist-vars x)))
    :hints(("Goal" :in-theory (enable mergesort
                                      svex-override-triplelist-vars))))

  (defcong set-equiv set-equiv (svex-override-triplelist-vars x) 1
    :hints (("goal" :in-theory (e/d (acl2::set-unequal-witness-rw)
                                    (mergesort-preserves-member-vars))
             :use ((:instance mergesort-preserves-member-vars
                    (k (acl2::set-unequal-witness
                        (svex-override-triplelist-vars x)
                        (svex-override-triplelist-vars x-equiv)))
                    (x x))
                   (:instance mergesort-preserves-member-vars
                    (k (acl2::set-unequal-witness
                        (svex-override-triplelist-vars x)
                        (svex-override-triplelist-vars x-equiv)))
                    (x x-equiv)))
             :do-not-induct t)))

  (defthm mergesort-preserves-no-duplicate-vars
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (no-duplicatesp-equal (svex-override-triplelist-vars (mergesort x))))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      mergesort))))

  (defthm lookup-when-no-intersecting-vars-2
    (implies (and (not (intersectp-equal (svex-override-triplelist-vars trips1)
                                         (svex-override-triplelist-vars trips2)))
                  (svex-override-triplelist-lookup key trips1))
             (and (not (svex-override-triplelist-lookup key trips2))
                  (not (svex-override-triplelist-lookup-valvar key trips2)))))

  (defthm lookup-when-no-intersecting-vars-1
    (implies (and (not (intersectp-equal (svex-override-triplelist-vars trips1)
                                         (svex-override-triplelist-vars trips2)))
                  (svex-override-triplelist-lookup key trips2))
             (and (not (svex-override-triplelist-lookup key trips1))
                  (not (svex-override-triplelist-lookup-valvar key trips1)))))


  (defthmd svex-override-triplelist-vars-of-append
    (Equal (svex-override-triplelist-vars (append a b))
           (append (svex-override-triplelist-vars a)
                   (svex-override-triplelist-vars b)))))



(define svex-override-triplelist-testvars ((x svex-override-triplelist-p))
  :returns (vars svarlist-p)
  (b* (((when (atom x)) nil)
       ((svex-override-triple trip) (car x)))
    (cons trip.testvar (svex-override-triplelist-testvars (cdr x))))
  ///
  (local (in-theory (enable svex-override-triplelist-lookup
                            svex-override-triplelist-lookup-valvar)))

  (defret not-lookup-when-not-member-<fn>
    (implies (not (member-equal (svar-fix var) vars))
             (not (svex-override-triplelist-lookup var x))))

  (defret member-when-lookup-<fn>
    (implies (and (svex-override-triplelist-lookup var x)
                  (svar-p var))
             (member-equal var vars)))

  (local (defthm member-svex-override-triplelist-testvars-of-insert
           (iff (member k (svex-override-triplelist-testvars (insert trip x)))
                (b* (((svex-override-triple trip)))
                  (or (equal k trip.testvar)
                      (member k (svex-override-triplelist-testvars (sfix x))))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-testvars
                                             insert head empty tail sfix setp)))))
  
  (defthm mergesort-preserves-member-testvars
    (iff (member k (svex-override-triplelist-testvars (mergesort x)))
         (member k (svex-override-triplelist-testvars x)))
    :hints(("Goal" :in-theory (enable mergesort
                                      svex-override-triplelist-testvars))))

  (defcong set-equiv set-equiv (svex-override-triplelist-testvars x) 1
    :hints (("goal" :in-theory (e/d (acl2::set-unequal-witness-rw)
                                    (mergesort-preserves-member-testvars))
             :use ((:instance mergesort-preserves-member-testvars
                    (k (acl2::set-unequal-witness
                        (svex-override-triplelist-testvars x)
                        (svex-override-triplelist-testvars x-equiv)))
                    (x x))
                   (:instance mergesort-preserves-member-testvars
                    (k (acl2::set-unequal-witness
                        (svex-override-triplelist-testvars x)
                        (svex-override-triplelist-testvars x-equiv)))
                    (x x-equiv)))
             :do-not-induct t)))


  (defthmd svex-override-triplelist-testvars-of-append
    (Equal (svex-override-triplelist-testvars (append a b))
           (append (svex-override-triplelist-testvars a)
                   (svex-override-triplelist-testvars b)))))








(defprod svar-override-triple
  ((testvar svar-p)
   (valvar svar-p)
   (refvar svar-p))
  :layout :list)

(fty::deflist svar-override-triplelist :elt-type svar-override-triple :true-listp t)

(define svar->svex-override-triple ((x svar-override-triple-p)
                                        (values svex-alist-p))
  :returns (triple svex-override-triple-p)
  (b* (((svar-override-triple x1) x))
    (make-svex-override-triple :testvar x1.testvar
                               :valvar x1.valvar
                               :valexpr (or (svex-fastlookup x1.refvar values)
                                            (svex-x)))))

(define svar->svex-override-triplelist ((x svar-override-triplelist-p)
                                        (values svex-alist-p))
  :returns (triples svex-override-triplelist-p)
  (if (atom x)
      nil
    (cons (svar->svex-override-triple (car x) values)
          (svar->svex-override-triplelist (cdr x) values)))
  ///
  (defret len-of-<fn>
    (equal (len triples) (len x))))


(defprojection svar-override-triplelist->valvars ((x svar-override-triplelist-p))
  :returns (valvars svarlist-p)
  (svar-override-triple->valvar x))

(defprojection svar-override-triplelist->testvars ((x svar-override-triplelist-p))
  :returns (testvars svarlist-p)
  (svar-override-triple->testvar x)
  ///
  (defthm svex-override-triplelist-testvars-of-svar->svex-override-triplelist
    (equal (svex-override-triplelist-testvars (svar->svex-override-triplelist x values))
           (svar-override-triplelist->testvars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-testvars
                                      svar->svex-override-triplelist
                                      svar->svex-override-triple)))))

(defprojection svar-override-triplelist->refvars ((x svar-override-triplelist-p))
  :returns (refvars svarlist-p)
  (svar-override-triple->refvar x))

(define svar-override-triplelist-lookup-valvar ((valvar svar-p) (table svar-override-triplelist-p))
  :returns (val (iff (svar-override-triple-p val) val))
  (b* (((when (atom table)) nil)
       ((svar-override-triple x1) (svar-override-triple-fix (car table)))
       ((when (equal (svar-fix valvar) x1.valvar)) x1))
    (svar-override-triplelist-lookup-valvar valvar (cdr table)))
  ///
  (defret lookup-valvar-under-iff
    (iff val
         (member-equal (svar-fix valvar)
                       (svar-override-triplelist->valvars table)))))

(define svar-override-triplelist-lookup-refvar ((refvar svar-p) (table svar-override-triplelist-p))
  :returns (val (iff (svar-override-triple-p val) val))
  (b* (((when (atom table)) nil)
       ((svar-override-triple x1) (svar-override-triple-fix (car table)))
       ((when (equal (svar-fix refvar) x1.refvar)) x1))
    (svar-override-triplelist-lookup-refvar refvar (cdr table)))
  ///
  (defret lookup-refvar-under-iff
    (iff val
         (member-equal (svar-fix refvar)
                       (svar-override-triplelist->refvars table)))))



(define svar-override-triplelist-override-vars ((x svar-override-triplelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (b* (((svar-override-triple x1) (car x)))
      (cons x1.testvar (cons x1.valvar (svar-override-triplelist-override-vars (cdr x))))))
  ///
  (defthm svex-override-triplelist-vars-of-svar->svex-override-triplelist
    (equal (svex-override-triplelist-vars (svar->svex-override-triplelist x values))
           (svar-override-triplelist-override-vars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      svar->svex-override-triplelist
                                      svar->svex-override-triple))))

  
  (defthm svar-override-triplelist->testvars-subset-of-override-vars
    (subsetp-equal (svar-override-triplelist->testvars x) (svar-override-triplelist-override-vars x))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-override-vars svar-override-triplelist->testvars)))))


(define svarlist-to-override-triples ((x svarlist-p))
  :returns (triples svar-override-triplelist-p)
  (if (atom x)
      nil
    (cons (b* ((x1 (car x)))
            (make-svar-override-triple
             :refvar (svar-change-override x1 nil)
             :valvar (svar-change-override x1 :val)
             :testvar (svar-change-override x1 :test)))
          (svarlist-to-override-triples (cdr x))))
  ///
  (defret svar-override-triplelist->refvars-of-<fn>
    (equal (svar-override-triplelist->refvars triples)
           (svarlist-change-override x nil))
    :hints(("Goal" :in-theory (enable svarlist-change-override))))


  (local (defret member-non-override-val-valvars-of-<fn>
           (implies (not (svar-override-p v :val))
                    (not (member-equal v (svar-override-triplelist->valvars triples))))))

  (local (defret member-testvars-when-not-member-of-<fn>
           (implies (and (svarlist-override-p x nil)
                         (svar-override-p v nil)
                         (not (member-equal (svar-fix v) (svarlist-fix x))))
                    (not (member-equal (svar-change-override v :test)
                                       (svar-override-triplelist->testvars triples))))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svarlist-fix
                                             equal-of-svar-change-override)
                   :induct t))))

  (local (defret member-valvars-when-not-member-of-<fn>
           (implies (and (svarlist-override-p x nil)
                         (svar-override-p v nil)
                         (not (member-equal (svar-fix v) (svarlist-fix x))))
                    (not (member-equal (svar-change-override v :val)
                                       (svar-override-triplelist->valvars triples))))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svarlist-fix
                                             equal-of-svar-change-override)
                   :induct t))))

  (local (defret member-non-override-test-testvars-of-<fn>
           (implies (not (svar-override-p v :test))
                    (not (member-equal v (svar-override-triplelist->testvars triples))))))

  (local (defret member-override-test-when-svarlist-non-override-p
           (implies (and (svar-override-p v :test)
                         (svarlist-override-p x nil))
                    (not (member-equal v (svarlist-fix x))))
           :hints(("Goal" :in-theory (enable svarlist-override-p svarlist-fix
                                             svar-override-p-when-other)))))

  (local (defret member-override-val-when-svarlist-non-override-p
           (implies (and (svar-override-p v :val)
                         (svarlist-override-p x nil))
                    (not (member-equal v (svarlist-fix x))))
           :hints(("Goal" :in-theory (enable svarlist-override-p svarlist-fix
                                             svar-override-p-when-other)))))

  (defret no-duplicates-of-<fn>
    (implies (and (no-duplicatesp-equal (svarlist-fix x))
                  (svarlist-override-p x nil))
             (and (no-duplicatesp-equal (svar-override-triplelist->valvars triples))
                  (no-duplicatesp-equal (svar-override-triplelist->testvars triples))
                  (not (intersectp-equal (svar-override-triplelist->valvars triples)
                                         (svar-override-triplelist->testvars triples)))
                  (not (intersectp-equal (svarlist-fix x) (svar-override-triplelist->valvars triples)))
                  (not (intersectp-equal (svarlist-fix x) (svar-override-triplelist->testvars triples)))))
    :hints(("Goal" :in-theory (enable svarlist-override-p
                                      equal-of-svar-change-override
                                      svar-override-p-when-other
                                      svarlist-fix))))

  (defret testvar-override-p-of-<fn>
    (implies (svar-override-p v nil)
             (not (member-equal v (svar-override-triplelist->testvars triples)))))

  (defret testvars-dont-intersect-addr-vars-of-<fn>
    (implies (svarlist-override-p v nil)
             (and (not (intersectp-equal (svar-override-triplelist->testvars triples) v))
                  (not (intersectp-equal v (svar-override-triplelist->testvars triples)))))
    :hints(("Goal" :induct (svarlist-override-p v nil)
            :in-theory (enable svarlist-override-p))))

  (defret valvar-override-p-of-<fn>
    (implies (svar-override-p v nil)
             (not (member-equal v (svar-override-triplelist->valvars triples)))))

  (defret valvars-dont-intersect-addr-vars-of-<fn>
    (implies (svarlist-override-p v nil)
             (and (not (intersectp-equal (svar-override-triplelist->valvars triples) v))
                  (not (intersectp-equal v (svar-override-triplelist->valvars triples)))))
    :hints(("Goal" :induct (svarlist-override-p v nil)
            :in-theory (enable svarlist-override-p))))

  (defret override-var-non-addr-of-<fn>
    (implies (svar-override-p v nil)
             (not (member-equal v (svar-override-triplelist-override-vars triples))))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-override-vars))))

  (defret override-vars-dont-intersect-addr-vars-of-<fn>
    (implies (svarlist-override-p v nil)
             (and (not (intersectp-equal (svar-override-triplelist-override-vars triples) v))
                  (not (intersectp-equal v (svar-override-triplelist-override-vars triples)))))
    :hints(("Goal" :induct (svarlist-override-p v nil)
            :in-theory (enable svarlist-override-p))))

  (defretd valvars-of-<fn>
    (equal (svar-override-triplelist->valvars triples)
           (svarlist-change-override x :val))
    :hints(("Goal" :in-theory (enable svarlist-change-override))))

  (defretd testvars-of-<fn>
    (equal (svar-override-triplelist->testvars triples)
           (svarlist-change-override x :test))
    :hints(("Goal" :in-theory (enable svarlist-change-override)))))



(define svarlist-to-override-alist ((x svarlist-p))
  :returns (alist svex-alist-p)
  (if (atom x)
      nil
    (cons (b* ((x1 (car x))
               (nonovr (svar-change-override x1 nil)))
            (cons nonovr
                  (svex-call 'bit?!
                             (list (svex-var (svar-change-override x1 :test))
                                   (svex-var (svar-change-override x1 :val))
                                   (svex-var nonovr)))))
          (svarlist-to-override-alist (cdr x))))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys alist)
           (svarlist-change-override x nil))
    :hints(("Goal" :in-theory (enable svex-alist-keys
                                      svarlist-change-override)))))


(defsection member-of-svarlist-change-override

  (defthmd member-of-svarlist-change-override
    (implies (and (svar-equiv v1 (double-rewrite v))
                  (svar-override-p v1 type1)
                  (not (svar-overridetype-equiv type1 type2)))
             (not (member-equal v (svarlist-change-override x type2))))
    :hints(("Goal" :in-theory (enable svarlist-change-override
                                      equal-of-svar-change-override
                                      svar-override-p-when-other))))

  (defthmd member-when-svar-override-p-diff
    (implies (and (svar-equiv v1 (double-rewrite v))
                  (svar-override-p v1 type1)
                  (svarlist-equiv x1 (double-rewrite x))
                  (svarlist-override-p x1 type2)
                  (not (svar-overridetype-equiv type1 type2)))
             (not (member-equal v x)))
    :hints(("Goal" :in-theory (enable svarlist-override-p
                                      svar-override-p-when-other))))

  (defthmd member-when-not-svar-override-p
    (implies (and (svarlist-equiv x1 (double-rewrite x))
                  (svarlist-override-p x1 type)
                  (svar-equiv v1 (double-rewrite v))
                  (not (svar-override-p v1 type)))
             (not (member-equal v x)))
    :hints(("Goal" :in-theory (enable svarlist-override-p))))

  (defthmd member-svarlist-change-override-when-not-svar-override-p
    (implies (and (svar-equiv v1 (double-rewrite v))
                  (not (svar-override-p v1 type)))
             (not (member-equal v (svarlist-change-override x type))))
    :hints(("Goal" :in-theory (enable svarlist-change-override
                                      equal-of-svar-change-override)))))



(define svar-override-okp ((x svar-p))
  (or (svar-override-p x :test)
      (svar-override-p x :val)
      (svar-override-p x nil))
  ///
  (defthm svar-override-okp-when-svar-override-p
    (implies (and (svar-override-p x type)
                  (not (integerp (svar-overridetype-fix type))))
             (svar-override-okp x))
    :hints(("Goal" :in-theory (enable svar-override-p))))
  (defthm svar-override-okp-of-svar-change-override
    (implies (not (integerp (svar-overridetype-fix type)))
             (svar-override-okp (svar-change-override x type)))
    :hints(("Goal" :in-theory (enable svar-overridetype-fix-possibilities)))))

(define svarlist-override-okp ((x svarlist-p))
  (if (atom x)
      t
    (and (svar-override-okp (car x))
         (svarlist-override-okp (cdr x))))
  ///
  (defthm svarlist-override-okp-of-append
    (iff (svarlist-override-okp (append x y))
         (and (svarlist-override-okp x)
              (svarlist-override-okp y))))

  (defthm svarlist-override-okp-when-svarlist-override-p
    (implies (and (svarlist-override-p x type)
                  (not (integerp (svar-overridetype-fix type))))
             (svarlist-override-okp x))
    :hints(("Goal" :in-theory (enable svarlist-override-p))))

  (defthm svarlist-override-okp-of-svarlist-change-override
    (implies (not (integerp (svar-overridetype-fix type)))
             (svarlist-override-okp (svarlist-change-override x type)))
    :hints(("Goal" :in-theory (enable svarlist-change-override)))))


(define svarlist-override-okp-badguy ((x svarlist-p))
  :returns (badguy)
  (if (atom x)
      nil
    (if (svar-override-okp (car x))
        (svarlist-override-okp-badguy (cdr x))
      (svar-fix (car x))))
  ///
  (defretd svarlist-override-okp-iff-badguy
    (iff (svarlist-override-okp x)
         (or (not (member-equal badguy (svarlist-fix x)))
             (svar-override-okp badguy)))
    :hints(("Goal" :in-theory (enable svarlist-override-okp svarlist-fix))))

  (defretd svarlist-override-okp-by-badguy
    (implies (or (not (member-equal badguy (svarlist-fix x)))
                 (svar-override-okp badguy))
             (svarlist-override-okp x))
    :hints(("Goal" :in-theory (enable svarlist-override-okp-iff-badguy)))))
