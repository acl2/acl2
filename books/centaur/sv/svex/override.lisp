; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")

(include-book "eval")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "alist-equiv")
(include-book "svex-lattice")
(include-book "std/util/defprojection" :dir :system)
(local (include-book "std/alists/hons-remove-assoc" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))


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

(define svar->svex-override-triplelist ((x svar-override-triplelist-p)
                                        (values svex-alist-p))
  :returns (triples svex-override-triplelist-p)
  (if (atom x)
      nil
    (cons (b* (((svar-override-triple x1) (car x)))
            (make-svex-override-triple :testvar x1.testvar
                                       :valvar x1.valvar
                                       :valexpr (or (svex-fastlookup x1.refvar values)
                                                    (svex-x))))
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
                                      svar->svex-override-triplelist)))))

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










(define 4vec-no-1s-p ((x 4vec-p))
  (b* (((4vec x)))
    (int= (logand x.upper x.lower) 0))
  ///
  (defthm bit?!-when-4vec-no-1s-p
    (implies (4vec-no-1s-p test)
             (equal (4vec-bit?! test override-val real-val)
                    (4vec-fix real-val)))
    :hints(("Goal" :in-theory (enable 4vec-bit?!)))))




     
      

(local
 (defthm bit?!-when-branches-same
   (equal (4vec-bit?! test real-val real-val)
          (4vec-fix real-val))
   :hints(("Goal" :in-theory (enable 4vec-bit?!))
          (bitops::logbitp-reasoning))))
 
(local (defthm equal-of-4vec-bit?!-by-example
         (implies (equal (4vec-bit?! test then1 else1) (4vec-bit?! test then2 else1))
                  (equal (equal (4vec-bit?! test then1 else2) (4vec-bit?! test then2 else2))
                         t))
         :hints(("Goal" :in-theory (enable 4vec-bit?!))
                (bitops::logbitp-reasoning))))

(local (defthm equal-of-4vec-bit?!-implies-equal-else
         (implies (and (equal (4vec-bit?! test then1 else1) (4vec-bit?! test then2 else1))
                       (4vec-p then2))
                  (equal (equal (4vec-bit?! test then1 then2) then2)
                         t))
         :hints (("goal" :use ((:instance equal-of-4vec-bit?!-by-example
                                (else2 then2)))
                  :in-theory (disable equal-of-4vec-bit?!-by-example)))))
       

(local (defthm svex-env-lookup-of-cons
         (equal (svex-env-lookup key (cons pair rest))
                (if (and (consp pair)
                         (svar-p (car pair))
                         (equal (svar-fix key) (car pair)))
                    (4vec-fix (cdr pair))
                  (svex-env-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-env-lookup)))))


(local (defthmd cons-under-iff
         (iff (cons a b) t)))


(define svex-env-keys-no-1s-p ((keys svarlist-p)
                               (env svex-env-p))
  (if (atom keys)
      t
    (and (4vec-no-1s-p (svex-env-lookup (car keys) env))
         (svex-env-keys-no-1s-p (cdr keys) env)))
  ///
  (defthm 4vec-no-1s-p-lookup-when-svex-env-keys-no-1s-p
    (implies (and (svex-env-keys-no-1s-p keys env)
                  (member-equal (svar-fix var) (svarlist-fix keys)))
             (4vec-no-1s-p (svex-env-lookup var env)))))


                               

(define svex-env-removekey ((key svar-p) (env svex-env-p))
  :returns (new-env svex-env-p)
  :prepwork ((local (defthm svex-env-p-of-hons-remove-assoc
                      (implies (svex-env-p x)
                               (svex-env-p (acl2::hons-remove-assoc k x)))
                      :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc))))))
  (acl2::hons-remove-assoc (svar-fix key) (svex-env-fix env))

  ///

  (defret svex-env-boundp-of-<fn>
    (equal (svex-env-boundp k new-env)
           (and (not (equal (svar-fix k) (svar-fix key)))
                (svex-env-boundp k env)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup k new-env)
           (if (equal (svar-fix k) (svar-fix key))
               (4vec-x)
             (svex-env-lookup k env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (local (in-theory (disable svex-env-removekey)))

  (defthm svex-env-acons-key-val-removekey-under-svex-envs-similar
    (implies (and (svar-p key)
                  (equal (4vec-fix val) (svex-env-lookup key env)))
             (svex-envs-similar (cons (cons key val)
                                      (svex-env-removekey key env))
                                env))
    :hints(("Goal" :in-theory (enable svex-envs-similar))))

  (defthm svex-env-acons-key-val-removekey-under-svex-envs-similar-fix
    (implies (and (equal (4vec-fix val) (svex-env-lookup key env)))
             (svex-envs-similar (cons (cons (svar-fix key) val)
                                      (svex-env-removekey key env))
                                env))
    :hints(("Goal" :in-theory (enable svex-envs-similar)))))


(defthmd svex-env-removekeys-in-terms-of-removekey
  (svex-envs-similar (svex-env-removekeys keys env)
                     (if (atom keys)
                         (svex-env-fix env)
                       (svex-env-removekey (car keys)
                                           (svex-env-removekeys (cdr keys) env))))
  :hints(("Goal" :in-theory (enable svex-envs-similar)))
  :rule-classes :definition)

(defcong svex-envs-similar svex-envs-similar (svex-env-removekeys keys env) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong svex-envs-similar svex-envs-similar (svex-env-removekey keys env) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))



(defthm-svex-eval-flag
  (defthm svex-eval-of-svex-env-removekey-when-not-member-vars
    (implies (not (member (svar-fix v) (svex-vars x)))
             (equal (svex-eval x (svex-env-removekey v env))
                    (svex-eval x env)))
    :hints ('(:expand ((:free (env) (svex-eval x env)))))
    :flag expr)
  (defthm svexlist-eval-of-svex-env-removekey-when-not-member-vars
    (implies (not (member (svar-fix v) (svexlist-vars x)))
             (equal (svexlist-eval x (svex-env-removekey v env))
                    (svexlist-eval x env)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env)))))
    :flag list))

(defthm-svex-eval-flag
  (defthm svex-eval-of-svex-env-removekeys-when-not-intersectp
    (implies (not (intersectp-equal (svarlist-fix vars) (svex-vars x)))
             (equal (svex-eval x (svex-env-removekeys vars env))
                    (svex-eval x env)))
    :hints ('(:expand ((:free (env) (svex-eval x env)))))
    :flag expr)
  (defthm svexlist-eval-of-svex-env-removekeys-when-not-intersectp
    (implies (not (intersectp-equal (svarlist-fix vars) (svexlist-vars x)))
             (equal (svexlist-eval x (svex-env-removekeys vars env))
                    (svexlist-eval x env)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env)))))
    :flag list))

(define svex-override-triplelist-env-ok ((x svex-override-triplelist-p)
                                         (override-env svex-env-p)
                                         (prev-env svex-env-p))
  (if (atom x)
      t
    (and (b* (((svex-override-triple trip) (car x))
              (testval (svex-env-lookup trip.testvar override-env))
              (valval (svex-env-lookup trip.valvar override-env))
              (exprval (svex-eval trip.valexpr prev-env)))
           (equal (4vec-bit?! testval valval 0)
                  (4vec-bit?! testval exprval 0)))
         (svex-override-triplelist-env-ok (cdr x) override-env prev-env)))
  ///
  (defthm svex-override-triplelist-env-ok-implies-lookup
    (implies (and (svex-override-triplelist-env-ok x override-env prev-env)
                  (svex-override-triplelist-lookup test x))
             (b* (((svex-override-triple trip) (svex-override-triplelist-lookup test x))
                  (testval (svex-env-lookup test override-env))
                  (valval (svex-env-lookup trip.valvar override-env))
                  (exprval (svex-eval trip.valexpr prev-env)))
               (and (equal (4vec-bit?! testval valval 0)
                           (4vec-bit?! testval exprval 0))
                    (equal (4vec-bit?! testval valval exprval)
                           exprval))))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup))))

  (defthm svex-override-triplelist-env-ok-of-remove-test
    (implies (and (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svex-override-triplelist-env-ok x env prev-env)
                  (not (svex-override-triplelist-lookup-valvar test x)))
             (svex-override-triplelist-env-ok x (svex-env-removekey test env) prev-env))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar
                                      svex-override-triplelist-vars))))

  (defcong svex-envs-similar equal (svex-override-triplelist-env-ok x override-env prev-env) 2)
  (defcong svex-envs-similar equal (svex-override-triplelist-env-ok x override-env prev-env) 3)

  (defthm svex-override-triplelist-env-ok-of-cons
    (equal (svex-override-triplelist-env-ok (cons trip rest) override-env prev-env)
           (and (b* (((svex-override-triple trip))
                     (testval (svex-env-lookup trip.testvar override-env))
                     (valval (svex-env-lookup trip.valvar override-env))
                     (exprval (svex-eval trip.valexpr prev-env)))
                  (equal (4vec-bit?! testval valval 0)
                         (4vec-bit?! testval exprval 0)))
                (svex-override-triplelist-env-ok rest override-env prev-env))))

  (defthm svex-override-triplelist-env-ok-of-nil
    (equal (svex-override-triplelist-env-ok nil env prev-env) t)))
                              
(define svex-override-triple-check ((test svex-p)
                                    (then svex-p)
                                    (else svex-p)
                                    (triples svex-override-triplelist-p))
  ;; returns NIL if it doesn't look like an override triple,
  ;; T if it looks like a correct override triple,
  ;; some other object representing the bad value if it looks like an incorrect override triple.
  :returns (result)
  (b* (((unless (svex-case test :var))
        nil)
       ((svex-var test))
       (triple (svex-override-triplelist-lookup test.name triples))
       ((unless triple)
        nil)
       ;; impossible when no duplicate vars
       ;; ((when (svex-override-triplelist-lookup-valvar test.name triples))
       ;;  (cons :test-var-is-also-valvar test.name))
       ((svex-override-triple triple))
       ((unless (svex-case then :var))
        (cons :test-var-with-then-nonvar (svexlist-fix (list test then else))))
       ((svex-var then))
       ((unless (equal then.name triple.valvar))
        (cons :test-var-with-then-othervar (svexlist-fix (list test then else))))
       ;; impossible when no duplicate vars
       ;; ((when (equal triple.valvar triple.testvar))
       ;;  (list :bad-triple-valvar-same-as-testvar))
       ((unless (equal (svex-fix else) triple.valexpr))
        (cons :test-var-with-else-other (svexlist-fix (list test then else))))
       ;; impossible when no duplicate vars
       ;; ((when (svex-override-triplelist-lookup triple.valvar triples))
       ;;  (cons :valvar-is-also-test-var triple.valvar))
       ;; always true when no duplicate vars
       ;; ((unless (equal triple (svex-override-triplelist-lookup-valvar triple.valvar triples)))
       ;;  (cons :valvar-is-other-valvar triple.valvar))
       )
    t)

  ///
  
  (defthm svex-override-triple-check-cdr-when-nil
    (implies (and (equal (svex-override-triple-check test then else x) nil)
                  (no-duplicatesp-equal (svex-override-triplelist-vars x)))
             (equal (svex-override-triple-check test then else (cdr x)) nil))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      svex-override-triplelist-lookup))))

  (defthm svex-override-triple-check-cdr-when-t
    (implies (and (equal (svex-override-triple-check test then else x) t)
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (not (equal (svex-override-triple-check test then else (cdr x)) nil)))
             (equal (svex-override-triple-check test then else (cdr x)) t))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      svex-override-triplelist-lookup))))

  (defthm svex-override-triple-check-of-mergesort
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (equal (svex-override-triple-check test then else (mergesort x))
                    (svex-override-triple-check test then else x))))

  (defthm svex-override-triple-check-of-append
    (implies (and (no-duplicatesp-equal (svex-override-triplelist-vars trips1))
                  (no-duplicatesp-equal (svex-override-triplelist-vars trips2))
                  (not (intersectp-equal (svex-override-triplelist-vars trips1)
                                         (svex-override-triplelist-vars trips2))))
             (equal (svex-override-triple-check test then else (append trips1 trips2))
                    (or (svex-override-triple-check test then else trips1)
                        (svex-override-triple-check test then else trips2))))
    :hints (("goal" :do-not-induct t))))
             




;; This checks whether a svex/svexlist satisfies syntactic criteria for
;; recomposition after a decomposition proof using the given overrides.
;; The correctness theorem looks like this:
;; (defret remove-override-when-<fn>
;;       (implies (and (not bad)
;;                     (svar-p test)
;;                     (svar-p valvar)
;;                     (b* ((look (svex-override-triplelist-lookup test triples)))
;;                       (and look
;;                            (b* (((svex-override-triple look)))
;;                              (and (equal valvar look.valvar)
;;                                   (equal (4vec-bit?! testval val 0)
;;                                          (4vec-bit?! testval (svex-eval look.valexpr env) 0))
;;                                   (equal (svex-override-triplelist-lookup-valvar valvar triples)
;;                                          look)
;;                                   (not (svex-override-triplelist-lookup-valvar test triples))
;;                                   (not (svex-override-triplelist-lookup valvar triples))
;;                                   (4vec-no-1s-p (svex-env-lookup test env)))))))
;;                (equal (svex-eval x (cons (cons test testval)
;;                                          (cons (cons valvar val)
;;                                                env)))
;;                       (svex-eval x env)))
;;       :hints ('(:expand <call>)
;;               (and stable-under-simplificationp
;;                    '(:expand ((:free (env) (svex-eval x env))))))
;;       :fn svex-check-overridetriples)
;; That is, you can remove an override test and override value binding from the environment
;; if the following conditions apply...
;;   0. This function's check of the expression is OK
;;   1. The test and value variables are a corresponding pair of variables from the given triples
;;      and there's no confusion where e.g. they are the same, the test variable is another triple's
;;      value variable or vice versa, etc
;;   2. The test variable's binding in the rest of the env is "false" (in this case, not 1)
;;      on all bits
;;   3. The override value's current binding in the env matches
;;      (on the bits where test's binding is 1) the evaluation of the triple's value 
;;      expression on the rest of the env.

;; This test is probably efficient enough, and could be changed to use fast
;; alist lookups into the triplelist.  But a couple of things might make it
;; hard to apply.
;;   1 -- Syntactically, the theorem just says we can take two pairs out of the env.
;;        Of course, the envs here occur under a svex-envs-similar context so this is
;;        relatively easy to expand.
;;   2 -- In practice we're going to have an evaluation involving an environment where 
;;        several overrides are added to a previous environment, and each of the override
;;        values is an evaluation of the corresponding variable's expression 
;;        using the previous environment.  This doesn't quite
;;        correspond to an iterative application of this theorem -- we need to whow that
;;        these expressions are independent of the other overrides, or at least can be
;;        topologically ordered.
(defines svex-check-overridetriples
  (define svex-check-overridetriples ((x svex-p)
                                      (triples svex-override-triplelist-p))
    :measure (two-nats-measure (svex-count x) 1)
    :returns (bad)
    (svex-case x
      :quote nil
      :var (and (or (svex-override-triplelist-lookup x.name triples)
                    (svex-override-triplelist-lookup-valvar x.name triples))
                (list :bad-var (svex-fix x)))
      :call (svex-check-overridetriples-call x triples)))
  (define svex-check-overridetriples-call ((x svex-p)
                                           (triples svex-override-triplelist-p))
    :measure (two-nats-measure (svex-count x) 0)
    :hints ((and stable-under-simplificationp
                 '(:expand ((svex-count x)))))
    :guard (svex-case x :call)
    :returns (bad)
    (b* (((unless (mbt (svex-case x :call))) (list :programming-err (svex-fix x)))
         ((svex-call x)))
      (case x.fn
        (bit?! (b* (((unless (Eql (len x.args) 3))
                     (svex-args-check-overridetriples 0 x.args triples))
                    ((list test then else) x.args)
                    (check (svex-override-triple-check test then else triples))
                    ((unless check)
                     ;; not an override triple -- just recur on args
                     (svex-args-check-overridetriples 0 x.args triples))
                    ((when (eq check t))
                     ;; good override triple -- just recur on else
                     (let ((ans (svex-check-overridetriples else triples)))
                       (and ans (cons 2 ans)))))
                 check))

        (otherwise (svex-args-check-overridetriples 0 x.args triples)))))

  (define svex-args-check-overridetriples ((n natp)
                                           (x svexlist-p)
                                           (triples svex-override-triplelist-p))
    :measure (two-nats-measure (svexlist-count x) 0)
    :returns (bad)
    (if (atom x)
        nil
      (b* ((first (svex-check-overridetriples (car x) triples)))
        (if first
            (cons (lnfix n) first)
          (svex-args-check-overridetriples (1+ (lnfix n)) (cdr x) triples)))))
  
  (define svexlist-check-overridetriples ((x svexlist-p)
                                          (triples svex-override-triplelist-p))
    :measure (two-nats-measure (svexlist-count x) 0)
    :returns (bad)
    (if (atom x)
        nil
      (or (svex-check-overridetriples (car x) triples)
          (svexlist-check-overridetriples (cdr x) triples))))
  ///

  (memoize 'svex-check-overridetriples-call)

  (local (defun count-up-cdr-down (n x)
           (if (atom x)
               n
             (count-up-cdr-down (1+ (nfix n)) (cdr x)))))
  
  (defthm svex-args-check-overridetriples-under-iff
    (iff (svex-args-check-overridetriples n x triples)
         (svexlist-check-overridetriples x triples))
    :hints (("goal" :induct (count-up-cdr-down n x)
             :expand ((svex-args-check-overridetriples n x triples)
                      (svexlist-check-overridetriples x triples)))))

  (local (defthm member-of-cons
           (iff (member k (cons a b))
                (or (equal k a)
                    (member k b)))))

  (local (defthm member-when-atom
           (implies (atom x)
                    (not (member k x)))))

  (local (in-theory (disable svex-check-overridetriples
                             svex-check-overridetriples-call
                             svexlist-check-overridetriples
                             member-equal)))

  (local (defthm svex-eval-when-var
           (implies (svex-case x :var)
                    (equal (svex-eval x env)
                           (svex-env-lookup (svex-var->name x) env)))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (defthm open-nth
           (implies (syntaxp (quotep n))
                    (equal (nth n x)
                           (if (zp n)
                               (car x)
                             (nth (1- n) (cdr x)))))))


  (local (defthm member-vars-when-not-lookups
           (implies (and (not (svex-override-triplelist-lookup var x))
                         (not (svex-override-triplelist-lookup-valvar var x)))
                    (not (member-equal var (svex-override-triplelist-vars x))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             svex-override-triplelist-lookup-valvar
                                             svex-override-triplelist-lookup)))))



  (local
   (defthm svex-override-triplelist-env-ok-implies-lookup-free
     (b* (((svex-override-triple trip) (svex-override-triplelist-lookup test x))
          (testval (svex-env-lookup test1 override-env))
          (valval (svex-env-lookup trip.valvar1 override-env))
          (exprval (svex-eval trip.valexpr1 env1)))
       (implies (and (svex-override-triplelist-env-ok x override-env prev-env)
                     (equal trip.valvar1 trip.valvar)
                     (equal test1 test)
                     (equal exprval (svex-eval trip.valexpr prev-env))
                     trip)
                (equal (4vec-bit?! testval valval exprval)
                       exprval)))))

  (std::defret-mutual remove-override-vars-when-check-overridetriples
    (defret remove-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (prev-env (svex-env-removekeys vars env)))
        (implies (and (not bad)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svex-eval x prev-env)
                        (svex-eval x env))))
      :hints ('(:expand <call>)
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env))))))
      :fn svex-check-overridetriples)
    (defret remove-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (prev-env (svex-env-removekeys vars env)))
        (implies (and (not bad)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svex-eval x prev-env)
                        (svex-eval x env))))
      :hints ('(:expand (<call>
                         (:free (env) (svex-eval x env)))
                :in-theory (enable svex-apply 4veclist-nth-safe
                                   svex-override-triple-check))
              (and stable-under-simplificationp
                   '(:in-theory (enable cons-under-iff))))
      :fn svex-check-overridetriples-call)
    (defret remove-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (prev-env (svex-env-removekeys vars env)))
        (implies (and (not bad)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svexlist-eval x prev-env)
                        (svexlist-eval x env))))
      :hints ('(:expand <call>))
      :fn svexlist-check-overridetriples)

    (defret remove-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (prev-env (svex-env-removekeys vars env)))
        (implies (and (not bad)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svexlist-eval x prev-env)
                        (svexlist-eval x env))))
      :hints ('(:expand <call>))
      :fn svex-args-check-overridetriples))
  


  ;; )

  (encapsulate nil
    (local (defthm svex-alist-eval-is-pairlis$
             (equal (svex-alist-eval x env)
                    (pairlis$ (svex-alist-keys x)
                              (svexlist-eval (svex-alist-vals x) env)))
             :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-keys svex-alist-eval
                                               svexlist-eval)))))

    (defthm remove-override-vars-from-svex-alist-eval-when-svexlist-check-overridetriples
      (b* ((vars  (svex-override-triplelist-vars triples))
           (prev-env (svex-env-removekeys vars env)))
        (implies (and (not (svexlist-check-overridetriples (svex-alist-vals x) triples))
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svex-alist-eval x prev-env)
                        (svex-alist-eval x env))))))



  ;; (std::defret-mutual remove-override-test-when-check-overridetriples
  ;;   (defret remove-override-test-when-<fn>
  ;;     (implies (and (not bad)
  ;;                   (svar-p test)
  ;;                   (no-duplicatesp-equal (svex-override-triplelist-vars triples))
  ;;                   (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples)))
  ;;                     (and look
  ;;                          (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
  ;;                                 (4vec-bit?! testval (svex-eval look.valexpr env) 0))
  ;;                          (4vec-no-1s-p (svex-env-lookup test env)))))
  ;;              (equal (svex-eval x (cons (cons test testval)
  ;;                                        ;; (cons (cons valvar val)
  ;;                                              env))
  ;;                     (svex-eval x env)))
  ;;     :hints ('(:expand <call>)
  ;;             (and stable-under-simplificationp
  ;;                  '(:expand ((:free (env) (svex-eval x env))))))
  ;;     :fn svex-check-overridetriples)
  ;;   (defret remove-override-test-when-<fn>
  ;;     (implies (and (not bad)
  ;;                   (svar-p test)
  ;;                   (no-duplicatesp-equal (svex-override-triplelist-vars triples))
  ;;                   (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples)))
  ;;                     (and look
  ;;                          (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
  ;;                                 (4vec-bit?! testval (svex-eval look.valexpr env) 0))
  ;;                          (4vec-no-1s-p (svex-env-lookup test env)))))
  ;;              (equal (svex-eval x (cons (cons test testval)
  ;;                                        ;; (cons (cons valvar val)
  ;;                                              env))
  ;;                     (svex-eval x env)))
  ;;     :hints ('(:expand (<call>
  ;;                        (:free (env) (svex-eval x env)))
  ;;               :in-theory (enable svex-apply 4veclist-nth-safe
  ;;                                  svex-override-triple-check))
  ;;             (and stable-under-simplificationp
  ;;                  '(:in-theory (enable cons-under-iff))))
  ;;     :fn svex-check-overridetriples-call)
  ;;   (defret remove-override-test-when-<fn>
  ;;     (implies (and (not bad)
  ;;                   (svar-p test)
  ;;                   (no-duplicatesp-equal (svex-override-triplelist-vars triples))
  ;;                   (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples)))
  ;;                     (and look
  ;;                          (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
  ;;                                 (4vec-bit?! testval (svex-eval look.valexpr env) 0))
  ;;                          (4vec-no-1s-p (svex-env-lookup test env)))))
  ;;              (equal (svexlist-eval x (cons (cons test testval)
  ;;                                            ;; (cons (cons valvar val)
  ;;                                            env))
  ;;                     (svexlist-eval x env)))
  ;;     :hints ('(:expand <call>))
  ;;     :fn svexlist-check-overridetriples))

  ;; (std::defret-mutual remove-override-val-when-check-overridetriples
  ;;   (defret remove-override-val-when-<fn>
  ;;     (implies (and (not bad)
  ;;                   (svar-p valvar)
  ;;                   (no-duplicatesp-equal (svex-override-triplelist-vars triples))
  ;;                   (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
  ;;                     (and look
  ;;                          (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
  ;;              (equal (svex-eval x (cons (cons valvar val) env))
  ;;                     (svex-eval x env)))
  ;;     :hints ('(:expand <call>)
  ;;             (and stable-under-simplificationp
  ;;                  '(:expand ((:free (env) (svex-eval x env))))))
  ;;     :fn svex-check-overridetriples)
  ;;   (defret remove-override-val-when-<fn>
  ;;     (implies (and (not bad)
  ;;                   (svar-p valvar)
  ;;                   (no-duplicatesp-equal (svex-override-triplelist-vars triples))
  ;;                   (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
  ;;                     (and look
  ;;                          (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
  ;;              (equal (svex-eval x (cons (cons valvar val) env))
  ;;                     (svex-eval x env)))
  ;;     :hints ('(:expand (<call>
  ;;                        (:free (env) (svex-eval x env)))
  ;;               :in-theory (enable svex-apply 4veclist-nth-safe
  ;;                                  svex-override-triple-check)))
  ;;     :fn svex-check-overridetriples-call)
  ;;   (defret remove-override-val-when-<fn>
  ;;     (implies (and (not bad)
  ;;                   (svar-p valvar)
  ;;                   (no-duplicatesp-equal (svex-override-triplelist-vars triples))
  ;;                   (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
  ;;                     (and look
  ;;                          (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
  ;;              (equal (svexlist-eval x (cons (cons valvar val) env))
  ;;                     (svexlist-eval x env)))
  ;;     :hints ('(:expand <call>)
  ;;             (and stable-under-simplificationp
  ;;                  '(:expand ((:free (env) (svex-eval x env))))))
  ;;     :fn svexlist-check-overridetriples))

  (local (defthm svexlist-check-overridetriples-when-svex-override-triple-check-is-t
           (implies (and (equal (svex-override-triple-check (car args)
                                                            (cadr args)
                                                            (caddr args)
                                                            triples)
                                t)
                         (not (svex-override-triple-check (car args)
                                                          (cadr args)
                                                          (caddr args)
                                                          (cdr triples)))
                         (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                         (equal (len args) 3)
                         (not (svex-check-overridetriples (caddr args) (cdr triples))))
                    (not (svexlist-check-overridetriples args (cdr triples))))
           :hints(("Goal" :in-theory (enable svex-override-triple-check)
                   :expand ((:free (x) (svex-check-overridetriples x (cdr triples)))
                            (svexlist-check-overridetriples args (cdr triples))
                            (svexlist-check-overridetriples (cdr args) (cdr triples))
                            (svexlist-check-overridetriples (cddr args) (cdr triples))
                            (svexlist-check-overridetriples (cdddr args) (cdr triples))
                            (:free (x) (svex-override-triplelist-lookup x triples))
                            (svex-override-triplelist-vars triples))))))

  (std::defret-mutual cdr-triples-preserves-<fn>
    (defret cdr-triples-preserves-<fn>
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
               (not (let ((triples (cdr triples))) <call>)))
      :hints ('(:expand ((:free (triples) <call>)
                         (:free (var) (svex-override-triplelist-lookup var triples))
                         (:free (var) (svex-override-triplelist-lookup-valvar var triples)))))
      :fn svex-check-overridetriples)
    (defret cdr-triples-preserves-<fn>
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
               (not (let ((triples (cdr triples))) <call>)))
      :hints ('(:expand ((:Free (triples) <call>))))
      :fn svex-check-overridetriples-call)
    (defret cdr-triples-preserves-<fn>
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
               (not (let ((triples (cdr triples))) <call>)))
      :hints ('(:expand ((:free (triples) <call>))))
      :fn svexlist-check-overridetriples)

    (defret cdr-triples-preserves-<fn>
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
               (not (let ((triples (cdr triples))) <call>)))
      :hints ('(:expand ((:free (triples) (svexlist-check-overridetriples x triples)))))
      :fn svex-args-check-overridetriples))


  
  
  (local (defthm svexlist-check-overridetriples-when-svex-override-triple-check-is-t
           (implies (and (equal (svex-override-triple-check (car args)
                                                            (cadr args)
                                                            (caddr args)
                                                            triples)
                                t)
                         (not (svex-override-triple-check (car args)
                                                          (cadr args)
                                                          (caddr args)
                                                          (cdr triples)))
                         (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                         (equal (len args) 3)
                         (not (svex-check-overridetriples (caddr args) (cdr triples))))
                    (not (svexlist-check-overridetriples args (cdr triples))))
           :hints(("Goal" :in-theory (enable svex-override-triple-check)
                   :expand ((:free (x) (svex-check-overridetriples x (cdr triples)))
                            (svexlist-check-overridetriples args (cdr triples))
                            (svexlist-check-overridetriples (cdr args) (cdr triples))
                            (svexlist-check-overridetriples (cddr args) (cdr triples))
                            (svexlist-check-overridetriples (cdddr args) (cdr triples))
                            (:free (x) (svex-override-triplelist-lookup x triples))
                            (svex-override-triplelist-vars triples))))))


  (std::defret-mutual <fn>-of-mergesort
    (defret <fn>-of-mergesort
      (implies (no-duplicatesp-equal (svex-override-triplelist-vars triples))
               (equal (let ((triples (mergesort triples))) <call>)
                      bad))
      :hints ('(:expand ((:free (triples) <call>))))
      :fn svex-check-overridetriples)
    (defret <fn>-of-mergesort
      (implies (no-duplicatesp-equal (svex-override-triplelist-vars triples))
               (equal (let ((triples (mergesort triples))) <call>)
                      bad))
      :hints ('(:expand ((:Free (triples) <call>))))
      :fn svex-check-overridetriples-call)
    (defret <fn>-of-mergesort
      (implies (no-duplicatesp-equal (svex-override-triplelist-vars triples))
               (equal (let ((triples (mergesort triples))) <call>)
                      bad))
      :hints ('(:expand ((:free (triples) <call>))))
      :fn svexlist-check-overridetriples)

    (defret <fn>-of-mergesort
      (implies (no-duplicatesp-equal (svex-override-triplelist-vars triples))
               (equal (let ((triples (mergesort triples))) <call>)
                      bad))
      :hints ('(:expand ((:free (triples) <call>))))
      :fn svex-args-check-overridetriples))

  ;; (local (defthm svex-override-triplelist-vars-of-append
  ;;          (equal (svex-override-triplelist-vars (append x y))
  ;;                 (append (svex-override-triplelist-vars x)
  ;;                         (svex-override-triplelist-vars y)))
  ;;          :hints(("Goal" :in-theory (enable svex-override-triplelist-vars)))))


  (local (defthm svexlist-check-override-triples-implies-caddr
           (implies (and (not (svexlist-check-overridetriples args triples))
                         (equal (+ 2 (len (cddr args))) 3))
                    (not (svex-check-overridetriples (caddr args) triples)))
           :hints (("goal" :expand ((svexlist-check-overridetriples args triples)
                                    (svexlist-check-overridetriples (Cdr args) triples)
                                    (svexlist-check-overridetriples (cddr args) triples))))))

  (local (defthm svex-check-overridetriples-of-append-implied
           (implies (and (svex-check-overridetriples x trips)
                         (no-duplicatesp-equal (svex-override-triplelist-vars (append more trips))))
                    (svex-check-overridetriples x (append more trips)))
           :hints (("goal" :induct (append more trips))
                   '(:use ((:instance cdr-triples-preserves-svex-check-overridetriples
                            (triples (append more trips))))
                     :in-theory (enable svex-override-triplelist-vars
                                        svex-override-triplelist-vars-of-append)))))

  (local (defthm svex-check-overridetriples-of-append-implied-2
           (implies (and (svex-check-overridetriples x trips)
                         (no-duplicatesp-equal (svex-override-triplelist-vars (append trips more))))
                    (svex-check-overridetriples x (append trips more)))
           :hints (("goal" :use ((:instance svex-check-overridetriples-of-mergesort
                                  (triples (append trips more)))
                                 (:instance svex-check-overridetriples-of-mergesort
                                  (triples (append more trips))))
                    :in-theory (e/d (svex-override-triplelist-vars-of-append)
                                    (svex-check-overridetriples-of-mergesort))))))

  (local (defthm lookup-valvar-when-no-intersecting-vars-free-1
           (implies (and (not (intersectp-equal (svex-override-triplelist-vars trips1)
                                                (svex-override-triplelist-vars trips2)))
                         (svex-override-triplelist-lookup-valvar key trips1))
                    (and (not (svex-override-triplelist-lookup key trips2))
                         (not (svex-override-triplelist-lookup-valvar key trips2))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar
                                             svex-override-triplelist-lookup
                                             svex-override-triplelist-vars)))))

  (local (defthm lookup-valvar-when-no-intersecting-vars-1
           (implies (and (not (intersectp-equal (svex-override-triplelist-vars trips1)
                                                (svex-override-triplelist-vars trips2)))
                         (svex-override-triplelist-lookup-valvar key trips2))
                    (and (not (svex-override-triplelist-lookup key trips1))
                         (not (svex-override-triplelist-lookup-valvar key trips1))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar
                                             svex-override-triplelist-lookup
                                             svex-override-triplelist-vars)))))

  (local (defthm svexlist-check-overridetriples-when-check-of-non-intersecting-t
           (implies (and (equal (svex-override-triple-check test then else triples)
                                t)
                         ;; (svex-override-triple-check test then else trips2)
                         (not (intersectp-equal 
                               (svex-override-triplelist-vars triples)
                               (svex-override-triplelist-vars trips2))))
                    (not (svex-override-triple-check test then else trips2)))
           :hints(("Goal" :in-theory (enable svex-override-triple-check)
                   :do-not-induct t))))

  (local (defthm svexlist-check-overridetriples-when-check-of-non-intersecting
           (implies (and (equal (svex-override-triple-check (car args)
                                                            (cadr args)
                                                            (caddr args)
                                                            triples)
                                t)
                         (not (intersectp-equal 
                               (svex-override-triplelist-vars triples)
                               (svex-override-triplelist-vars trips2)))
                         (equal (len args) 3))
                    (equal (svexlist-check-overridetriples args trips2)
                           (svex-check-overridetriples (caddr args) trips2)))
           :hints(("Goal" :in-theory (enable svex-override-triple-check)
                   :expand ((svex-check-overridetriples (car args) trips2)
                            (svex-check-overridetriples (cadr args) trips2)
                            (svexlist-check-overridetriples args trips2)
                            (svexlist-check-overridetriples (cdr args) trips2)
                            (svexlist-check-overridetriples (cddr args) trips2)
                            (svexlist-check-overridetriples (cdddr args) trips2))
                   :do-not-induct t))))

  (local (mutual-recursion
          (defun-nx svex-check-overridetriples-ind (x)
            (declare (xargs :measure (svex-count x)))
            (svex-case x
              :call (if (and (eq x.fn 'bit?!)
                             (eql (len x.args) 3))
                        (list (svex-check-overridetriples-ind (caddr x.args))
                              (svexlist-check-overridetriples-ind x.args))
                      (svexlist-check-overridetriples-ind x.args))
              :otherwise x))
          (defun-nx svexlist-check-overridetriples-ind (x)
            (declare (xargs :measure (svexlist-count x)))
            (if (atom x)
                x
              (list (svex-check-overridetriples-ind (car x))
                    (svexlist-check-overridetriples-ind (cdr x)))))))
  
  (flag::make-flag svex-check-overridetriples-ind-flag
                   svex-check-overridetriples-ind
                   :local t)
                      

  (defthm-svex-check-overridetriples-ind-flag
    (defthm svex-check-overridetriples-of-append
      (implies (and (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (no-duplicatesp-equal (svex-override-triplelist-vars trips2))
                    (not (intersectp-equal (svex-override-triplelist-vars triples)
                                           (svex-override-triplelist-vars trips2))))
               (and (iff (svex-check-overridetriples x (append triples trips2))
                         (or (svex-check-overridetriples x triples)
                             (svex-check-overridetriples x trips2)))
                    (iff (svex-check-overridetriples-call x (append triples trips2))
                         (or (svex-check-overridetriples-call x triples)
                             (svex-check-overridetriples-call x trips2)))))
      :hints ('(:expand ((:free (triples) (svex-check-overridetriples x triples))
                         (:free (triples) (svex-check-overridetriples-call x triples)))))
      :flag svex-check-overridetriples-ind)
    (defthm svexlist-check-overridetriples-of-append
      (implies (and (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (no-duplicatesp-equal (svex-override-triplelist-vars trips2))
                    (not (intersectp-equal (svex-override-triplelist-vars triples)
                                           (svex-override-triplelist-vars trips2))))
               (iff (svexlist-check-overridetriples x (append triples trips2))
                    (or (svexlist-check-overridetriples x triples)
                        (svexlist-check-overridetriples x trips2))))
      :hints ('(:expand ((:free (triples) (svexlist-check-overridetriples x triples)))))
      :flag svexlist-check-overridetriples-ind))

  (defthm-svex-check-overridetriples-ind-flag
    (defthm svex-check-overridetriples-of-atom
      (implies (not (consp triples))
               (and (not (svex-check-overridetriples x triples))
                    (implies (svex-case x :call)
                             (not (svex-check-overridetriples-call x triples)))))
      :hints ('(:expand ((:free (triples) (svex-check-overridetriples x triples))
                         (:free (triples) (svex-check-overridetriples-call x triples)))
                :in-theory (enable svex-override-triple-check
                                   svex-override-triplelist-lookup
                                   svex-override-triplelist-lookup-valvar)))
      :flag svex-check-overridetriples-ind)
    (defthm svexlist-check-overridetriples-of-atom
      (implies (not (consp triples))
               (not (svexlist-check-overridetriples x triples)))
      :hints ('(:expand ((:free (triples) (svexlist-check-overridetriples x triples)))))
      :flag svexlist-check-overridetriples-ind))



  (local
   (defthm svex-override-triplelist-env-ok-implies-lookup-free-2
     (b* (((svex-override-triple trip) (svex-override-triplelist-lookup test x))
          (testval (svex-env-lookup test1 override-env))
          (valval (svex-env-lookup trip.valvar1 override-env))
          (exprval (svex-eval trip.valexpr1 env1)))
       (implies (and (svex-override-triplelist-env-ok x override-env1 prev-env)
                     (equal testval (svex-env-lookup test1 override-env1))
                     (equal valval (svex-env-lookup trip.valvar1 override-env1))
                     (equal trip.valvar1 trip.valvar)
                     (equal test1 test)
                     (equal exprval (svex-eval trip.valexpr prev-env))
                     trip)
                (equal (4vec-bit?! testval valval exprval)
                       exprval)))
     :hints (("goal" :use ((:instance svex-override-triplelist-env-ok-implies-lookup
                            (override-env override-env1)))
              :in-theory (disable svex-override-triplelist-env-ok-implies-lookup)))))
  

  (std::defret-mutual un-append-override-vars-when-check-overridetriples
    (defret un-append-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (env (append (svex-env-extract vars override-env) prev-env)))
        (implies (and (not bad)
                      (svex-env-keys-no-1s-p
                       (svex-override-triplelist-testvars triples) prev-env)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svex-eval x env)
                        (svex-eval x prev-env))))
      :hints ('(:expand <call>)
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env))))))
      :fn svex-check-overridetriples)
    (defret un-append-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (env (append (svex-env-extract vars override-env) prev-env)))
        (implies (and (not bad)
                      (svex-env-keys-no-1s-p
                       (svex-override-triplelist-testvars triples) prev-env)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svex-eval x env)
                        (svex-eval x prev-env))))
      :hints ('(:expand (<call>
                         (:free (env) (svex-eval x env)))
                :in-theory (enable svex-apply 4veclist-nth-safe
                                   svex-override-triple-check))
              (and stable-under-simplificationp
                   '(:in-theory (enable cons-under-iff))))
      :fn svex-check-overridetriples-call)
    (defret un-append-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (env (append (svex-env-extract vars override-env) prev-env)))
        (implies (and (not bad)
                      (svex-env-keys-no-1s-p
                       (svex-override-triplelist-testvars triples) prev-env)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svexlist-eval x env)
                        (svexlist-eval x prev-env))))
      :hints ('(:expand <call>))
      :fn svexlist-check-overridetriples)
    (defret un-append-override-vars-when-<fn>
      (b* ((vars  (svex-override-triplelist-vars triples))
           (env (append (svex-env-extract vars override-env) prev-env)))
        (implies (and (not bad)
                      (svex-env-keys-no-1s-p
                       (svex-override-triplelist-testvars triples) prev-env)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svexlist-eval x env)
                        (svexlist-eval x prev-env))))
      :hints ('(:expand <call>))
      :fn svex-args-check-overridetriples))

  (encapsulate nil
    (local (defthm svex-alist-eval-is-pairlis$
             (equal (svex-alist-eval x env)
                    (pairlis$ (svex-alist-keys x)
                              (svexlist-eval (svex-alist-vals x) env)))
             :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-keys svex-alist-eval
                                               svexlist-eval)))))
    
    (defthm un-append-override-vars-from-svex-alist-eval-when-svexlist-check-overridetriples
      (b* ((vars  (svex-override-triplelist-vars triples))
           (env (append (svex-env-extract vars override-env) prev-env)))
        (implies (and (not (svexlist-check-overridetriples (svex-alist-vals x) triples))
                      (svex-env-keys-no-1s-p
                       (svex-override-triplelist-testvars triples) prev-env)
                      (no-duplicatesp-equal vars)
                      (svex-override-triplelist-env-ok triples env prev-env))
                 (equal (svex-alist-eval x env)
                        (svex-alist-eval x prev-env))))))
  
  
  (fty::deffixequiv-mutual svex-check-overridetriples))



;; just a debugging function
(define svex-follow-path ((x svex-p)
                          (path))
  :measure (len path)
  :hints(("Goal" :in-theory (enable len)))
  :guard-hints (("goal" :in-theory (disable nth)))
  (if (and (consp path)
           (svex-case x :call)
           (natp (car path))
           (< (car path) (len (svex-call->args x))))
      (cons (svex-fix x) (svex-follow-path (nth (car path) (svex-call->args x)) (cdr path)))
    (list (svex-fix x))))





(defretd <fn>-when-svex-envs-agree-except-overrides
  (b* ((vars  (svex-override-triplelist-vars triples)))
    (implies (and (not bad)
                  (svex-env-keys-no-1s-p
                   (svex-override-triplelist-testvars triples) prev-env)
                  (svex-envs-agree-except vars env prev-env)
                  (no-duplicatesp-equal vars)
                  (svex-override-triplelist-env-ok triples env prev-env))
             (equal (svexlist-eval x env)
                    (svexlist-eval x prev-env))))
  :hints (("goal" :use ((:instance un-append-override-vars-when-<fn>
                         (override-env env))
                        (:instance svex-envs-agree-except-commutative
                         (vars (svex-override-triplelist-vars triples))
                         (x env) (y prev-env)))
           :expand ((:with svex-envs-agree-except
                     (svex-envs-agree-except
                      (svex-override-triplelist-vars triples) prev-env env)))))
  :fn svexlist-check-overridetriples)

(encapsulate nil
  (local (defthm svex-alist-eval-is-pairlis$
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-keys svex-alist-eval
                                             svexlist-eval)))))
    
  (defthmd svex-alist-eval-when-svexlist-check-overridetriples-and-svex-envs-agree-except-overrides
    (b* ((vars  (svex-override-triplelist-vars triples)))
      (implies (and (svex-override-triplelist-env-ok triples env prev-env)
                    (svex-env-keys-no-1s-p
                     (svex-override-triplelist-testvars triples) prev-env)
                    (svex-envs-agree-except vars env prev-env)
                    (not (svexlist-check-overridetriples (svex-alist-vals x) triples))
                    (no-duplicatesp-equal vars))
               (equal (svex-alist-eval x env)
                      (svex-alist-eval x prev-env))))
    :hints(("Goal" :in-theory (enable svexlist-check-overridetriples-when-svex-envs-agree-except-overrides)))))





(defsection svexlist-check-overridetriples-of-singleton
  ;; (local
  ;;  (defthmd append-when-member
  ;;    (implies (member-equal k x)
  ;;             (equal (append (take (- (len x) (len (member-equal k x))) x)
  ;;                            (member-equal k x))
  ;;                    x))
  ;;    :hints(("Goal" :in-theory (enable take)))))

  ;; ;; (local
  ;; ;;  (defthm append-when-member
  ;; ;;    (implies (and (member-equal k x)
  ;; ;;                  (equal len  (- (len x) (len (member-equal k x)))))
  ;; ;;             (equal (append (take len x)
  ;; ;;                            (member-equal k x))
  ;; ;;                    x))))

  ;; (local (defthmd append-member-cdr
  ;;          (implies (member-equal k x)
  ;;                   (equal (append (list k) (cdr (member-equal k x)))
  ;;                          (member-equal k x)))))

  (local (defthmd append-when-member
           (implies (member-equal k x)
                    (equal (append (take (- (len x) (len (member-equal k x))) x)
                                   (list k)
                                   (cdr (member-equal k x)))
                           x))))

  (local (defthmd svexlist-check-overridetriples-of-singleton-lemma
           (implies (and (equal triples (append a b c))
                         (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
                    (iff (svexlist-check-overridetriples x triples)
                         (or (svexlist-check-overridetriples x a)
                             (svexlist-check-overridetriples x b)
                             (svexlist-check-overridetriples x c))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars-of-append)))))
  
  (defthmd svexlist-check-overridetriples-of-singleton
    (implies (and (not (svexlist-check-overridetriples x triples))
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (member-equal trip (svex-override-triplelist-fix triples)))
             (not (svexlist-check-overridetriples x (list trip))))
    :hints (("goal" :use ((:instance svexlist-check-overridetriples-of-singleton-lemma
                           (triples (svex-override-triplelist-fix triples))
                           (a (take (- (len triples)
                                       (len (member-equal trip (svex-override-triplelist-fix triples))))
                                    (svex-override-triplelist-fix triples)))
                           (b (list trip))
                           (c (cdr (member-equal trip (svex-override-triplelist-fix triples)))))
                          (:instance append-when-member
                           (k trip) (x (svex-override-triplelist-fix triples)))))))


  (defthmd svexlist-check-overridetriples-expand-consp
    (implies (and (syntaxp (not (or (and (quotep triples)
                                         (consp (unquote triples))
                                         (eq (cdr (unquote triples)) nil))
                                    (and (consp triples)
                                         (eq (car triples) 'cons)
                                         (equal (caddr triples) ''nil)))))
                  (consp triples)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
             (iff (svexlist-check-overridetriples x triples)
                  (or (svexlist-check-overridetriples x (list (car triples)))
                      (svexlist-check-overridetriples x (cdr triples)))))
    :hints (("goal" :use ((:instance svexlist-check-overridetriples-of-append
                           (triples (list (car triples)))
                           (trips2 (cdr triples))))
             :expand ((svex-override-triplelist-vars triples)
                      (svex-override-triplelist-vars (list (car triples))))
             :in-theory (disable svexlist-check-overridetriples-of-append)))))


;; Picks the first triple that fails
(define svexlist-check-overridetriples-badguy ((x svexlist-p)
                                               (triples svex-override-triplelist-p))
  :returns (badguy (iff (svex-override-triple-p badguy) badguy))
  (if (atom triples)
      nil
    (if (svexlist-check-overridetriples x (list (car triples)))
        (svex-override-triple-fix (car triples))
      (svexlist-check-overridetriples-badguy x (cdr triples))))
  ///
  (defret badguy-fails-when-svexlist-check-overridetriples
    (implies (and (svexlist-check-overridetriples x triples)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
             (and badguy
                  (member-equal badguy (svex-override-triplelist-fix triples))
                  (svexlist-check-overridetriples x (list badguy))))
    :hints(("Goal" :in-theory (enable svexlist-check-overridetriples-expand-consp)
            :expand ((svex-override-triplelist-vars triples)))))

  (defret badguy-when-not-svexlist-check-overridetriples
    (implies (and (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (svexlist-check-overridetriples x (list badguy))
                  (member-equal badguy (svex-override-triplelist-fix triples)))
             (svexlist-check-overridetriples x triples))
    :hints(("Goal" :in-theory (enable svexlist-check-overridetriples-expand-consp)
            :expand ((svex-override-triplelist-vars triples))))))
             

(defthmd svexlist-check-overridetriples-when-subset
  (implies (and (not (svexlist-check-overridetriples x triples))
                (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                (subsetp-equal (svex-override-triplelist-fix sub)
                               (svex-override-triplelist-fix triples))
                (no-duplicatesp-equal (svex-override-triplelist-vars sub)))
           (not (svexlist-check-overridetriples x sub)))
  :hints(("Goal" :use ((:instance badguy-fails-when-svexlist-check-overridetriples
                        (triples sub)))
          :in-theory (e/d (svexlist-check-overridetriples-of-singleton)
                          (badguy-fails-when-svexlist-check-overridetriples)))))

(defthm svexlist-check-overridetriples-when-set-equiv
  (implies (and (no-duplicatesp-equal (svex-override-triplelist-vars trips1))
                (no-duplicatesp-equal (svex-override-triplelist-vars trips2))
                (set-equiv (svex-override-triplelist-fix trips1)
                           (svex-override-triplelist-fix trips2)))
           (iff (svexlist-check-overridetriples x trips1)
                (svexlist-check-overridetriples x trips2)))
  :hints(("Goal" :in-theory (enable set-equiv
                                    svexlist-check-overridetriples-when-subset)))
  :rule-classes nil)





(include-book "vars")



(defines svex-vars-intersect
  :verify-guards nil
  :flag-local nil
  :prepwork ((local (Defthm intersect-nil
                      (equal (intersect nil x) nil)
                      :hints(("Goal" :in-theory (enable intersect)))))

             (local (Defthm intersect-single
                      (equal (intersect (list k) x)
                             (and (set::in k x) (list k)))
                      :hints(("Goal" :in-theory (enable intersect empty head tail setp insert)
                              :expand ((intersect (list k) x))))))

             (local (defthm hons-assoc-equal-under-iff
                      (iff (hons-assoc-equal k x)
                           (member-equal k (Alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys)))))

             (local (defthm union-of-equal-intersect
                      (implies (and (equal a (intersect b c))
                                    (equal d (intersect e c)))
                               (equal (union a d)
                                      (intersect (union b e) c)))
                      :hints(("Goal" :in-theory (enable set::double-containment
                                                        set::pick-a-point-subset-strategy))))))
  (define svex-vars-intersect
    ((x svex-p "Expression to collect variables from.")
     (tab))
    :returns
    (vars (equal vars (set::intersect (svex-vars x)
                                      (set::mergesort (alist-keys tab))))
          :hints ('(:expand ((svex-vars x)))))
    :measure (svex-count x)
    (svex-case x
      :quote nil
      :var (and (hons-get x.name tab) (list x.name))
      :call (svexlist-vars-intersect x.args tab)))

  (define svexlist-vars-intersect
    ((x svexlist-p "Expression list to collect variables from.")
     (tab))
    :returns
    (vars (equal vars (set::intersect (svexlist-vars x)
                                      (set::mergesort (alist-keys tab))))
          :hints ('(:expand ((svexlist-vars x)))))

    :measure (svexlist-count x)
    (if (atom x)
        nil
      (union (svex-vars-intersect (car x) tab)
             (svexlist-vars-intersect (cdr x) tab))))
  ///
  (verify-guards svex-vars-intersect)
  (memoize 'svex-vars-intersect)
  ///
  (deffixequiv-mutual svex-vars-intersect
    :hints (("Goal" :expand ((svexlist-fix x))))))





(local (defthmd svex-env-boundp-iff-member-alist-keys
         (iff (svex-env-boundp v x)
              (member-equal (svar-fix v) (alist-keys (svex-env-fix x))))
         :hints(("Goal" :in-theory (enable svex-env-boundp
                                           svex-env-fix
                                           alist-keys)))))

(define svar-override-triplelist-env-ok ((x svar-override-triplelist-p)
                                         (override-env svex-env-p)
                                         (ref-env svex-env-p))
  (if (atom x)
      t
    (and (b* (((svar-override-triple trip) (car x))
              (testval (svex-env-lookup trip.testvar override-env))
              (valval (svex-env-lookup trip.valvar override-env))
              (refval (svex-env-lookup trip.refvar ref-env)))
           (equal (4vec-bit?! testval valval 0)
                  (4vec-bit?! testval refval 0)))
         (svar-override-triplelist-env-ok (cdr x) override-env ref-env)))
      
  ///
  (defthm svar-override-triplelist-env-ok-in-terms-of-svex-override-triplelist-env-ok
    (equal (svar-override-triplelist-env-ok x override-env (svex-alist-eval values prev-env))
           (svex-override-triplelist-env-ok
            (svar->svex-override-triplelist x values)
            override-env prev-env))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-env-ok
                                      svar->svex-override-triplelist))))

  (local (in-theory (enable svex-env-boundp-iff-member-alist-keys)))
  
  (defthm svar-override-triplelist-env-ok-of-append-ref-envs-when-subsetp-first
    (implies (subsetp-equal (svar-override-triplelist->refvars x)
                            (alist-keys (svex-env-fix ref-env)))
             (equal (svar-override-triplelist-env-ok x override-env (append ref-env ref-env2))
                    (svar-override-triplelist-env-ok x override-env ref-env)))
    :hints(("Goal" :in-theory (enable svar-override-triplelist->refvars)))))




(define svar-override-triplelist-map-refs-to-values ((triples svar-override-triplelist-p)
                                                (ref-values svex-env-p))
  :returns (values svex-env-p)
  (if (atom triples)
      nil
    (b* (((svar-override-triple trip) (car triples))
         ;; ((unless (svex-env-boundp trip.refvar ref-values))
         ;;  (svar-override-triplelist-map-refs-to-values (cdr triples) ref-values))
         )
      (cons (cons trip.valvar (svex-env-lookup trip.refvar ref-values))
            (svar-override-triplelist-map-refs-to-values (cdr triples) ref-values))))
  ///
  (local (defthm svex-env-boundp-of-cons-2
           (equal (svex-env-boundp key (cons pair rest))
                  (if (and (consp pair) (equal (svar-fix key) (car pair)))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))
  (local (defthm svex-env-lookup-of-cons2
           (equal (svex-env-lookup v (cons x y))
                  (if (and (consp x)
                           (svar-p (car x))
                           (equal (car x) (svar-fix v)))
                      (4vec-fix (cdr x))
                    (svex-env-lookup v y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (defcong svex-envs-equivalent svex-envs-equivalent (svar-override-triplelist-map-refs-to-values triples ref-values) 2
    :hints (("goal" :induct (svar-override-triplelist-map-refs-to-values triples ref-values))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-env-boundp-of-cons-2
                                      svex-env-lookup-of-cons2))))
    :package :function)

  (defret keys-of-<fn>-strict
    ;; (implies (subsetp-equal (svar-override-triplelist->refvars triples)
    ;;                         (alist-keys (svex-env-fix ref-values)))
             (equal (alist-keys values) (svar-override-triplelist->valvars triples))
    :hints(("Goal" :in-theory (enable alist-keys
                                      svar-override-triplelist->valvars
                                      svar-override-triplelist->refvars
                                      svex-env-boundp-iff-member-alist-keys))))

  (defret boundp-of-<fn>
    ;; (implies (subsetp-equal (svar-override-triplelist->refvars triples)
    ;;                         (alist-keys (svex-env-fix ref-values)))
             (iff (svex-env-boundp var values)
                  (svar-override-triplelist-lookup-valvar var triples))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                      svar-override-triplelist->refvars
                                      svex-env-boundp-iff-member-alist-keys
                                      alist-keys)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-boundp)))))

  (defret lookup-of-<fn>
    ;; (implies (subsetp-equal (svar-override-triplelist->refvars triples)
    ;;                         (alist-keys (svex-env-fix ref-values)))
    (equal (svex-env-lookup var values)
           (b* ((look (svar-override-triplelist-lookup-valvar var triples)))
             (if look
                 (svex-env-lookup (svar-override-triple->refvar look) ref-values)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                      svar-override-triplelist->refvars
                                      svex-env-boundp-iff-member-alist-keys)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-boundp))))))


(define svar-override-triplelist-map-refs-to-intermediate-values ((triples svar-override-triplelist-p)
                                                                  (override-values svex-env-p)
                                                                  (ref-values svex-env-p))
  :returns (values svex-env-p)
  (if (atom triples)
      nil
    (b* (((svar-override-triple trip) (car triples))
         ;; ((unless (svex-env-boundp trip.refvar ref-values))
         ;;  (svar-override-triplelist-map-refs-to-intermediate-values (cdr triples) ref-values))
         )
      (cons (cons trip.valvar (4vec-bit?! (svex-env-lookup trip.testvar override-values)
                                          (svex-env-lookup trip.refvar ref-values)
                                          (svex-env-lookup trip.valvar override-values)))
            (svar-override-triplelist-map-refs-to-intermediate-values (cdr triples) override-values ref-values))))
  ///
  (local (defthm svex-env-boundp-of-cons-2
           (equal (svex-env-boundp key (cons pair rest))
                  (if (and (consp pair) (equal (svar-fix key) (car pair)))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))
  (local (defthm svex-env-lookup-of-cons2
           (equal (svex-env-lookup v (cons x y))
                  (if (and (consp x)
                           (svar-p (car x))
                           (equal (car x) (svar-fix v)))
                      (4vec-fix (cdr x))
                    (svex-env-lookup v y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (defcong svex-envs-equivalent svex-envs-equivalent (svar-override-triplelist-map-refs-to-intermediate-values triples override-values ref-values) 2
    :hints (("goal" :induct (svar-override-triplelist-map-refs-to-intermediate-values triples override-values ref-values))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-env-boundp-of-cons-2
                                      svex-env-lookup-of-cons2))))
    :package :function)
  (defcong svex-envs-equivalent svex-envs-equivalent (svar-override-triplelist-map-refs-to-intermediate-values triples override-values ref-values) 3
    :hints (("goal" :induct (svar-override-triplelist-map-refs-to-intermediate-values triples override-values ref-values))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-env-boundp-of-cons-2
                                      svex-env-lookup-of-cons2))))
    :package :function)

  (defret keys-of-<fn>-strict
    ;; (implies (subsetp-equal (svar-override-triplelist->refvars triples)
    ;;                         (alist-keys (svex-env-fix ref-values)))
             (equal (alist-keys values) (svar-override-triplelist->valvars triples))
    :hints(("Goal" :in-theory (enable alist-keys
                                      svar-override-triplelist->valvars
                                      svar-override-triplelist->refvars
                                      svex-env-boundp-iff-member-alist-keys))))

  (defret boundp-of-<fn>
    ;; (implies (subsetp-equal (svar-override-triplelist->refvars triples)
    ;;                         (alist-keys (svex-env-fix ref-values)))
             (iff (svex-env-boundp var values)
                  (svar-override-triplelist-lookup-valvar var triples))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                      svar-override-triplelist->refvars
                                      svex-env-boundp-iff-member-alist-keys
                                      alist-keys)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-boundp)))))

  (defret lookup-of-<fn>
    ;; (implies (subsetp-equal (svar-override-triplelist->refvars triples)
    ;;                         (alist-keys (svex-env-fix ref-values)))
    (equal (svex-env-lookup var values)
           (b* ((look (svar-override-triplelist-lookup-valvar var triples)))
             (if look
                 (4vec-bit?! (svex-env-lookup (svar-override-triple->testvar look) override-values)
                             (svex-env-lookup (svar-override-triple->refvar look) ref-values)
                             (svex-env-lookup (svar-override-triple->valvar look) override-values))
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                      svar-override-triplelist->refvars
                                      svex-env-boundp-iff-member-alist-keys)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-boundp))))))



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
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars svar->svex-override-triplelist)))))


(define svar-override-triplelist-env-ok-<<= ((x svar-override-triplelist-p)
                                             (override-env svex-env-p)
                                             (ref-env svex-env-p))
  (if (atom x)
      t
    (and (b* (((svar-override-triple trip) (car x))
              (testval (svex-env-lookup trip.testvar override-env))
              (valval (svex-env-lookup trip.valvar override-env))
              (refval (svex-env-lookup trip.refvar ref-env)))
           (4vec-<<= (4vec-bit?! testval valval 0)
                     (4vec-bit?! testval refval 0)))
         (svar-override-triplelist-env-ok-<<= (cdr x) override-env ref-env)))
      
  ///

  (local (in-theory (enable svex-env-boundp-iff-member-alist-keys)))
  
  (defthm svar-override-triplelist-env-ok-<<=-of-append-ref-envs-when-subsetp-first
    (implies (subsetp-equal (svar-override-triplelist->refvars x)
                            (alist-keys (svex-env-fix ref-env)))
             (equal (svar-override-triplelist-env-ok-<<= x override-env (append ref-env ref-env2))
                    (svar-override-triplelist-env-ok-<<= x override-env ref-env)))
    :hints(("Goal" :in-theory (enable svar-override-triplelist->refvars))))


  (local
   (defthm svex-env-<<=-of-cons-implies-4vec-<<=
     (implies (and (not (4vec-<<= val1 val2))
                   (svar-p var))
              (not (svex-env-<<= (cons (cons var val1) rest1)
                                 (cons (cons var val2) rest2))))
     :hints (("goal" :use ((:instance svex-env-<<=-necc
                            (x (cons (cons var val1) rest1)) (y (cons (cons var val2) rest2))
                            (var var)))))))

  (local
   (defthm svex-env-<<=-of-cons-implies-rest-<<=
     (implies (and (not (svex-env-<<= rest1 rest2))
                   (4vec-<<= (svex-env-lookup var rest1)
                             (svex-env-lookup var rest2)))
              (not (svex-env-<<= (cons (cons var val1) rest1)
                                 (cons (cons var val2) rest2))))
     :hints (("goal" :use ((:instance svex-env-<<=-necc
                            (x (cons (cons var val1) rest1))
                            (y (cons (cons var val2) rest2))
                            (var (svex-env-<<=-witness rest1 rest2))))
              :expand ((svex-env-<<= rest1 rest2))))))

  (local
   (defthm svex-env-<<=-of-cons-under-iff
     (implies (and (4vec-<<= (svex-env-lookup var rest1)
                             (svex-env-lookup var rest2))
                   (svar-p var))
              (iff (svex-env-<<= (cons (cons var val1) rest1)
                                 (cons (cons var val2) rest2))
                   (and (4vec-<<= val1 val2)
                        (svex-env-<<= rest1 rest2))))))


  (local (in-theory (disable bitops::logior-<-0-linear-2
                             bitops::logior-<-0-linear-1
                             bitops::logand->=-0-linear-2
                             bitops::logior->=-0-linear)))
  
  (local (defthm 4vec-<<=-of-bit?!
           (implies (4vec-<<= then1 then2)
                    (4vec-<<= (4vec-bit?! test then1 else) (4vec-bit?! test then2 else)))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-<<=))
                  (bitops::logbitp-reasoning))))

  (local (defthm svex-env-lookup-when-not-boundp
           (implies (not (svex-env-boundp var x))
                    (equal (svex-env-lookup var x) (4vec-x)))
           :hints(("Goal" :in-theory (e/d (svex-env-lookup svex-env-boundp)
                                          (svex-env-boundp-iff-member-alist-keys))))))

  (local (defthm not-member-valvars-when-not-member-override-vars
           (implies (not (member-equal v (svar-override-triplelist-override-vars x)))
                    (not (member-equal v (svar-override-triplelist->valvars x))))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-override-vars
                                             svar-override-triplelist->valvars)))))
  
  (defthm svar-override-triplelist-env-ok-<<=-when-valvars-<<=-map
    (implies (and (no-duplicatesp-equal (svar-override-triplelist-override-vars x))
                  (svex-env-<<=
                   (svex-env-extract (svar-override-triplelist->valvars x) override-env)
                   (svar-override-triplelist-map-refs-to-values x ref-env)))
             (svar-override-triplelist-env-ok-<<= x override-env ref-env))
    :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                      svar-override-triplelist-override-vars
                                      svex-env-extract
                                      svar-override-triplelist-map-refs-to-values
                                      svex-env-boundp-iff-member-alist-keys))))

  (defthmd svar-override-triplelist-env-ok-<<=-implies
    (implies (and (svar-override-triplelist-env-ok-<<= x override-env ref-env)
                  (member-equal triple (svar-override-triplelist-fix x)))
             (b* (((svar-override-triple trip) triple)
                  (testval (svex-env-lookup trip.testvar override-env))
                  (valval (svex-env-lookup trip.valvar override-env))
                  (refval (svex-env-lookup trip.refvar ref-env)))
               (4vec-<<= (4vec-bit?! testval valval 0)
                         (4vec-bit?! testval refval 0))))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-fix)))))



(define intermediate-override-env ((triples svar-override-triplelist-p)
                                   (all-test-vars svarlist-p)
                                   (lemma-env svex-env-p)
                                   (spec-env svex-env-p)
                                   (spec-run svex-env-p))
  :returns (override-env svex-env-p)
  (append (svex-env-extract all-test-vars lemma-env)
          (svar-override-triplelist-map-refs-to-values triples spec-run)
          (svex-env-fix spec-env))
  ///
  (defret intermediate-override-env-agrees-with-lemma-env-on-test-vars
    (svex-envs-agree all-test-vars lemma-env override-env)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable svex-envs-agree-by-witness)))))

  (local (defthm override-vars-under-set-equiv
           (acl2::set-equiv (svar-override-triplelist-override-vars x)
                            (append (svar-override-triplelist->valvars x)
                                    (svar-override-triplelist->testvars x)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                             svar-override-triplelist->testvars
                                             svar-override-triplelist-override-vars)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::set-unequal-witness-rw))))))

  (local (defthm valvar-member-when-triple-member
           (implies (member-equal (svar-override-triple-fix trip)
                                  (svar-override-triplelist-fix triples))
                    (member-equal (svar-override-triple->valvar trip)
                                  (svar-override-triplelist->valvars triples)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                             svar-override-triplelist-fix)))))
  
  (local (defthm lookup-valvar-of-valvar-when-member
           (implies (and (member-equal (svar-override-triple-fix trip)
                                       (svar-override-triplelist-fix triples))
                         (no-duplicatesp-equal (svar-override-triplelist->valvars triples)))
                    (equal (svar-override-triplelist-lookup-valvar
                            (svar-override-triple->valvar trip)
                            triples)
                           (svar-override-triple-fix trip)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                             svar-override-triplelist->valvars
                                             svar-override-triplelist-fix)))))


  (local (defthm testvar-member-when-triple-member
           (implies (member-equal (svar-override-triple-fix trip)
                                  (svar-override-triplelist-fix triples))
                    (member-equal (svar-override-triple->testvar trip)
                                  (svar-override-triplelist->testvars triples)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->testvars
                                             svar-override-triplelist-fix)))))

  
  (defret svar-override-triplelist-env-ok-of-<fn>
    (implies (and (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run)))
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars))
                  (subsetp-equal (svar-override-triplelist-fix trips)
                                 (svar-override-triplelist-fix triples))
                  (no-duplicatesp-equal (svar-override-triplelist->valvars triples))
                  (not (intersectp-equal (svar-override-triplelist->valvars triples)
                                         (svarlist-fix all-test-vars))))
             (svar-override-triplelist-env-ok
              trips override-env spec-run))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok
                                      svar-override-triplelist-fix)
            :induct (len trips))))

  
  (defret intermediate-override-env-=>>-lemma-env
    (implies (and (svex-env-<<= (svex-env-removekeys
                                 (svar-override-triplelist-override-vars triples)
                                 lemma-env)
                                spec-env)
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run)))
                  (svex-env-<<=
                   (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env)
                   (svar-override-triplelist-map-refs-to-values triples spec-run))
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars)))
             (svex-env-<<= lemma-env override-env))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (witness `(svex-env-<<=-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-env-<<=-necc
                            (x (svex-env-removekeys
                                 (svar-override-triplelist-override-vars triples)
                                 lemma-env))
                            (y spec-env)
                            (var ,witness))
                           (:instance svex-env-<<=-necc
                            (x (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env))
                            (y (svar-override-triplelist-map-refs-to-values triples spec-run))
                            (var ,witness))))))))

  (defret intermediate-override-env-agrees-with-spec-env-except-override-vars
    (implies (and (svex-envs-agree (set-difference-equal
                                    (svarlist-fix all-test-vars)
                                    (svar-override-triplelist->testvars triples))
                                   lemma-env spec-env)
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars))
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run))))
             (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
                                     override-env spec-env))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (witness `(svex-envs-agree-except-witness . ,(cdr lit))))
                   `(:expand ((:with svex-envs-agree-except-by-witness ,lit))
                     :use ((:instance lookup-when-svex-envs-agree
                            (vars (set-difference-equal
                                    (svarlist-fix all-test-vars)
                                    (svar-override-triplelist->testvars triples)))
                            (x lemma-env) (y spec-env)
                            (v ,witness))))))))


  (defret intermediate-override-env-agrees-with-reference-vars
    (implies (and (not (intersectp-equal (svarlist-fix all-test-vars)
                                         (svar-override-triplelist->valvars triples)))
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run))))
             (svex-envs-agree (svar-override-triplelist->valvars triples)
                              (svar-override-triplelist-map-refs-to-values triples spec-run)
                              override-env))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (?witness `(svex-envs-disagree-witness . ,(cdr lit))))
                   `(:expand ((:with svex-envs-agree-by-witness ,lit)))))))


  (defret extract-test-vars-of-<fn>
    (implies (subsetp-equal (svarlist-fix vars) (svarlist-fix all-test-vars))
             (equal (svex-env-extract vars override-env)
                    (svex-env-extract vars lemma-env)))
    :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix)))))


(define intermediate-override-env2 ((triples svar-override-triplelist-p)
                                   (all-test-vars svarlist-p)
                                   (lemma-env svex-env-p)
                                   (spec-env svex-env-p)
                                   (spec-run svex-env-p))
  :returns (override-env svex-env-p)
  (append (svex-env-extract all-test-vars lemma-env)
          (svar-override-triplelist-map-refs-to-intermediate-values triples lemma-env spec-run)
          (svex-env-fix spec-env))
  ///
  (defret intermediate-override-env2-agrees-with-lemma-env-on-test-vars
    (svex-envs-agree all-test-vars lemma-env override-env)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable svex-envs-agree-by-witness)))))

  (local (defthm override-vars-under-set-equiv
           (acl2::set-equiv (svar-override-triplelist-override-vars x)
                            (append (svar-override-triplelist->valvars x)
                                    (svar-override-triplelist->testvars x)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                             svar-override-triplelist->testvars
                                             svar-override-triplelist-override-vars)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::set-unequal-witness-rw))))))

  (local (defthm valvar-member-when-triple-member
           (implies (member-equal (svar-override-triple-fix trip)
                                  (svar-override-triplelist-fix triples))
                    (member-equal (svar-override-triple->valvar trip)
                                  (svar-override-triplelist->valvars triples)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                             svar-override-triplelist-fix)))))
  
  (local (defthm lookup-valvar-of-valvar-when-member
           (implies (and (member-equal (svar-override-triple-fix trip)
                                       (svar-override-triplelist-fix triples))
                         (no-duplicatesp-equal (svar-override-triplelist->valvars triples)))
                    (equal (svar-override-triplelist-lookup-valvar
                            (svar-override-triple->valvar trip)
                            triples)
                           (svar-override-triple-fix trip)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                             svar-override-triplelist->valvars
                                             svar-override-triplelist-fix)))))

  (local (defthm valvar-of-lookup-valvar-when-member
           (implies (member-equal (svar-fix var)
                                  (svar-override-triplelist->valvars triples))
                    (equal (svar-override-triple->valvar
                            (svar-override-triplelist-lookup-valvar var triples))
                           (svar-fix var)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                             svar-override-triplelist->valvars)))))


  (local (defthm testvar-member-when-triple-member
           (implies (member-equal (svar-override-triple-fix trip)
                                  (svar-override-triplelist-fix triples))
                    (member-equal (svar-override-triple->testvar trip)
                                  (svar-override-triplelist->testvars triples)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->testvars
                                             svar-override-triplelist-fix)))))


  (local (defthm bit?!-of-bit?!
           (equal (4vec-bit?! test (4vec-bit?! test then else1) else2)
                  (4vec-bit?! test then else2))
           :hints(("Goal" :in-theory (enable 4vec-bit?!))
                  (bitops::logbitp-reasoning))))

  (local (defthm bit?!-of-bit?!-2
           (equal (4vec-bit?! test then1 (4vec-bit?! test then2 else))
                  (4vec-bit?! test then1 else))
           :hints(("Goal" :in-theory (enable 4vec-bit?!))
                  (bitops::logbitp-reasoning))))

  (local (in-theory (disable bitops::logior-<-0-linear-2
                             bitops::logior-<-0-linear-1
                             bitops::logand->=-0-linear-2
                             bitops::logior->=-0-linear)))
  
  (local (defthm 4vec-<<=-of-bit?!-lemma
           (implies (4vec-<<= (4vec-bit?! test then1 else) (4vec-bit?! test then2 else))
                    (4vec-<<= then1 (4vec-bit?! test then2 then1)))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-<<=))
                  (bitops::logbitp-reasoning))))
  
  (defret svar-override-triplelist-env-ok-of-<fn>
    (implies (and (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run)))
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars))
                  (subsetp-equal (svar-override-triplelist-fix trips)
                                 (svar-override-triplelist-fix triples))
                  (no-duplicatesp-equal (svar-override-triplelist->valvars triples))
                  (not (intersectp-equal (svar-override-triplelist->valvars triples)
                                         (svarlist-fix all-test-vars))))
             (svar-override-triplelist-env-ok
              trips override-env spec-run))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok
                                      svar-override-triplelist-fix)
            :induct (len trips))))

  (local (defthm member-triples-of-lookup-valvar
           (implies (member-equal (svar-fix var) (svar-override-triplelist->valvars x))
                    (member-equal (svar-override-triplelist-lookup-valvar var x)
                                  (svar-override-triplelist-fix x)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-fix
                                             svar-override-triplelist-lookup-valvar
                                             svar-override-triplelist->valvars)))))
  
  (defret intermediate-override-env2-=>>-lemma-env
    (implies (and (svex-env-<<= (svex-env-removekeys
                                 (svar-override-triplelist-override-vars triples)
                                 lemma-env)
                                spec-env)
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run)))
                  (svar-override-triplelist-env-ok-<<= triples lemma-env spec-run)
                  ;; (svex-env-<<=
                  ;;  (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env)
                  ;;  (svar-override-triplelist-map-refs-to-values triples spec-run))
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars)))
             (svex-env-<<= lemma-env override-env))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (witness `(svex-env-<<=-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-env-<<=-necc
                            (x (svex-env-removekeys
                                 (svar-override-triplelist-override-vars triples)
                                 lemma-env))
                            (y spec-env)
                            (var ,witness))
                           (:instance svar-override-triplelist-env-ok-<<=-implies
                            (x triples)
                            (override-env lemma-env)
                            (ref-env spec-run)
                            (triple (svar-override-triplelist-lookup-valvar
                                     ,witness triples)))
                           ))))))

  (defret intermediate-override-env2-agrees-with-spec-env-except-override-vars
    (implies (and (svex-envs-agree (set-difference-equal
                                    (svarlist-fix all-test-vars)
                                    (svar-override-triplelist->testvars triples))
                                   lemma-env spec-env)
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars))
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run))))
             (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
                                     override-env spec-env))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (witness `(svex-envs-agree-except-witness . ,(cdr lit))))
                   `(:expand ((:with svex-envs-agree-except-by-witness ,lit))
                     :use ((:instance lookup-when-svex-envs-agree
                            (vars (set-difference-equal
                                    (svarlist-fix all-test-vars)
                                    (svar-override-triplelist->testvars triples)))
                            (x lemma-env) (y spec-env)
                            (v ,witness))))))))


  (defret intermediate-override-env2-agrees-with-reference-vars
    (implies (and (not (intersectp-equal (svarlist-fix all-test-vars)
                                         (svar-override-triplelist->valvars triples)))
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars))
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run))))
             (svex-envs-agree (svar-override-triplelist->valvars triples)
                              (svar-override-triplelist-map-refs-to-intermediate-values triples override-env spec-run)
                              override-env))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (?witness `(svex-envs-disagree-witness . ,(cdr lit))))
                   `(:expand ((:with svex-envs-agree-by-witness ,lit)))))))


  (defret extract-test-vars-of-<fn>
    (implies (subsetp-equal (svarlist-fix vars) (svarlist-fix all-test-vars))
             (equal (svex-env-extract vars override-env)
                    (svex-env-extract vars lemma-env)))
    :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix)))))

