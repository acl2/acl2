; GLMC -- Hardware model checking interface
; Copyright (C) 2017 Centaur Technology
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


(in-package "GL")

(include-book "centaur/gl/shape-spec" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/alists/alistp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))


(define sspec-geval-ev-alist ((x alistp) (a alistp))
  :returns (xev alistp)
  (if (Atom x)
      nil
    (cons (cons (caar x) (sspec-geval-ev (cdar x) a))
          (sspec-geval-ev-alist (cdr x) a)))
  ///
  (defthm nat-listp-alist-keys-of-sspec-geval-ev-alist
    (implies (and (nat-listp (alist-keys x))
                  (alistp x))
             (nat-listp (alist-keys (sspec-geval-ev-alist x a)))))

  (defthm sspec-geval-ev-alist-of-append
    (equal (sspec-geval-ev-alist (append x y) a)
           (append (sspec-geval-ev-alist x a)
                   (sspec-geval-ev-alist y a))))

  (defthm alist-keys-of-sspec-geval-ev-alist
    (implies (alistp x)
             (equal (alist-keys (sspec-geval-ev-alist x a))
                    (alist-keys x))))

  (defthm strip-cars-of-sspec-geval-ev-alist
    (implies (alistp x)
             (equal (strip-cars (sspec-geval-ev-alist x a))
                    (alist-keys x))))

  (defthm sspec-geval-ev-alist-of-cons
    (equal (sspec-geval-ev-alist (cons (cons var term) rest) a)
           (cons (cons var (sspec-geval-ev term a))
                 (sspec-geval-ev-alist rest a)))))


(defthm bfr-list->s-of-numlist-to-vars-set-non-member
  (implies (and (not (member (bfr-varname-fix v) vars))
                (nat-listp vars))
           (equal (bfr-list->s (numlist-to-vars vars) (bfr-set-var v val env))
                  (bfr-list->s (numlist-to-vars vars) env)))
  :hints(("Goal" :in-theory (enable bfr-list->s s-endp scdr numlist-to-vars)
          :expand ((:free (a b env) (bfr-list->s (cons a b) env))))))

(defthm bfr-list->u-of-numlist-to-vars-set-non-member
  (implies (and (not (member (bfr-varname-fix v) vars))
                (nat-listp vars))
           (equal (bfr-list->u (numlist-to-vars vars) (bfr-set-var v val env))
                  (bfr-list->u (numlist-to-vars vars) env)))
  :hints(("Goal" :in-theory (enable bfr-list->u numlist-to-vars))))

(defthm consp-of-numlist-to-vars
  (equal (consp (numlist-to-vars lst))
         (consp lst))
  :hints(("Goal" :in-theory (enable numlist-to-vars))))


(local (fty::deflist nat-list :pred nat-listp :elt-type natp :true-listp t :elementp-of-nil nil))

(define pseudo-term-alistp (x)
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (pseudo-termp (cdar x))
         (pseudo-term-alistp (cdr x))))
  ///
  (defthm lookup-in-pseudo-term-alistp
    (implies (pseudo-term-alistp x)
             (pseudo-termp (cdr (hons-assoc-equal k x)))))

  (defthm pseudo-term-alistp-of-append
    (implies (and (pseudo-term-alistp x)
                  (pseudo-term-alistp y))
             (pseudo-term-alistp (append x y))))

  (defthm pseudo-term-alistp-of-cons
    (equal (pseudo-term-alistp (cons (cons a b) c))
           (and (pseudo-termp b)
                (pseudo-term-alistp c)))))

(define integer-bits-shape-spec-invert ((idx natp)
                                        (bits nat-listp)
                                        (term pseudo-termp))
  :returns (bvar-bindings alistp)
  (if (atom bits)
      nil
    (cons (cons (lnfix (car bits)) `(logbitp ',(lnfix idx) ,term))
          (integer-bits-shape-spec-invert (1+ (lnfix idx)) (cdr bits) term)))
  ///
  (std::defret lookup-in-integer-bits-shape-spec-invert
    (implies (and (no-duplicatesp bits)
                  (nat-listp bits))
             (equal (assoc v bvar-bindings)
                    (and (member v bits)
                         (cons v `(logbitp ',(+ (nfix idx)
                                                (acl2::index-of v bits))
                                           ,term)))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (v) (acl2::index-of v bits)))))))
  
  
  (std::defret integer-bits-shape-spec-invert-correct-signed
    (implies (and (no-duplicatesp bits)
                  (nat-listp bits))
             (equal (bfr-list->s (numlist-to-vars bits)
                                 (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env))
                    (if (consp bits)
                        (logext (len bits) (logtail idx (sspec-geval-ev term a)))
                      0)))
    :hints (("goal" :in-theory (enable numlist-to-vars 
                                       slice-to-bdd-env sspec-geval-ev-alist
                                       bfr-list->s scdr s-endp)
             :induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (x) (logext 1 x))
                            (:free (n x) (logext (+ 1 n) x))
                            (:free (x y env) (bfr-list->s (cons x y) env)))))))

  (std::defret integer-bits-shape-spec-invert-correct-unsigned
    (implies (and (no-duplicatesp bits)
                  (nat-listp bits))
             (equal (bfr-list->u (numlist-to-vars bits)
                                 (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env))
                    (loghead (len bits) (logtail idx (sspec-geval-ev term a)))))
    :hints (("goal" :in-theory (enable numlist-to-vars 
                                       slice-to-bdd-env sspec-geval-ev-alist
                                       bfr-list->s scdr s-endp)
             :induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (n x) (loghead (+ 1 n) x)))))))

  (std::defret alist-keys-of-integer-bits-shape-spec-invert
    (equal (alist-keys bvar-bindings)
           (nat-list-fix bits)))

  (std::defret pseudo-term-alistp-of-integer-bits-shape-spec-invert
    (implies (pseudo-termp term)
             (pseudo-term-alistp bvar-bindings))))


(local (include-book "arithmetic/rationals" :dir :system))
(local (defthm max-numerator-of-divide
         (implies (and (natp num) (posp denom))
                  (<= (numerator (/ num denom)) num))
         :hints (("goal" :use ((:instance acl2::numerator-goes-down-by-integer-division
                                (r num) (x denom)))
                  :in-theory (disable acl2::numerator-goes-down-by-integer-division)))))

(local (defthm min-numerator-of-divide
         (implies (and (integerp num) (<= num 0) (posp denom))
                  (>= (numerator (/ num denom)) num))
         :hints (("goal" :use ((:instance acl2::numerator-goes-down-by-integer-division
                                (r num) (x denom)))
                  :in-theory (disable acl2::numerator-goes-down-by-integer-division)))))



(local
 (defthm max-denominator-of-divide
   (implies (and (integerp num) (posp denom))
            (<= (denominator (/ num denom)) denom))
   :hints (("goal" :use ((:instance max-numerator-of-divide)
                         (:instance min-numerator-of-divide)
                         (:instance rational-implies2
                          (x (/ num denom))))
            :in-theory (disable max-numerator-of-divide
                                min-numerator-of-divide
                                rational-implies2
                                acl2::numerator-goes-down-by-integer-division
                                ;; acl2::commutativity-2-of-*
                                ;; commutativity-of-*
                                acl2::*-r-denominator-r
                                ;; acl2::equal-*-/-1
                                ;; acl2::equal-*-/-2
                                ))
           (and stable-under-simplificationp
                '(:cases ((equal num 0))))
           (and stable-under-simplificationp
                '(:nonlinearp t)))))

(local (defthm numerator-of-divide-logext-less-than-ash
         (implies (and (natp n) (natp d))
                  (and (<= (- (ash 1 n))
                           (numerator (* (/ d) (logext (+ 1 n) x))))
                       (< (numerator (* (/ d) (logext (+ 1 n) x)))
                          (ash 1 n))))
         :hints (("goal" :use ((:instance acl2::signed-byte-p-logext
                                (size (+ 1 n)) (size1 (+ 1 n)) (i x))
                               (:instance max-numerator-of-divide
                                (denom d) (num (logext (+ 1 n) x)))
                               (:instance min-numerator-of-divide
                                (denom d) (num (logext (+ 1 n) x))))
                  :in-theory (e/d (signed-byte-p
                                   bitops::ash-is-expt-*-x)
                                  (acl2::signed-byte-p-logext
                                   bitops::signed-byte-p-of-logext
                                   max-numerator-of-divide
                                   min-numerator-of-divide))))))

(local (defthm numerator-of-divide-logext-less-than-ash
         (implies (and (natp n) (natp d))
                  (and (<= (- (ash 1 n))
                           (numerator (* (/ d) (logext (+ 1 n) x))))
                       (< (numerator (* (/ d) (logext (+ 1 n) x)))
                          (ash 1 n))))
         :hints (("goal" :use ((:instance acl2::signed-byte-p-logext
                                (size (+ 1 n)) (size1 (+ 1 n)) (i x))
                               (:instance max-numerator-of-divide
                                (denom d) (num (logext (+ 1 n) x)))
                               (:instance min-numerator-of-divide
                                (denom d) (num (logext (+ 1 n) x))))
                  :in-theory (e/d (signed-byte-p
                                   bitops::ash-is-expt-*-x)
                                  (acl2::signed-byte-p-logext
                                   bitops::signed-byte-p-of-logext
                                   max-numerator-of-divide
                                   min-numerator-of-divide))))))

(local (defthm denominator-of-divide-loghead-less-than-ash
         (implies (and (natp n) (integerp num))
                  (and (<= (denominator (* num (/ (loghead n x))))
                           (ash 1 n))
                       (equal (< (denominator (* num (/ (loghead n x))))
                                 (ash 1 n))
                              (not (equal n 0)))))
         :hints (("goal" :use ((:instance acl2::unsigned-byte-p-of-loghead
                                (size n) (size1 n) (i x))
                               (:instance max-denominator-of-divide
                                (denom (loghead n x))))
                  :in-theory (e/d (unsigned-byte-p
                                   bitops::ash-is-expt-*-x)
                                  (acl2::unsigned-byte-p-loghead
                                   acl2::unsigned-byte-p-of-loghead
                                   max-denominator-of-divide))))))

(local (defthm realpart-of-rational
         (implies (rationalp x)
                  (equal (realpart x) x))))



(local (defthm alist-keys-of-append
         (equal (alist-keys (append a b))
                (append (alist-keys a) (alist-keys b)))))

                    

(local (include-book "std/alists/alistp" :dir :system))

(local
 (defthm hons-assoc-equal-append
   (implies (and (alistp v1)
                 (member-equal key (alist-keys v1)))
            (equal (hons-assoc-equal key (append v1 v2))
                   (hons-assoc-equal key v1)))
   :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(local
 (defthm hons-assoc-equal-append-2
   (implies (and (alistp v1)
                 (not (member-equal key (alist-keys v1))))
            (equal (hons-assoc-equal key (append v1 v2))
                   (hons-assoc-equal key v2)))
   :hints(("Goal" :in-theory (enable hons-assoc-equal)))))







;; (local
;;  (define clause-marker (x)
;;    (declare (ignore x))
;;    :prepwork ((set-tau-auto-mode nil))
;;    'nil
;;    ///
   
;;    (defthm resolve-clause-marker
;;      (implies (acl2::rewriting-negative-literal `(clause-marker ,x))
;;               (equal (clause-marker x) nil)))

;;    (in-theory (disable (:t clause-marker) (clause-marker)))))




(defines shape-spec-invert
  :verify-guards nil
  (define shape-spec-invert ((x shape-specp "the shape spec we're traversing")
                             (term pseudo-termp
                                   "the term expressing the position we're in in
                                    terms of the state variable, e.g. @('(car (cdr
                                    st))')"))
    :returns (mv (bvar-bindings alistp)
                 (gvar-bindings alistp))
    (if (atom x)
        (mv nil nil)
      (pattern-match x
        ((g-number num) (mv (integer-bits-shape-spec-invert 0 (car num) term) nil))
        ((g-integer bits)
         (mv (integer-bits-shape-spec-invert 0 bits term) nil))
        ((g-boolean n) (mv `((,n . ,term)) nil))
        ((g-var v) (mv nil `((,v . ,term))))
        ((g-concrete &) (mv nil nil))
        ((g-ite test then else)
         (b* (((mv test-bvar-bindings test-gvar-bindings)
               (shape-spec-invert-iff test (shape-spec-oblig-term then term)))
              ((mv then-bvar-bindings then-gvar-bindings)
               (shape-spec-invert then term))
              ((mv else-bvar-bindings else-gvar-bindings)
               (shape-spec-invert else term)))
           (mv (append test-bvar-bindings then-bvar-bindings else-bvar-bindings)
               (append test-gvar-bindings then-gvar-bindings else-gvar-bindings))))
        ((g-call & args inverse)
         (b* ((nths (make-nth-terms (list (ss-unary-function-fix inverse) term) 0 (len args))))
           (shape-spec-list-invert args nths)))
        (& (b* (((mv car-bvar-bindings car-gvar-bindings)
                 (shape-spec-invert (car x) (car-term term)))
                ((mv cdr-bvar-bindings cdr-gvar-bindings)
                 (shape-spec-invert (cdr x) (cdr-term term))))
             (mv (append car-bvar-bindings cdr-bvar-bindings)
                 (append car-gvar-bindings cdr-gvar-bindings))))))
    ///
    (std::defret true-listp-of-shape-spec-invert-bvar-bindings
      (true-listp bvar-bindings)
      :rule-classes :type-prescription)

    (std::defret true-listp-of-shape-spec-invert-gvar-bindings
      (true-listp bvar-bindings)
      :rule-classes :type-prescription))

  (define shape-spec-invert-iff ((x shape-specp "the shape spec we're traversing")
                                 (term pseudo-termp
                                       "the term expressing the position we're in in
                                    terms of the state variable, e.g. @('(car (cdr
                                    st))')"))
    :returns (mv (bvar-bindings alistp)
                 (gvar-bindings alistp))
    (if (atom x)
        (mv nil nil)
      (pattern-match x
        ((g-number num)
         (mv (integer-bits-shape-spec-invert 0 (car num) `(if ,term 't 'nil)) nil))
        ((g-integer bits)
         (mv (integer-bits-shape-spec-invert 0 bits `(if ,term 't 'nil)) nil))
        ((g-boolean n) (mv `((,n . (if ,term 't 'nil))) nil))
        ((g-var v) (mv nil `((,v . (if ,term 't 'nil)))))
        ((g-concrete &) (mv nil nil))
        ((g-ite test then else)
         (b* (((mv test-bvar-bindings test-gvar-bindings)
               (shape-spec-invert-iff test (shape-spec-oblig-term-iff then term)))
              ((mv then-bvar-bindings then-gvar-bindings)
               (shape-spec-invert-iff then term))
              ((mv else-bvar-bindings else-gvar-bindings)
               (shape-spec-invert-iff else term)))
           (mv (append test-bvar-bindings then-bvar-bindings else-bvar-bindings)
               (append test-gvar-bindings then-gvar-bindings else-gvar-bindings))))
        ((g-call & args inverse)
         (b* ((nths (make-nth-terms (list (ss-unary-function-fix inverse)
                                          `(if ,term 't 'nil)) 0 (len args))))
           (shape-spec-list-invert args nths)))
        (& (b* ((term `(if ,term 't 'nil))
                ((mv car-bvar-bindings car-gvar-bindings)
                 (shape-spec-invert (car x) (car-term term)))
                ((mv cdr-bvar-bindings cdr-gvar-bindings)
                 (shape-spec-invert (cdr x) (cdr-term term))))
             (mv (append car-bvar-bindings cdr-bvar-bindings)
                 (append car-gvar-bindings cdr-gvar-bindings))))))
    ///
    (std::defret true-listp-of-shape-spec-invert-iff-bvar-bindings
      (true-listp bvar-bindings)
      :rule-classes :type-prescription)

    (std::defret true-listp-of-shape-spec-invert-iff-gvar-bindings
      (true-listp bvar-bindings)
      :rule-classes :type-prescription))

  (define shape-spec-list-invert ((x shape-spec-listp)
                                  (terms pseudo-term-listp))
    :guard (equal (len x) (len terms))
    :returns (mv (bvar-bindings alistp)
                 (gvar-bindings alistp))
    (if (atom x)
        (mv nil nil)
      (b* (((mv car-bvar-bindings car-gvar-bindings)
            (shape-spec-invert (car x) (car terms)))
           ((mv cdr-bvar-bindings cdr-gvar-bindings)
            (shape-spec-list-invert (cdr x) (cdr terms))))
        (mv (append car-bvar-bindings cdr-bvar-bindings)
            (append car-gvar-bindings cdr-gvar-bindings))))
    ///
    (std::defret true-listp-of-shape-spec-list-invert-bvar-bindings
      (true-listp bvar-bindings)
      :rule-classes :type-prescription)
    
    (std::defret true-listp-of-shape-spec-list-invert-gvar-bindings
      (true-listp bvar-bindings)
      :rule-classes :type-prescription))
  ///

  (verify-guards shape-spec-invert
    :hints (("goal" :do-not-induct t))
    :guard-debug t)

  (defthm-shape-spec-invert-flag
    (defthm bvars-of-shape-spec-invert
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert x term)))
        (implies (shape-specp x)
                 (equal (alist-keys bvar-bindings)
                        (shape-spec-indices x))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-indices x)
                              (shape-spec-invert x term)))))
      :flag shape-spec-invert)
    (defthm bvars-of-shape-spec-invert-iff
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert-iff x term)))
        (implies (shape-specp x)
                 (equal (alist-keys bvar-bindings)
                        (shape-spec-indices x))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-indices x)
                              (shape-spec-invert-iff x term)))))
      :flag shape-spec-invert-iff)
    (defthm bvars-of-shape-spec-list-invert
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-list-invert x terms)))
        (implies (shape-spec-listp x)
                 (equal (alist-keys bvar-bindings)
                        (shape-spec-list-indices x))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-list-indices x)
                              (shape-spec-list-invert x terms)
                              (shape-spec-list-invert nil terms)))))
      :flag shape-spec-list-invert))

  (defthm-shape-spec-invert-flag
    (defthm gvars-of-shape-spec-invert
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert x term)))
        (implies (shape-specp x)
                 (equal (alist-keys gvar-bindings)
                        (shape-spec-vars x))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-vars x)
                              (shape-spec-invert x term)))))
      :flag shape-spec-invert)
    (defthm gvars-of-shape-spec-invert-iff
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert-iff x term)))
        (implies (shape-specp x)
                 (equal (alist-keys gvar-bindings)
                        (shape-spec-vars x))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-vars x)
                              (shape-spec-invert-iff x term)))))
      :flag shape-spec-invert-iff)
    (defthm gvars-of-shape-spec-list-invert
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-list-invert x terms)))
        (implies (shape-spec-listp x)
                 (equal (alist-keys gvar-bindings)
                        (shape-spec-list-vars x))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-list-vars x)
                              (shape-spec-list-invert x terms)
                              (shape-spec-list-invert nil terms)))))
      :flag shape-spec-list-invert))

  (defthm pseudo-termp-of-car-term
    (implies (pseudo-termp x)
             (pseudo-termp (car-term x)))
    :hints(("Goal" :in-theory (enable car-term))))

  (defthm pseudo-termp-of-cdr-term
    (implies (pseudo-termp x)
             (pseudo-termp (car-term x)))
    :hints(("Goal" :in-theory (enable cdr-term))))

  (defthm pseudo-termp-of-fncall
    (implies (and (symbolp fn)
                  (not (eq fn 'quote))
                  (pseudo-term-listp args))
             (pseudo-termp (cons fn args))))

  (defthm pseudo-term-listp-of-cons
    (implies (and (pseudo-termp x)
                  (pseudo-term-listp y))
             (pseudo-term-listp (cons x y))))
             
  (defthm pseudo-term-listp-of-make-nth-terms
    (implies (pseudo-termp x)
             (pseudo-term-listp (make-nth-terms x n len)))
    :hints(("Goal" :in-theory (enable make-nth-terms))))


  (defthm-shape-spec-invert-flag
    (defthm pseudo-term-alistp-of-shape-spec-invert
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert x term)))
        (implies (and (pseudo-termp term)
                      (shape-specp x))
                 (and (pseudo-term-alistp bvar-bindings)
                      (pseudo-term-alistp gvar-bindings))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-invert x term)))))
      :flag shape-spec-invert)
    (defthm pseudo-term-alistp-of-shape-spec-invert-iff
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert-iff x term)))
        (implies (and (pseudo-termp term)
                      (shape-specp x))
                 (and (pseudo-term-alistp bvar-bindings)
                      (pseudo-term-alistp gvar-bindings))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-invert-iff x term)))))
      :flag shape-spec-invert-iff)
    (defthm pseudo-term-alistp-of-shape-spec-list-invert
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-list-invert x terms)))
        (implies (and (pseudo-term-listp terms)
                      (shape-spec-listp x))
                 (and (pseudo-term-alistp bvar-bindings)
                      (pseudo-term-alistp gvar-bindings))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((shape-spec-list-invert x terms)
                              (shape-spec-list-invert x nil)))))
      :flag shape-spec-list-invert))
  


  (local (defthm g-keyword-symbolp-of-shape-spec-to-gobj
           (equal (g-keyword-symbolp (shape-spec-to-gobj x))
                  (g-keyword-symbolp x))
           :hints(("Goal" :expand ((shape-spec-to-gobj x))))))

  (local (defthm g-keyword-symbolp-of-shape-spec-to-gobj-2
           (implies (and (g-keyword-symbolp key)
                         (not (g-keyword-symbolp x)))
                    (not (equal (shape-spec-to-gobj x) key)))
           :hints(("Goal" :expand ((shape-spec-to-gobj x))))))


  ;; (local
  ;;  (progn
  ;;    (local (in-theory (enable shape-spec-call-free)))

  ;;    (defthmd shape-spec-to-gobj-of-cons
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call))))
  ;;               (equal (shape-spec-to-gobj x)
  ;;                      (gl-cons (shape-spec-to-gobj (car x))
  ;;                               (shape-spec-to-gobj (cdr x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-to-gobj shape-spec-call-free))))

  ;;    (defthm shape-spec-indices-of-cons
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call))))
  ;;               (equal (shape-spec-indices x)
  ;;                      (append (shape-spec-indices (car x))
  ;;                              (shape-spec-indices (cdr x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-indices shape-spec-call-free))))

  ;;    (defthm shape-spec-vars-of-cons
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call))))
  ;;               (equal (shape-spec-vars x)
  ;;                      (append (shape-spec-vars (car x))
  ;;                              (shape-spec-vars (cdr x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-vars shape-spec-call-free))))

  ;;    (defthm shape-specp-car/cdr
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call)))
  ;;                    (shape-specp x))
  ;;               (and (shape-specp (car x))
  ;;                    (shape-specp (cdr x))))
  ;;      :hints(("Goal" :in-theory (enable shape-specp))))

  ;;    (defthmd shape-spec-to-gobj-of-g-call
  ;;      (implies (equal (tag x) :g-call)
  ;;               (equal (shape-spec-to-gobj x)
  ;;                      (g-apply (g-call->fn x)
  ;;                               (shape-spec-to-gobj-list (g-call->args x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

  ;;    (defthm shape-spec-indices-of-g-call
  ;;      (implies (equal (tag x) :g-call)
  ;;               (equal (shape-spec-indices x)
  ;;                      (shape-spec-list-indices (g-call->args x))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-indices))))

  ;;    (defthm shape-spec-vars-of-g-call
  ;;      (implies (equal (tag x) :g-call)
  ;;               (equal (shape-spec-vars x)
  ;;                      (shape-spec-list-vars (g-call->args x))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-vars))))

  ;;    (defthm shape-specp-g-call
  ;;      (implies (and (equal (tag x) :g-call)
  ;;                    (shape-specp x))
  ;;               (and (shape-spec-listp (g-call->args x))
  ;;                    (symbolp (g-call->fn x))
  ;;                    (not (equal (g-call->fn x) 'quote))
  ;;                    (ss-unary-functionp (g-call->inverse x))))
  ;;      :hints(("Goal" :in-theory (enable shape-specp))))

  ;;    ;; (defthm shape-spec-to-gobj-of-g-ite
  ;;    ;;   (implies (equal (tag x) :g-ite)
  ;;    ;;            (equal (shape-spec-to-gobj x)
  ;;    ;;                   (g-ite (shape-spec-to-gobj (g-ite->test x))
  ;;    ;;                          (shape-spec-to-gobj (g-ite->then x))
  ;;    ;;                          (shape-spec-to-gobj (g-ite->else x)))))
  ;;    ;;   :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

  ;;    (defthm shape-spec-indices-of-g-ite
  ;;      (implies (equal (tag x) :g-ite)
  ;;               (equal (shape-spec-indices x)
  ;;                      (append (shape-spec-indices (g-ite->test x))
  ;;                              (shape-spec-indices (g-ite->then x))
  ;;                              (shape-spec-indices (g-ite->else x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-indices))))

  ;;    (defthm shape-spec-vars-of-g-ite
  ;;      (implies (equal (tag x) :g-ite)
  ;;               (equal (shape-spec-vars x)
  ;;                      (append (shape-spec-vars (g-ite->test x))
  ;;                              (shape-spec-vars (g-ite->then x))
  ;;                              (shape-spec-vars (g-ite->else x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-vars))))

  ;;    (defthm shape-specp-g-ite
  ;;      (implies (and (equal (tag x) :g-ite)
  ;;                    (shape-specp x))
  ;;               (and (shape-specp (g-ite->test x))
  ;;                    (shape-specp (g-ite->then x))
  ;;                    (shape-specp (g-ite->else x))))
  ;;      :hints(("Goal" :in-theory (enable shape-specp))))

  ;;    (local (defthm g-keyword-symbolp-compound-recognizer
  ;;             (implies (g-keyword-symbolp x)
  ;;                      (and (symbolp x)
  ;;                           (not (booleanp x))))
  ;;             :rule-classes :compound-recognizer))
  ;;    (local (defthmd shape-spec-to-gobj-when-atom
  ;;             (implies (atom x)
  ;;                      (equal (shape-spec-to-gobj x) x))
  ;;             :hints(("Goal" :in-theory (enable shape-spec-to-gobj)))
  ;;             :rule-classes ((:rewrite :backchain-limit-lst 0))))))


  ;; (local (defthmd sspec-geval-of-atom
  ;;          (implies (atom x)
  ;;                   (equal (sspec-geval x env) x))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval)))))

  ;; (local (defthm sspec-geval-of-cons-shape-spec
  ;;          (implies (and (consp x)
  ;;                        (not (equal (tag x) :g-number))
  ;;                        (not (equal (tag x) :g-integer))
  ;;                        (not (equal (tag x) :g-integer?))
  ;;                        (not (equal (tag x) :g-boolean))
  ;;                        (not (equal (tag x) :g-var))
  ;;                        (not (equal (tag x) :g-concrete))
  ;;                        (not (equal (tag x) :g-ite))
  ;;                        (not (equal (tag x) :g-call)))
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (cons (sspec-geval (shape-spec-to-gobj (car x)) env)
  ;;                                (sspec-geval (shape-spec-to-gobj (cdr x)) env))))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj)))))

  ;; (local (defthm sspec-geval-of-g-ite-shape-spec
  ;;          (implies (equal (tag x) :g-ite)
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (if (sspec-geval (shape-spec-to-gobj (g-ite->test x)) env)
  ;;                              (sspec-geval (shape-spec-to-gobj (g-ite->then x)) env)
  ;;                            (sspec-geval (shape-spec-to-gobj (g-ite->else x)) env))))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj)))))

  ;; (local (defthm sspec-geval-of-g-concrete-shape-spec
  ;;          (implies (equal (tag x) :g-concrete)
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (g-concrete->obj x)))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj)))))

  ;; (local (defthm sspec-geval-of-g-call-shape-spec
  ;;          (implies (equal (tag x) :g-call)
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (if (eq (g-call->fn x) 'quote)
  ;;                              nil
  ;;                            (sspec-geval-ev (cons (g-call->fn x)
  ;;                                                  (kwote-lst (sspec-geval-list
  ;;                                                              (shape-spec-to-gobj-list (g-call->args x))
  ;;                                                              env)))
  ;;                                            nil))))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj)))))

  ;; (local (defthm sspec-geval-of-g-var-shape-spec
  ;;          (implies (equal (tag x) :g-var)
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (cdr (hons-assoc-equal (g-var->name x) (cdr env)))))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj)))))

  ;; (local (defthm sspec-geval-of-g-boolean-shape-spec
  ;;          (implies (equal (tag x) :g-boolean)
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (bfr-lookup (nfix (g-boolean->bool x)) (car env))))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj)))))

  ;; (local (defthm sspec-geval-of-atom-shape-spec
  ;;          (implies (not (consp x))
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          x))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj)))))

  ;; (local (defthm loghead-of-bfr-list->u
  ;;          (implies (equal len (len x))
  ;;                   (equal (loghead len (bfr-list->u x env))
  ;;                          (bfr-list->u x env)))
  ;;          :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs
  ;;                                             bfr-list->u)))))

  ;; (local (defthm sspec-geval-of-g-integer?-shape-spec
  ;;          (implies (equal (tag x) :g-integer?)
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (maybe-integer (logapp (len (g-integer?->bits x))
  ;;                                                 (bfr-list->u (numlist-to-vars (g-integer?->bits x)) (car env))
  ;;                                                 (int-set-sign
  ;;                                                  (bfr-lookup (nfix (g-integer?->sign x)) (car env))
  ;;                                                  (cdr (hons-assoc-equal (g-integer?->var x) (cdr env)))))
  ;;                                         (cdr (hons-assoc-equal (g-integer?->var x) (cdr env)))
  ;;                                         (bfr-lookup (nfix (g-integer?->intp x)) (car env)))))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval sspec-geval-list shape-spec-to-gobj
  ;;                                            break-g-number)))))

  ;; (local (defthm sspec-geval-of-g-integer-shape-spec
  ;;          (implies (equal (tag x) :g-integer)
  ;;                   (equal (sspec-geval (shape-spec-to-gobj x) env)
  ;;                          (logapp (len (g-integer->bits x))
  ;;                                  (bfr-list->u (numlist-to-vars (g-integer->bits x)) (car env))
  ;;                                  (int-set-sign
  ;;                                   (bfr-lookup (nfix (g-integer->sign x)) (car env))
  ;;                                   (cdr (hons-assoc-equal (g-integer->var x) (cdr env)))))))
  ;;          :hints(("Goal" :in-theory (enable sspec-geval sspec-geval-list shape-spec-to-gobj
  ;;                                            break-g-number)))))

  ;; (local (def-ruleset! sspec-geval-of-shape-spec-rules
  ;;          '(sspec-geval-of-g-integer?-shape-spec
  ;;            sspec-geval-of-g-integer-shape-spec
  ;;            sspec-geval-of-g-boolean-shape-spec
  ;;            sspec-geval-of-g-var-shape-spec
  ;;            sspec-geval-of-g-ite-shape-spec
  ;;            sspec-geval-of-g-concrete-shape-spec
  ;;            sspec-geval-of-g-call-shape-spec
  ;;            sspec-geval-of-cons-shape-spec
  ;;            sspec-geval-of-atom-shape-spec)))

  (local (in-theory (disable not
                             no-duplicatesp
                             sspec-geval
                             shape-spec-call-free
                             shape-specp
                             shape-spec-indices
                             shape-spec-vars
                             shape-spec-invert
                             equal-of-booleans-rewrite
                             acl2::consp-when-member-equal-of-atom-listp
                             append tag-when-atom len member)))

  (local (defthm <-0-of-logtail
           (equal (< (logtail n x) 0)
                  (< (ifix x) 0))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm logapp-of-integer-length
           (implies (equal sign (if (< (ifix x) 0) -1 0))
                    (equal (logapp (integer-length x) x sign)
                           (ifix x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm int-set-sign-of-logtail
           (implies (equal sign (< (ifix x) 0))
                    (Equal (int-set-sign sign x)
                           (ifix x)))
           :hints(("Goal" :in-theory (e/d (int-set-sign)
                                          (bitops::logapp-of-j-0))))))

  (local (defthm logapp-loghead-id
           (equal (logapp n (loghead n x) y)
                  (logapp n x y))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm logapp-logtail-id
           (equal (logapp n x (logtail n x))
                  (ifix x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  
  (local (defthm slice-to-bdd-env-of-cons
           (equal (slice-to-bdd-env (cons (cons var val) rest) env)
                  (bfr-set-var var val (slice-to-bdd-env rest env)))
           :hints(("Goal" :in-theory (enable slice-to-bdd-env)))))


  (local (defthm integer-in-range-is-signed-byte-p
           (equal (integer-in-range lst obj)
                  (if (atom lst)
                      (equal obj 0)
                    (signed-byte-p (len lst) obj)))
           :hints(("Goal" :in-theory (enable signed-byte-p integer-in-range
                                             bitops::ash-is-expt-*-x
                                             len)))))

  
  (defthm-shape-spec-invert-flag
    (defthm shape-spec-invert-correct-call-free
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert x term)))
        (implies (and (no-duplicatesp (shape-spec-indices x))
                      (no-duplicatesp (shape-spec-vars x))
                      (shape-specp x)
                      (shape-spec-call-free x)
                      (shape-spec-obj-in-range x (sspec-geval-ev term a)))
                 (equal (sspec-geval (shape-spec-to-gobj x)
                                     (cons (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env)
                                           (sspec-geval-ev-alist gvar-bindings a)))
                        (sspec-geval-ev term a))))
      :hints ('(:expand ((shape-spec-invert x term)
                         (shape-spec-call-free x)
                         (shape-spec-obj-in-range x (sspec-geval-ev term a))
                         (shape-spec-oblig-term (g-ite->then x) term))))
      ;; :hints ((and stable-under-simplificationp
      ;;              '(:expand ((shape-spec-indices x)
      ;;                         (shape-spec-vars x)
      ;;                         (shape-spec-call-free x)
      ;;                         (shape-specp x)
      ;;                         (:free (term iff-flg) (shape-spec-invert x term iff-flg))
      ;;                         (:free (obj) (shape-spec-obj-in-range x obj))
      ;;                         (:free (obj) (shape-spec-obj-in-range-iff x obj))
      ;;                         )
      ;;                :do-not-induct t))
      ;;         (and stable-under-simplificationp
      ;;              '(:expand ((shape-specp x)
      ;;                         ;; (:free (env) (sspec-geval (sspec-geval-ev term a) env))
      ;;                         (:free (a b rest env) (sspec-geval-ev-alist (cons (cons a b) rest) env))
      ;;                         (sspec-geval-ev-alist nil a)
      ;;                         (:free (a b rest env) (slice-to-bdd-env (cons (cons a b) rest) env))
      ;;                         (slice-to-bdd-env nil rest-env)
      ;;                         (:free (a b) (no-duplicatesp-equal (cons a b)))
      ;;                         )
      ;;                :in-theory (enable break-g-number))))
      :flag shape-spec-invert)
    (defthm shape-spec-invert-iff-correct-call-free
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert-iff x term)))
        (implies (and (no-duplicatesp (shape-spec-indices x))
                      (no-duplicatesp (shape-spec-vars x))
                      (shape-specp x)
                      (shape-spec-call-free x)
                      (shape-spec-obj-in-range-iff x (sspec-geval-ev term a)))
                 (iff (sspec-geval (shape-spec-to-gobj x)
                                     (cons (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env)
                                           (sspec-geval-ev-alist gvar-bindings a)))
                        (sspec-geval-ev term a))))
      :hints ('(:expand ((shape-spec-invert-iff x term)
                         (shape-spec-call-free x)
                         (:free (obj) (shape-spec-obj-in-range-iff x obj))
                         (shape-spec-oblig-term-iff (g-ite->then x) term))))
      :flag shape-spec-invert-iff)
    :skip-others t
    ;; (defthm shape-spec-list-invert-correct-call-free
    ;;   (b* (((mv ?bvar-bindings ?gvar-bindings)
    ;;         (shape-spec-list-invert x terms)))
    ;;     (implies (and (no-duplicatesp (shape-spec-list-indices x))
    ;;                   (no-duplicatesp (shape-spec-list-vars x))
    ;;                   (shape-spec-listp x)
    ;;                   (shape-spec-call-free x)
    ;;                   (shape-spec-obj-in-range x (sspec-geval-ev-lst term a)))
    ;;            (equal (sspec-geval-list (shape-spec-to-gobj-list x)
    ;;                                     (cons (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env)
    ;;                                           (sspec-geval-ev-alist gvar-bindings a)))
    ;;                   (sspec-geval-ev-lst terms a))))
    ;;   :hints ((and stable-under-simplificationp
    ;;                '(:expand ((shape-spec-list-indices x)
    ;;                           (shape-spec-list-vars x)
    ;;                           (shape-spec-listp x)
    ;;                           (shape-spec-list-call-free)
    ;;                           (shape-spec-to-gobj-list x)
    ;;                           (shape-spec-list-invert x terms)
    ;;                           (shape-spec-list-oblig-term x terms)
    ;;                           (shape-spec-list-invert nil terms)
    ;;                           (:free (a b env) (sspec-geval-list (cons a b) env))
    ;;                           (:free (env) (sspec-geval-list nil env))))))
    ;;   :flag shape-spec-list-invert)
    )


  ;; (local (defthm not-shape-spec-call-free-implies-ite-cons-or-call
  ;;          (implies (not (shape-spec-call-free x))
  ;;                   (and (consp x)
  ;;                        (or (equal (tag x) :g-ite)
  ;;                            (equal (tag x) :g-call)
  ;;                            (and (not (equal (tag x) :g-number))
  ;;                                 (not (equal (tag x) :g-boolean))
  ;;                                 (not (equal (tag x) :g-var))
  ;;                                 (not (equal (tag x) :g-concrete))))))
  ;;          :hints(("Goal" :in-theory (enable shape-spec-call-free)))
  ;;          :rule-classes :forward-chaining))

  (local (defthm shape-spec-call-free-implies-not-call
           (implies (shape-spec-call-free x)
                    (not (equal (tag x) :g-call)))
           :hints(("Goal" :in-theory (enable shape-spec-call-free)))
           :rule-classes :forward-chaining))
  



  (local (in-theory (disable shape-spec-invert
                             shape-spec-invert-iff
                             shape-spec-list-invert)))


  (defthm-shape-spec-invert-flag
    (defthm shape-spec-invert-correct
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert x term)))
        (implies (and (no-duplicatesp (shape-spec-indices x))
                      (no-duplicatesp (shape-spec-vars x))
                      (shape-specp x)
                      (sspec-geval-ev (shape-spec-oblig-term x term) a))
                 (Equal (sspec-geval (shape-spec-to-gobj x)
                                     (cons (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env)
                                           (sspec-geval-ev-alist gvar-bindings a)))
                        (sspec-geval-ev term a))))
      :hints ('(:expand ((shape-spec-oblig-term x term))
                :in-theory (disable* sspec-geval-of-shape-spec-rules))
              (and stable-under-simplificationp
                   (not (member-equal '(not (shape-spec-call-free x)) clause))
                   '(:expand ((shape-spec-invert x term))
                     :in-theory (enable sspec-geval-ev-of-fncall-args
                                        shape-spec-oblig-term-iff-eval
                                        shape-spec-oblig-term-eval))))
      :flag shape-spec-invert)
    (defthm shape-spec-invert-iff-correct
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-invert-iff x term)))
        (implies (and (no-duplicatesp (shape-spec-indices x))
                      (no-duplicatesp (shape-spec-vars x))
                      (shape-specp x)
                      (sspec-geval-ev (shape-spec-oblig-term-iff x term) a))
                 (iff (sspec-geval (shape-spec-to-gobj x)
                                   (cons (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env)
                                         (sspec-geval-ev-alist gvar-bindings a)))
                      (sspec-geval-ev term a))))
      :hints ('(:expand ((shape-spec-oblig-term-iff x term)
                         (shape-spec-obj-in-range-iff x nil)
                         (:Free (env) (sspec-geval nil env)))
                :in-theory (disable* sspec-geval-of-shape-spec-rules))
              (and stable-under-simplificationp
                   (not (member-equal '(not (shape-spec-call-free x)) clause))
                   '(:expand ((shape-spec-invert-iff x term))
                     :in-theory (enable sspec-geval-ev-of-fncall-args
                                        shape-spec-oblig-term-iff-eval
                                        shape-spec-oblig-term-eval))))
      :flag shape-spec-invert-iff)
    (defthm shape-spec-list-invert-correct
      (b* (((mv ?bvar-bindings ?gvar-bindings)
            (shape-spec-list-invert x terms)))
        (implies (and (no-duplicatesp (shape-spec-list-indices x))
                      (no-duplicatesp (shape-spec-list-vars x))
                      (shape-spec-listp x)
                      (sspec-geval-ev (shape-spec-list-oblig-term x terms) a))
                 (equal (sspec-geval-list (shape-spec-to-gobj-list x)
                                          (cons (slice-to-bdd-env (sspec-geval-ev-alist bvar-bindings a) rest-env)
                                                (sspec-geval-ev-alist gvar-bindings a)))
                        (sspec-geval-ev-lst terms a))))
      :hints ('(:expand ((:free (Env) (sspec-geval-list nil env))
                         (shape-spec-list-oblig-term nil terms)
                         (shape-spec-list-invert x terms)
                         (shape-spec-list-oblig-term x terms))))
      :flag shape-spec-list-invert))

  ;; (defthm-shape-spec-invert-flag
  ;;   (defthm lookup-in-bvars-shape-spec-env-term
  ;;     (implies (and (member k (shape-spec-indices x))
  ;;                   (shape-specp x))
  ;;              (equal (cdr (hons-assoc-equal k (car (sspec-geval-ev (shape-spec-env-term x term) a))))
  ;;                     (sspec-geval-ev (cdr (hons-assoc-equal k (mv-nth 0 (shape-spec-invert x term)))) a)))
  ;;     :hints ('(:expand ((shape-spec-env-term x term)
  ;;                        (shape-spec-invert x term)
  ;;                        (shape-spec-indices x))))
  ;;     :flag shape-spec-invert)
  ;;   (defthm lookup-in-bvars-shape-spec-env-term-iff
  ;;     (implies (and (member k (shape-spec-indices x))
  ;;                   (shape-specp x))
  ;;              (equal (cdr (hons-assoc-equal k (car (sspec-geval-ev (shape-spec-env-term-iff x term) a))))
  ;;                     (sspec-geval-ev (cdr (hons-assoc-equal k (mv-nth 0 (shape-spec-invert-iff x term)))) a)))
  ;;     :hints ('(:expand ((shape-spec-env-term-iff x term)
  ;;                        (shape-spec-invert-iff x term)
  ;;                        (shape-spec-indices x))))
  ;;     :flag shape-spec-invert-iff)
  ;;   (defthm lookup-in-bvars-shape-spec-list-env-term
  ;;     (implies (and (member k (shape-spec-list-indices x))
  ;;                   (shape-spec-listp x))
  ;;              (equal (cdr (hons-assoc-equal k (car (sspec-geval-ev (shape-spec-list-env-term x terms) a))))
  ;;                     (sspec-geval-ev (cdr (hons-assoc-equal k (mv-nth 0 (shape-spec-list-invert x terms)))) a)))
  ;;     :hints ('(:expand ((shape-spec-list-env-term x terms)
  ;;                        (shape-spec-list-invert x terms)
  ;;                        (shape-spec-list-indices x))))
  ;;     :flag shape-spec-list-invert))
  (local (defthm open-simple-term-vars
           (equal (simple-term-vars (cons fn args))
                  (and (not (eq fn 'quote))
                       (simple-term-vars-lst args)))
           :hints(("Goal" :in-theory (enable simple-term-vars)))))

  (local (defthm simple-term-vars-lst-of-consp
           (implies (consp x)
                    (equal (simple-term-vars-lst x)
                           (union-eq (simple-term-vars-lst (cdr x))
                                     (simple-term-vars (car x)))))
           :hints(("Goal" :in-theory (enable simple-term-vars-lst)))))

  (local (defthm simple-term-vars-lst-of-append
           (acl2::set-equiv (simple-term-vars-lst (append a b))
                            (append (simple-term-vars-lst a) (simple-term-vars-lst b)))
           :hints(("Goal" :in-theory (enable simple-term-vars-lst append)))))

  (local (defthm simple-term-vars-lst-of-make-nth-terms
           (implies (not (member v (simple-term-vars x)))
                    (not (member v (simple-term-vars-lst (make-nth-terms x start n)))))
           :hints(("Goal" :in-theory (enable make-nth-terms)))))

  (local (defthm member-vars-of-car-term
           (implies (not (member v (simple-term-vars x)))
                    (not (member v (simple-term-vars (car-term x)))))
           :hints(("Goal" :in-theory (enable car-term)))))
  (local (defthm member-vars-of-cdr-term
           (implies (not (member v (simple-term-vars x)))
                    (not (member v (simple-term-vars (cdr-term x)))))
           :hints(("Goal" :in-theory (enable cdr-term)))))

  (defthm vars-of-integer-bits-shape-spec-invert
    (implies (not (member v (simple-term-vars term)))
             (not (member v (simple-term-vars-lst (alist-vals (integer-bits-shape-spec-invert idx bits term))))))
    :hints(("Goal" :in-theory (enable integer-bits-shape-spec-invert alist-vals))))

  (local (defthm ss-unary-function-fix-not-equal-quote
           (not (equal (ss-unary-function-fix f) 'quote))))

  (local (defthm alist-vals-of-append
           (equal (alist-vals (append a b))
                  (append (alist-vals a) (alist-vals b)))
           :hints(("Goal" :in-theory (enable alist-vals append)))))

  (local (in-theory (enable alist-vals)))

  (defthm-shape-spec-invert-flag
    (defthm vars-of-shape-spec-invert-bvars
      (implies (not (member v (simple-term-vars term)))
               (not (member v (simple-term-vars-lst (alist-vals (mv-nth 0 (shape-spec-invert x term)))))))
      :hints ('(:expand ((shape-spec-invert x term))))
      :flag shape-spec-invert)
    (defthm vars-of-shape-spec-invert-iff-bvars
      (implies (not (member v (simple-term-vars term)))
               (not (member v (simple-term-vars-lst (alist-vals (mv-nth 0 (shape-spec-invert-iff x term)))))))
      :hints ('(:expand ((shape-spec-invert-iff x term))
                :in-theory (enable car-term cdr-term)))
      :flag shape-spec-invert-iff)
    (defthm vars-of-shape-spec-list-invert-bvars
      (implies (not (member v (simple-term-vars-lst terms)))
               (not (member v (simple-term-vars-lst (alist-vals (mv-nth 0 (shape-spec-list-invert x terms)))))))
      :hints ('(:expand ((shape-spec-list-invert x terms))))
      :flag shape-spec-list-invert))


  (defthm-shape-spec-invert-flag
    (defthm vars-of-shape-spec-invert-gvars
      (implies (not (member v (simple-term-vars term)))
               (not (member v (simple-term-vars-lst (alist-vals (mv-nth 1 (shape-spec-invert x term)))))))
      :hints ('(:expand ((shape-spec-invert x term))))
      :flag shape-spec-invert)
    (defthm vars-of-shape-spec-invert-iff-gvars
      (implies (not (member v (simple-term-vars term)))
               (not (member v (simple-term-vars-lst (alist-vals (mv-nth 1 (shape-spec-invert-iff x term)))))))
      :hints ('(:expand ((shape-spec-invert-iff x term))
                :in-theory (enable car-term cdr-term)))
      :flag shape-spec-invert-iff)
    (defthm vars-of-shape-spec-list-invert-gvars
      (implies (not (member v (simple-term-vars-lst terms)))
               (not (member v (simple-term-vars-lst (alist-vals (mv-nth 1 (shape-spec-list-invert x terms)))))))
      :hints ('(:expand ((shape-spec-list-invert x terms))))
      :flag shape-spec-list-invert))

)
