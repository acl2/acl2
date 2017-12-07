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


(in-package "DIMACS")

(include-book "litp")
(local (include-book "arithmetic/top" :dir :system))



(define litp (x)
  (and (integerp x) (not (equal x 0)))
  ///
  (defthm litp-compound-recognizer
    (equal (litp x)
           (and (integerp x) (not (equal x 0))))
    :rule-classes :compound-recognizer)

  (define lit-fix ((x litp))
    :returns (new-x litp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (if (litp x) x 1)
         :exec x)
    ///
    (defthm lit-fix-when-litp
      (implies (litp x)
               (equal (lit-fix x) x)))

    (fty::deffixtype lit :pred litp :fix lit-fix :equiv lit-equiv
      :define t :forward t)))

(define lit->var ((x litp))
  :returns (var natp :rule-classes :type-prescription)
  :inline t
  (+ -1 (abs (lit-fix x)))
  ///
  (defthm lit->var-of-negate
    (implies (litp x)
             (equal (lit->var (- x))
                    (lit->var x)))
    :hints(("Goal" :in-theory (enable litp)))))

(define lit->neg ((x litp))
  :returns (negp)
  :inline t
  (acl2::bool->bit (< (lit-fix x) 0)))

(define make-lit ((var natp) (neg bitp))
  :returns (lit litp :rule-classes :type-prescription
                :hints(("Goal" :in-theory (enable litp bfix))))
  :inline t
  (* (+ 1 (lnfix var)) (- 1 (* 2 (lbfix neg))))
  ///
  (defret lit->var-of-make-lit
    (equal (lit->var lit) (nfix var))
    :hints(("Goal" :in-theory (enable lit->var lit-fix litp bfix))))

  (defret lit->neg-of-make-lit
    (equal (lit->neg lit) (bfix neg))
    :hints(("Goal" :in-theory (enable lit->neg lit-fix acl2::bool->bit litp))))

  (defthm make-lit-of-components
    (equal (make-lit (lit->var x) (lit->neg x))
           (lit-fix x))
    :hints(("Goal" :in-theory (enable make-lit lit->var lit->neg lit-fix litp))))

  (defthm make-lit-elim
    (implies (litp x)
             (equal (make-lit (lit->var x) (lit->neg x))
                    x))
    :rule-classes :elim)

  (defthm equal-of-make-lit
    (equal (equal (make-lit var neg) x)
           (and (litp x)
                (equal (lit->var x) (nfix var))
                (equal (lit->neg x) (bfix neg))))
    :hints(("Goal" :in-theory (enable bfix lit->var lit->neg litp)))))

(define lit-maybe-negate ((lit litp) (neg bitp))
  :returns (new-lit litp :rule-classes :type-prescription
                    :hints(("Goal" :in-theory (enable litp lit-fix))))
  :inline t
  (* (lit-fix lit) (- 1 (* 2 (lbfix neg))))
  ///
  (defret lit->var-of-lit-maybe-negate
    (equal (lit->var new-lit) (lit->var lit))
    :hints(("Goal" :in-theory (enable lit->var lit-fix litp bfix))))

  (defret lit->neg-of-maybe-negate
    (equal (lit->neg new-lit) (b-xor neg (lit->neg lit)))
    :hints(("Goal" :in-theory (enable lit->neg lit-fix litp acl2::bool->bit))))

  (defret equal-of-lit-maybe-negate
    (equal (equal (lit-maybe-negate lit neg) x)
           (and (litp x)
                (equal (lit->var x) (lit->var lit))
                (equal (lit->neg x) (b-xor neg (lit->neg lit)))))
    :hints(("Goal" :in-theory (enable lit->var lit->neg litp bfix)))))

(define lit-negate ((lit litp))
  :returns (new-lit litp :rule-classes :type-prescription
                    :hints(("Goal" :in-theory (enable litp lit-fix))))
  :inline t
  (- (lit-fix lit))
  ///
  (defret lit->var-of-lit-negate
    (equal (lit->var new-lit) (lit->var lit))
    :hints(("Goal" :in-theory (enable lit->var lit-fix litp))))

  (defret lit->neg-of-negate
    (equal (lit->neg new-lit) (b-not (lit->neg lit)))
    :hints(("Goal" :in-theory (enable lit->neg lit-fix litp acl2::bool->bit))))

  (defret equal-of-lit-negate
    (equal (equal (lit-negate x) y)
           (and (litp y)
                (equal (lit->var y) (lit->var x))
                (equal (lit->neg y) (b-not (lit->neg x)))))
    :hints(("Goal" :in-theory (enable lit->var lit->neg)))))


(define satlink-to-dimacs-lit ((x satlink::litp))
  :returns (dimacs-lit litp
                       :rule-classes :type-prescription)
  :inline t
  (make-lit (satlink::lit->var x)
            (satlink::lit->neg x)))

(define dimacs-to-satlink-lit ((x litp))
  :returns (satlink-lit satlink::litp)
  :inline t
  (satlink::make-lit (lit->var x)
                     (lit->neg x)))


