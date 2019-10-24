; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "arith-base")
(include-book "syntax-bind")

(define check-integerp (ans x)
  (and (integerp x) ans t)
  ///
  (defthm check-integerp-implies-integerp
    (implies (check-integerp ans x)
             (integerp x))
    :rule-classes :forward-chaining)

  (defmacro check-integerp! (&rest args)
    `(binder (check-integerp . ,args))))

(define check-natp (ans x)
  (and (natp x) ans t)
  ///
  (defthm check-natp-implies-natp
    (implies (check-natp ans x)
             (natp x))
    :rule-classes :forward-chaining)

  (defmacro check-natp! (&rest args)
    `(binder (check-natp . ,args))))

(define check-int-endp (ans (x integerp))
  (and (int-endp x) ans t)
  ///
  (defthm check-int-endp-fn-implies-int-endp
    (implies (acl2::rewriting-negative-literal `(check-int-endp ,ans ,x))
             (iff (check-int-endp ans x)
                  (and (int-endp x)
                       (hide (check-int-endp ans x)))))
    :hints(("Goal" :expand ((:free (x) (hide x))))))

  (defmacro check-int-endp! (&rest args)
    `(binder (check-int-endp . ,args))))

(define check-bitp (ans x)
  (and (bitp x) ans t)
  ///
  (defthm check-bitp-implies-bitp
    (implies (check-bitp ans x)
             (bitp x))
    :rule-classes :forward-chaining)

  (defmacro check-bitp! (&rest args)
    `(binder (check-bitp . ,args))))

(define check-signed-byte-p (ans n x)
  (and (signed-byte-p n x) ans t)
  ///
  (defthm check-signed-byte-p-implies-signed-byte-p
    (implies (acl2::rewriting-negative-literal `(check-signed-byte-p ,ans ,n ,x))
             (iff (check-signed-byte-p ans n x)
                  (and (signed-byte-p n x)
                       (hide (check-signed-byte-p ans n x)))))
    :hints(("Goal" :expand ((:free (x) (hide x))))))

  (defmacro check-signed-byte-p! (&rest args)
    `(binder (check-signed-byte-p . ,args))))

(define check-unsigned-byte-p (ans n x)
  (and (unsigned-byte-p n x) ans t)
  ///
  (defthm check-unsigned-byte-p-implies-unsigned-byte-p
    (implies (acl2::rewriting-negative-literal `(check-unsigned-byte-p ,ans ,n ,x))
             (iff (check-unsigned-byte-p ans n x)
                  (and (unsigned-byte-p n x)
                       (hide (check-unsigned-byte-p ans n x)))))
    :hints(("Goal" :expand ((:free (x) (hide x))))))

  (defmacro check-unsigned-byte-p! (&rest args)
    `(binder (check-unsigned-byte-p . ,args))))


(define check-non-integerp (ans x)
  (and (not (integerp x))
       ans
       t)
  ///
  (defthm check-non-integerp-implies-not-integerp
    (implies (check-non-integerp ans x)
             (not (integerp x)))
    :rule-classes :forward-chaining)

  (defmacro check-non-integerp! (&rest args)
    `(binder (check-non-integerp . ,args))))

(define check-consp (ans x)
  (and (consp x)
       ans
       t)
  ///
  (defthm check-consp-implies-consp
    (implies (check-consp ans x)
             (consp x))
    :rule-classes :forward-chaining)

  (defmacro check-consp! (&rest args)
    `(binder (check-consp . ,args))))

(define check-non-consp (ans x)
  (and (not (consp x))
       ans
       t)
  ///
  (defthm check-non-consp-implies-not-consp
    (implies (check-non-consp ans x)
             (not (consp x)))
    :rule-classes :forward-chaining)

  (defmacro check-non-consp! (&rest args)
    `(binder (check-non-consp . ,args))))

(define check-booleanp (ans x)
  (and (booleanp x)
       ans
       t)
  ///
  (defthm check-booleanp-implies-booleanp
    (implies (check-booleanp ans x)
             (booleanp x))
    :rule-classes :forward-chaining)

  (defmacro check-booleanp! (&rest args)
    `(binder (check-booleanp . ,args))))

(define check-non-booleanp (ans x)
  (and (not (booleanp x))
       ans
       t)
  ///
  (defthm check-non-booleanp-implies-not-booleanp
    (implies (check-non-booleanp ans x)
             (not (booleanp x)))
    :rule-classes :forward-chaining)

  (defmacro check-non-booleanp! (&rest args)
    `(binder (check-non-booleanp . ,args))))



(define integer-length-bound ((ans acl2::maybe-natp) (x integerp))
  :returns (bound acl2::maybe-natp :rule-classes :type-prescription)
  (and (natp ans)
       (<= (integer-length x) ans)
       ans)
  ///
  (defthm integer-length-bound-implies-integer-length
    (implies (integer-length-bound ans x)
             (<= (integer-length x) (integer-length-bound ans x)))
    :hints (("goal" :expand ((:free (x) (hide x)))))
    :rule-classes :linear)

  (defmacro integer-length-bound! (&rest args)
    `(binder (integer-length-bound . ,args))))



(define check-equal (ans x y)
  (and (equal x y)
       ans
       t)
  ///
  (defthm check-equal-implies-equal
    (implies (check-equal ans x y)
             (equal x y))
    :rule-classes :forward-chaining)

  (defmacro check-equal! (&rest args)
    `(binder (check-equal . ,args))))
