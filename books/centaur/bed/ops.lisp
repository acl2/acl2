; Centaur BED Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "BED")
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (enable arith-equiv-forwarding)))

(local (defthm loghead-1
         (equal (loghead 1 x)
                (logcar x))
         :hints(("Goal" :in-theory (enable acl2::loghead**)))))

(defmacro car$ (x)
  `(mbe :logic (car ,x)
        :exec  (if (consp ,x) (car ,x) nil)))

(defmacro cdr$ (x)
  `(mbe :logic (cdr ,x)
        :exec  (if (consp ,x) (cdr ,x) nil)))

(define bed-op-p (x)
  :parents (bed)
  :short "Recognizer for BED operators."
  :long "<p>We use a simple truth-table based encoding, i.e., each operator is
a binary, Boolean connective; it is represented as a four-bit natural, where
the bits of the representation are the truth table for the operator.</p>"
  (unsigned-byte-p 4 x)
  ///
  (defthm unsigned-byte-p-when-bed-op-p
    (implies (bed-op-p x)
             (unsigned-byte-p 4 x)))
  (defthm type-when-bed-op-p
    (implies (bed-op-p x)
             (natp x))
    :rule-classes :compound-recognizer))

(define bed-op-fix (x)
  :returns (op bed-op-p)
  :parents (bed-op-p)
  :short "Fixing function for @(see bed-op-p)s."
  :prepwork ((local (in-theory (enable bed-op-p))))
  :inline t
  (the (unsigned-byte 4)
    (logand #b1111
            (the integer (ifix x))))
  ///
  (defthm bed-op-fix-when-bed-op-p
    (implies (bed-op-p x)
             (equal (bed-op-fix x)
                    x))))

(defsection bed-op-fix$
  :parents (bed-op-p)
  :short "Faster version of @(see bed-op-fix) for when you know it's a valid
  operator."
  :long "@(def bed-op-fix$)"

  (defmacro bed-op-fix$ (x)
    `(mbe :logic (bed-op-fix ,x)
          :exec ,x)))

(define bed-op-equiv (x y)
  (equal (bed-op-fix x)
         (bed-op-fix y))
  ///
  (defequiv bed-op-equiv)
  (defthm bed-op-equiv-of-bed-op-fix
    (bed-op-equiv (bed-op-fix op)
                  op)))


(local (xdoc::set-default-parents bed-op-p))


(define bed-op-eval ((op bed-op-p :type (unsigned-byte 4))
                     (x  bitp     :type bit)
                     (y  bitp     :type bit))
  :short "Application of a BED operator to two bits."
  :long "<p>This is just a truth-table lookup into the operator.</p>"
  :returns (value bitp)
  :split-types t
  :inline t
  :prepwork
  ((local (in-theory (enable bitp bool->bit bed-op-p))))
  (b* (((the (unsigned-byte 2) xshift)   (ash (the bit (lbfix x)) 1))
       ((the (unsigned-byte 2) index)    (logior xshift (the bit (lbfix y))))
       ((the (signed-byte 3) nindex)     (- index))
       ((the (unsigned-byte 4) op-shifted)
        (ash (the (unsigned-byte 4)
               (mbe :logic (bed-op-fix op)
                    :exec op))
             nindex)))
    (the bit (logand 1 op-shifted)))
  ///
  (defcong bit-equiv equal (bed-op-eval op x y) 2)
  (defcong bit-equiv equal (bed-op-eval op x y) 3)
  (defthm bed-op-eval-of-bed-op-fix
    (equal (bed-op-eval (bed-op-fix op) x y)
           (bed-op-eval op x y)))
  (defcong bed-op-equiv equal (bed-op-eval op x y) 1
    :hints(("Goal" :in-theory (enable bed-op-equiv))))
  (defthm bed-op-eval-when-fix-is-exact
    (implies (and (equal (bed-op-fix op) x)
                  (syntaxp (or (quotep x)
                               ;; 0-ary functions, like (bed-op-true)
                               (and (consp x)
                                    (not (cdr x))))))
             (equal (bed-op-eval op left right)
                    (bed-op-eval x left right)))))

(local (in-theory (enable bed-op-p bed-op-eval bfix bool->bit)))

(define bed-op-true ()
  :inline t
  :returns (op bed-op-p)
  15
  ///
  (defthm bed-op-eval-of-true
    (equal (bed-op-eval (bed-op-true) x y)
           1))
  (in-theory (disable (:e bed-op-true)
                      (:t bed-op-true))))

(define bed-op-ior ()
  :inline t
  :returns (op bed-op-p)
  14
  ///
  (defthm bed-op-eval-of-ior
    (equal (bed-op-eval (bed-op-ior) x y)
           (b-ior x y)))
  (in-theory (disable (:e bed-op-ior)
                      (:t bed-op-ior))))

(define bed-op-orc2 ()
  :inline t
  :returns (op bed-op-p)
  13
  ///
  (defthm bed-op-eval-of-orc2
    (equal (bed-op-eval (bed-op-orc2) x y)
           (b-orc2 x y)))
  (in-theory (disable (:e bed-op-orc2)
                      (:t bed-op-orc2))))

(define bed-op-arg1 ()
  :inline t
  :returns (op bed-op-p)
  12
  ///
  (defthm bed-op-eval-of-arg1
    (equal (bed-op-eval (bed-op-arg1) x y)
           (bfix x)))
  (in-theory (disable (:e bed-op-arg1)
                      (:t bed-op-arg1))))

(define bed-op-orc1 ()
  :inline t
  :returns (op bed-op-p)
  11
  ///
  (defthm bed-op-eval-of-orc1
    (equal (bed-op-eval (bed-op-orc1) x y)
           (b-orc1 x y)))
  (in-theory (disable (:e bed-op-orc1)
                      (:t bed-op-orc1))))

(define bed-op-arg2 ()
  :inline t
  :returns (op bed-op-p)
  10
  ///
  (defthm bed-op-eval-of-arg2
    (equal (bed-op-eval (bed-op-arg2) x y)
           (bfix y)))
  (in-theory (disable (:e bed-op-arg2)
                      (:t bed-op-arg2))))

(define bed-op-eqv ()
  :inline t
  :returns (op bed-op-p)
  9
  ///
  (defthm bed-op-eval-of-eqv
    (equal (bed-op-eval (bed-op-eqv) x y)
           (b-eqv x y)))
  (in-theory (disable (:e bed-op-eqv)
                      (:t bed-op-eqv))))

(define bed-op-and ()
  :inline t
  :returns (op bed-op-p)
  8
  ///
  (defthm bed-op-eval-of-and
    (equal (bed-op-eval (bed-op-and) x y)
           (b-and x y)))
  (in-theory (disable (:e bed-op-and)
                      (:t bed-op-and))))

(define bed-op-nand ()
  :inline t
  :returns (op bed-op-p)
  7
  ///
  (defthm bed-op-eval-of-nand
    (equal (bed-op-eval (bed-op-nand) x y)
           (b-nand x y)))
  (in-theory (disable (:e bed-op-nand)
                      (:t bed-op-nand))))

(define bed-op-xor ()
  :inline t
  :returns (op bed-op-p)
  6
  ///
  (defthm bed-op-eval-of-xor
    (equal (bed-op-eval (bed-op-xor) x y)
           (b-xor x y)))
  (in-theory (disable (:e bed-op-xor)
                      (:t bed-op-xor))))

(define bed-op-not2 ()
  :inline t
  :returns (op bed-op-p)
  5
  ///
  (defthm bed-op-eval-of-not2
    (equal (bed-op-eval (bed-op-not2) x y)
           (b-not y)))
  (in-theory (disable (:e bed-op-not2)
                      (:t bed-op-not2))))

(define bed-op-andc2 ()
  :inline t
  :returns (op bed-op-p)
  4
  ///
  (defthm bed-op-eval-of-andc2
    (equal (bed-op-eval (bed-op-andc2) x y)
           (b-andc2 x y)))
  (in-theory (disable (:e bed-op-andc2)
                      (:t bed-op-andc2))))

(define bed-op-not1 ()
  :inline t
  :returns (op bed-op-p)
  3
  ///
  (defthm bed-op-eval-of-not1
    (equal (bed-op-eval (bed-op-not1) x y)
           (b-not x)))
  (in-theory (disable (:e bed-op-not1)
                      (:t bed-op-not1))))

(define bed-op-andc1 ()
  :inline t
  :returns (op bed-op-p)
  2
  ///
  (defthm bed-op-eval-of-andc1
    (equal (bed-op-eval (bed-op-andc1) x y)
           (b-andc1 x y)))
  (in-theory (disable (:e bed-op-andc1)
                      (:t bed-op-andc1))))

(define bed-op-nor ()
  :inline t
  :returns (op bed-op-p)
  1
  ///
  (defthm bed-op-eval-of-nor
    (equal (bed-op-eval (bed-op-nor) x y)
           (b-nor x y)))
  (in-theory (disable (:e bed-op-nor)
                      (:t bed-op-nor))))

(define bed-op-false ()
  :inline t
  :returns (op bed-op-p)
  0
  ///
  (defthm bed-op-eval-of-false
    (equal (bed-op-eval (bed-op-false) x y)
           0))
  (in-theory (disable (:e bed-op-false)
                      (:t bed-op-false))))
