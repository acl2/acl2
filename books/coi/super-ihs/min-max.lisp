; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "ACL2")

;;thms about min and max
;bzo disable min and max later?

(defthm integerp-max
  (implies
   (and
    (integerp a)
    (integerp b))
   (integerp (max a b))))

(defthm integerp-min
  (implies
   (and
    (integerp a)
    (integerp b))
   (integerp (min a b))))


; Opening max and min causes too much casesplitting.  We add some
; rules that simplify max and min expressions, in case we later disable min and max.

(defthm equal-max-x-x
  (equal (max x x)
         x))

(defthm max-linear
  (and
   (<= a (max a b))
   (<= b (max a b)))
  :rule-classes :linear)

(defthm equal-a-max-a
  (implies
   (and
    (rationalp a)
    (rationalp b))
   (and
    (equal
     (equal (max a b) a)
     (<= b a))
   (equal
    (equal (max a b) b)
    (<= a b)))))

(defthm max-constants
  (implies
   (and
    (syntaxp (quotep x))
    (syntaxp (quotep y)))
   (equal
    (max x (max y z))
    (max (max x y) z))))

(defthm max-simplify
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (<= a b)
     (and
      (equal (<= a (max b c)) t)
      (equal (<= a (max c b)) t)))
    (implies
     (< a b)
     (and
      (equal (<= b (max a c)) (<= b c))
      (equal (<= b (max c a)) (<= b c))))
    (implies
     (< a b)
     (and
      (equal (< a (max b c)) t)
      (equal (< a (max c b)) t)))
    (implies
     (<= a b)
     (and
      (equal (< b (max a c)) (< b c))
      (equal (< b (max c a)) (< b c)))
     ))))


(defthm max-simplify2
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (< a b)
     (and
      (equal (<= (max b c) a) nil)
      (equal (<= (max c b) a) nil)))
    (implies
     (<= a b)
     (and
      (equal (<= (max a c) b) (<= c b))
      (equal (<= (max c a) b) (<= c b))))
    (implies
     (<= a b)
     (and
      (equal (< (max b c) a) nil)
      (equal (< (max c b) a) nil)))
    (implies
     (< a b)
     (and
      (equal (< (max a c) b) (< c b))
      (equal (< (max c a) b) (< c b)))))))

(defthm +-over-max
  (implies
   (syntaxp (quotep a))
  (equal
   (+ a (max b c))
   (max (+ a b) (+ a c)))))


(defthm commutativity-of-max
  (implies
   (and
    (acl2-numberp a)
    (acl2-numberp b))
   (equal (max a b) (max b a))))

(defthm equal-min-x-x
  (equal (min x x) x))

(defthm min-linear
  (and
   (<= (min a b) a)
   (<= (min a b) b))
  :rule-classes :linear)

(defthm equal-a-min-a
  (implies
   (and
    (rationalp a)
    (rationalp b))
   (and
    (equal
     (equal (min a b) a)
     (<= a b))
    (equal
     (equal (min a b) b)
     (<= b a)))))

(defthm min-simplify
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (<= a b)
     (and
      (equal (<= a (min b c)) (<= a c))
      (equal (<= a (min c b)) (<= a c))))
    (implies
     (< a b)
     (and
      (equal (<= b (min a c)) nil)
      (equal (<= b (min c a)) nil)))
    (implies
     (< a b)
     (and
      (equal (< a (min b c)) (< a c))
      (equal (< a (min c b)) (< a c))))
    (implies
     (<= a b)
     (and
      (equal (< b (min a c)) nil)
      (equal (< b (min c a)) nil))))))

(defthm min-simplify2
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (< a b)
     (and
      (equal (<= (min b c) a) (<= c a))
      (equal (<= (min c b) a) (<= c a))))
    (implies
     (<= a b)
     (and
      (equal (<= (min a c) b) t)
      (equal (<= (min c a) b) t)))
    (implies
     (<= a b)
     (and
      (equal (< (min b c) a) (< c a))
      (equal (< (min c b) a) (< c a))))
    (implies
     (< a b)
     (and
      (equal (< (min a c) b) t)
      (equal (< (min c a) b) t))))))

(defthm min-constants
  (implies
   (and
    (syntaxp (quotep x))
    (syntaxp (quotep y)))
   (equal
    (min x (min y z))
    (min (min x y) z))))

(defthm +-over-min
  (equal
   (+ a (min b c))
   (min (+ a b) (+ a c))))

(defthm commutativity-of-min
  (implies
   (and
    (acl2-numberp a)
    (acl2-numberp b))
   (equal (min a b) (min b a))))