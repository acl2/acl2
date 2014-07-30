; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "../primitives")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Extended base functions.
;;
;; We also introduce some extended arithmetic support.  This isn't strictly
;; necessary since we can define these functions in terms of the base
;; functions.  But, by making these base functions, we can give them far more
;; efficient Common Lisp implementations.

(definlined * (a b)
  ;; Multiply a and b.
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::* (nfix a) (nfix b)))

(definlined floor (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (let ((afix (nfix a))
        (bfix (nfix b)))
    (if (equal bfix 0)
        0
      (COMMON-LISP::floor afix bfix))))

(definlined mod (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (let ((afix (nfix a))
        (bfix (nfix b)))
    (if (equal bfix 0)
        afix
      (COMMON-LISP::mod afix bfix))))

(definlined expt (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::expt (nfix a) (nfix b)))

(definlined bitwise-shl (a n)
  ;; Shift a left by n bits.
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::ash (nfix a) (nfix n)))

(definlined bitwise-shr (a n)
  ;; Shift a right by n bits.
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::ash (nfix a) (COMMON-LISP::- (nfix n))))

(definlined bitwise-and (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::logand (nfix a) (nfix b)))

(definlined bitwise-or (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::logior (nfix a) (nfix b)))

(definlined bitwise-xor (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::logxor (nfix a) (nfix b)))

(definlined bitwise-nth (n a)
  ;; Is the nth bit of a set?
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::logbitp (nfix n) (nfix a)))

;; Common lisp also provides some other bitwise functions which we do not
;; support because they are not natural-valued.  For example:
;;
;;  (lognand 0 0) = -1
;;  (lognor 0 0) = -1
;;  (lognot 0) = -1
;;  (logorc1 0 0) = -1
;;  (logorc2 0 0) = -1
;;  (logeqv 0 0) = -1
;;
;; I didn't find an immediate example where logandc1 or logandc2 would produce
;; a negative value, but I'm not going to add them until someone wants them,
;; because I think they are weird.







(defun dec-floor2-induction (n a)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp n)
      a
    (dec-floor2-induction (- n 1) (floor a 2))))



;; Axioms for the extended base functions.
;;
;; We introduce recursive formulations of each of our extended arithmetic
;; functions.  This way, we only need one symbolic axiom per added base
;; function, and everything else is proven from the recursive definition.  It's
;; vital that we get these right, so we've used ACL2 to prove the equivalence
;; with our ACL2 definitions.

(encapsulate
 ()
 (local (in-theory (enable natp nfix zp < + - * expt floor mod
                           bitwise-shl bitwise-shr bitwise-and
                           bitwise-or bitwise-xor bitwise-nth)))

 (local (in-theory (disable ACL2::expt ACL2::floor ACL2::mod
                            ACL2::ash ACL2::logand
                            ACL2::logior ACL2::logxor ACL2::logbitp)))

 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
 (local (include-book "bitwise-support"))

 (defthmd definition-of-*
   (equal (* a b)
          (if (zp a)
              0
            (+ b (* (- a 1) b))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (* a b)
                              :scheme (dec-induction a))))

 (defthmd definition-of-floor
   (equal (floor a b)
          (cond ((zp b) 0)
                ((< a b) 0)
                (t (+ 1 (floor (- a b) b)))))
   :hints(("Goal" :in-theory (disable acl2::prefer-positive-addends-equal)))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (floor a b)
                              :scheme (sub-induction a b))))

 (defthmd definition-of-mod
   (equal (mod a b)
          (cond ((zp b) (nfix a))
                ((< a b) (nfix a))
                (t (mod (- a b) b))))
   :hints(("Goal" :in-theory (disable acl2::prefer-positive-addends-equal)))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (mod a b)
                              :scheme (sub-induction a b))))

 (defthmd definition-of-expt
   (equal (expt a b)
          (if (zp b)
              1
            (* a (expt a (- b 1)))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (expt a b)
                              :scheme (dec-induction b))))

 (defthmd definition-of-bitwise-shl
   (equal (bitwise-shl a n)
          (if (zp n)
              (nfix a)
            (* 2 (bitwise-shl a (- n 1)))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (bitwise-shl a n)
                              :scheme (dec-induction n)))
   :hints(("Goal" :in-theory (enable acl2::ash))))

 (defthmd definition-of-bitwise-shr
   (equal (bitwise-shr a n)
          (if (zp n)
              (nfix a)
            (floor (bitwise-shr a (- n 1)) 2)))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (bitwise-shr a n)
                              :scheme (dec-induction n)))
   :hints(("Goal" :in-theory (enable acl2::ash))))

 (encapsulate
  ()
  ;; We introduce the floor2-floor2 induction scheme without relying on ACL2
  ;; arithmetic, so we should be able to recreate this in Milawa.
  (local (in-theory (disable floor < natp + -)))

  (local (defthm termination-lemma
           (implies (not (zp a))
                    (equal (< (floor a 2) a)
                           t))
           :hints(("Goal"
                   :in-theory (e/d (definition-of-floor)
                                   (floor < natp + -))))))

  (defun floor2-floor2-induction (a b)
    (declare (xargs :guard t :measure (nfix a)))
    (if (or (zp a)
            (zp b))
        nil
      (floor2-floor2-induction (floor a 2) (floor b 2)))))

 (defthm definition-of-bitwise-and
   (equal (bitwise-and a b)
          (cond ((zp a) 0)
                ((zp b) 0)
                (t (+ (if (or (equal (mod a 2) 0)
                              (equal (mod b 2) 0))
                          0
                        1)
                      (* 2 (bitwise-and (floor a 2) (floor b 2)))))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (bitwise-and a b)
                              :scheme (floor2-floor2-induction a b))))

 (defthm definition-of-bitwise-or
   (equal (bitwise-or a b)
          (cond ((zp a) (nfix b))
                ((zp b) (nfix a))
                (t (+ (if (or (equal (mod a 2) 1)
                              (equal (mod b 2) 1))
                          1
                        0)
                      (* 2 (bitwise-or (floor a 2) (floor b 2)))))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (bitwise-or a b)
                              :scheme (floor2-floor2-induction a b))))

 (defthm definition-of-bitwise-xor
   (equal (bitwise-xor a b)
          (cond ((zp a) (nfix b))
                ((zp b) (nfix a))
                (t (+ (if (equal (mod a 2) (mod b 2))
                          0
                        1)
                      (* 2 (bitwise-xor (floor a 2) (floor b 2)))))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (bitwise-xor a b)
                              :scheme (floor2-floor2-induction a b))))

 (defthm definition-of-bitwise-nth
   (equal (bitwise-nth n a)
          (if (zp n)
              (equal (mod a 2) 1)
            (bitwise-nth (- n 1) (floor a 2))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (bitwise-nth n a)
                              :scheme (dec-floor2-induction n a))))

 )


;; From this point forward, all reasoning about our extended operations should
;; be done without referring to their under-the-hood implementations.

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition *))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition expt))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition floor))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition mod))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition bitwise-shl))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition bitwise-shr))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition bitwise-and))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition bitwise-or))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition bitwise-xor))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition bitwise-nth))))
