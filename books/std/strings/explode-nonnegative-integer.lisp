; Lemmas about explode-nonnegative-integer
; Copyright (C) 2005-2006 Kookamara LLC
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
;
; explode-nonnegative-integer.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "decimal")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/append" :dir :system))

; Explode-nonnegative-integer is a particularly nasty function to try to reason
; about because it is tail recursive and has a very nasty base case.  Instead
; of reasoning about it directly, we will split it up into the following,
; simpler definition.

(local (in-theory (disable floor mod)))

(local (defun simpler-explode-nonnegative-integer (n base ans)
         (declare (xargs :guard (and (integerp n)
                                     (<= 0 n)
                                     (print-base-p base))))
         (if (or (zp n)
                 (not (print-base-p base)))
             ans
           (simpler-explode-nonnegative-integer
            (floor n base)
            base
            (cons (digit-to-char (mod n base)) ans)))))


; We can now redefine explode-nonnegative-integer to be a simple nonrecursive
; function that uses our simpler-explode-nonnegative-integer as its core, but
; wraps it in a simple "or" statement.  We will then disable the previous
; definition of explode-nonnegative-integer, so that only our new definition
; will be used.

(local (defthm explode-nonnegative-integer-redefinition
         (equal (explode-nonnegative-integer n base ans)
                (or (simpler-explode-nonnegative-integer n base ans)
                    '(#\0)))
         :rule-classes ((:definition :install-body nil))))

(local (in-theory (disable (:definition explode-nonnegative-integer))))



; Sadly, even simpler-explode-nonnegative-integer is hard to reason about as it
; is tail recursive.  So, we will introduce a non tail-recursive function in
; its place that does almost the same thing.  We'll call this the "basic
; explode-nonnegative-integer core", or the basic-eni-core for short.

(local (defun basic-eni-core (n base)
         (declare (xargs :guard (and (natp n)
                                     (print-base-p base))))
         (if (or (zp n)
                 (not (print-base-p base)))
             nil
           (cons (digit-to-char (mod n base))
                 (basic-eni-core (floor n base) base)))))

(local (defun basic-eni-induction (n m base)
         (declare (xargs :guard (and (natp n)
                                     (natp m)
                                     (print-base-p base))))
         (cond ((zp n)
                nil)
               ((zp m)
                nil)
               ((not (print-base-p base))
                nil)
               (t
                (basic-eni-induction (floor n base) (floor m base) base)))))

(local (defthm basic-eni-core-under-iff
         (iff (basic-eni-core n base)
              (and (not (zp n))
                   (print-base-p base)))))

(local (defthm consp-of-basic-eni-core
         (equal (consp (basic-eni-core n base))
                (and (not (zp n))
                     (if (print-base-p base)
                         t
                       nil)))
         :hints(("Goal" :expand (basic-eni-core n base)))))

(local (defthm equal-of-basic-eni-cores
         (implies (force (print-base-p base))
                  (equal (equal (basic-eni-core n base)
                                (basic-eni-core m base))
                         (equal (nfix n)
                                (nfix m))))
         :hints(("Goal"
                 :in-theory (disable basic-eni-core)
                 :induct (basic-eni-induction n m base)
                 :expand ((:free (base) (basic-eni-core n base))
                          (:free (base) (basic-eni-core m base)))
                 :do-not '(generalize fertilize)))))

(local (defthm equal-of-basic-eni-core-with-list-zero
         (not (equal (basic-eni-core n base) '(#\0)))
         :hints(("Goal" :in-theory (enable digit-to-char)))))

(local (defthm basic/simpler-equivalence
         (equal (simpler-explode-nonnegative-integer n base acc)
                (revappend (basic-eni-core n base) acc))))

(local (defthm equal-of-simpler-explode-nonnegative-integers
         (implies (force (print-base-p base))
                  (equal (equal (simpler-explode-nonnegative-integer n base acc)
                                (simpler-explode-nonnegative-integer m base acc))
                         (equal (nfix n) (nfix m))))))

(local (defthm simpler-eni-when-nonzero
         (implies (and (not (zp n))
                       (print-base-p base))
                  (simpler-explode-nonnegative-integer n base acc))))

(local (defthm simpler-eni-degenerate-lemma
         (equal (equal (simpler-explode-nonnegative-integer n base acc) '(#\0))
                (and (equal acc '(#\0))
                     (or (zp n)
                         (not (print-base-p base)))))
         :hints(("Goal"
                 :induct (simpler-explode-nonnegative-integer n base acc)
                 :expand ((:free (base) (basic-eni-core n base)))
                 :in-theory (e/d (digit-to-char)
                                 (basic-eni-core))))))

(local (defthm not-of-simpler-explode-nonnegative-integer
         (equal (not (simpler-explode-nonnegative-integer n base acc))
                (and (equal acc nil)
                     (or (zp n)
                         (not (print-base-p base)))))))

(local (defthm true-listp-of-simpler-explode-nonnegative-integer
         (equal (true-listp (simpler-explode-nonnegative-integer n base acc))
                (true-listp acc))))

(local (defthm equal-of-explode-nonnegative-integers-lemma
         (implies (and (natp n)
                       (natp m)
                       (not (equal n m))
                       (not (simpler-explode-nonnegative-integer n base acc))
                       (force (print-base-p base)))
                  (simpler-explode-nonnegative-integer m base acc))))

(defthm equal-of-explode-nonnegative-integers
  (implies (and (natp n)
                (natp m)
                (force (print-base-p base)))
           (equal (equal (explode-nonnegative-integer n base acc)
                         (explode-nonnegative-integer m base acc))
                  (equal n m)))
  :hints(("Goal" :in-theory (disable simpler-explode-nonnegative-integer
                                     basic/simpler-equivalence))))

(defthm true-listp-of-explode-nonnegative-integer
  (equal (true-listp (explode-nonnegative-integer n base acc))
         (true-listp acc)))

(defthm true-listp-of-explode-nonnegative-integer-type
  (implies (true-listp acc)
           (true-listp (explode-nonnegative-integer n base acc)))
  :rule-classes :type-prescription)

(defthm character-listp-of-explode-nonnegative-integer
  (equal (character-listp (explode-nonnegative-integer n base acc))
         (character-listp acc)))

(local (defthm dec-digit-char-listp-of-basic-eni-core
         (str::dec-digit-char-listp (basic-eni-core n 10))))

(local (defthm dec-digit-char-listp-of-simpler-eni
         (implies (str::dec-digit-char-listp acc)
                  (str::dec-digit-char-listp (simpler-explode-nonnegative-integer n 10 acc)))))

(defthm dec-digit-char-listp-of-explode-nonnegative-integer
  (implies (str::dec-digit-char-listp acc)
           (str::dec-digit-char-listp (explode-nonnegative-integer n 10 acc))))


(encapsulate
 ()
 (local (in-theory (disable revappend-removal)))

 (local (defthm lemma
          (equal (equal (revappend x acc) '(#\0))
                 (or (and (equal acc nil)
                          (consp x)
                          (equal (car x) #\0)
                          (atom (cdr x)))
                     (and (equal acc '(#\0))
                          (atom x))))))

 (local (defthm lemma2
          (implies (and (not (zp n))
                        (print-base-p base))
                   (consp (basic-eni-core n base)))))

 (defthm nonzeroness-of-explode-nonnegative-integer-when-nonzero
   (implies (and (not (zp n))
                 (force (print-base-p base)))
            (not (equal (explode-nonnegative-integer n base nil)
                        '(#\0))))
   :hints(("Goal"
           :in-theory (e/d (digit-to-char)
                           (basic-eni-core))
           :expand ((:free (base) (basic-eni-core n base)))))))



(defthm dec-digit-char-value-of-digit-to-char
  (implies (and (force (natp n))
                (force (<= 0 n))
                (force (<= n 9)))
           (equal (str::dec-digit-char-value (digit-to-char n))
                  n))
  :hints(("Goal" :in-theory (enable str::dec-digit-char-value
                                    digit-to-char))))


(defsection digit-to-char-of-dec-digit-char-value

 (local (defun test (n)
          (declare (xargs :ruler-extenders :all))
          (and (let ((char (code-char n)))
                 (or (not (str::dec-digit-char-p char))
                     (equal (digit-to-char (str::dec-digit-char-value char))
                            char)))
               (if (zp n)
                   t
                 (test (- n 1))))))

 (local (defthm l0
          (implies (and (test n)
                        (natp i)
                        (natp n)
                        (<= i n))
                   (let ((char (code-char i)))
                     (implies (str::dec-digit-char-p char)
                              (equal (digit-to-char (str::dec-digit-char-value char))
                                     char))))))

 (local (defthm l1
          (implies (and (natp i)
                        (<= i 255))
                   (let ((char (code-char i)))
                     (implies (str::dec-digit-char-p char)
                              (equal (digit-to-char (str::dec-digit-char-value char))
                                     char))))
          :hints(("Goal" :use ((:instance l0 (n 255)))))))

 (defthm digit-to-char-of-dec-digit-char-value
   (implies (str::dec-digit-char-p char)
            (equal (digit-to-char (str::dec-digit-char-value char))
                   char))
   :hints(("Goal" :use ((:instance l1 (i (char-code char))))))))


(defund basic-unexplode-core (x)
  (declare (xargs :guard (and (character-listp x)
                              (str::dec-digit-char-listp x))))
  (if (consp x)
      (+ (str::dec-digit-char-value (car x))
         (* 10 (basic-unexplode-core (cdr x))))
    0))

(local (defthm basic-unexplode-core-of-basic-eni-core
         (implies (force (natp n))
                  (equal (basic-unexplode-core (basic-eni-core n 10))
                         n))
         :hints(("Goal" :in-theory (enable basic-eni-core
                                           basic-unexplode-core)))))

(defund unexplode-nonnegative-integer (x)
  (declare (xargs :guard (and (character-listp x)
                              (str::dec-digit-char-listp x))))
  (basic-unexplode-core (revappend x nil)))

(encapsulate
 ()
 (local (include-book "std/lists/rev" :dir :system))

 (defthm unexplode-nonnegative-integer-of-explode-nonnegative-integer
   (implies (force (natp n))
            (equal (unexplode-nonnegative-integer (explode-nonnegative-integer n 10 nil))
                   n))
   :hints(("Goal" :in-theory (e/d (unexplode-nonnegative-integer)
                                  (basic-eni-core))))))
