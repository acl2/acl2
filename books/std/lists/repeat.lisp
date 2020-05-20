; Repeat function and lemmas
; Copyright (C) 2005-2013 Kookamara LLC
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
; repeat.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "rev")
(local (include-book "take"))
(local (include-book "nthcdr"))


(defsection repeat
  :parents (std/lists make-list)
  :short "@(call repeat) creates a list of @('x')es with length @('n'); it
is a simpler alternative to @(see make-list)."

  (defund repeat (n x)
    (declare (xargs :guard (natp n)
                    :verify-guards nil))
    (mbe :logic (if (zp n)
                    nil
                  (cons x (repeat (- n 1) x)))

; On CCL, a simple loop of (loop for i from 1 to 10000 do (repeat 10000 6))
; finished in 2.74 seconds when we use make-list, versus 3.69 seconds when we
; use make-list-ac.  So lets use make-list.

         :exec (make-list n :initial-element x)))

  (local (in-theory (enable repeat)))

  (defthm repeat-when-zp
    (implies (zp n)
             (equal (repeat n a)
                    nil)))

  (defthm |(repeat 0 x)|
    (equal (repeat 0 x)
           nil))

  (defthm repeat-under-iff
    (iff (repeat n x)
         (not (zp n))))

  (defthm consp-of-repeat
    (equal (consp (repeat n a))
           (not (zp n))))

  (defthm repeat-1
    (equal (repeat 1 a)
           (list a)))

  (defthm take-when-atom
    (implies (atom x)
             (equal (take n x)
                    (repeat n nil))))

  (defthm len-of-repeat
    (equal (len (repeat n x))
           (nfix n)))

  (defthm repeat-of-nfix
    (equal (repeat (nfix n) x)
           (repeat n x)))

  (defthm car-of-repeat-increment
    ;; Goofy rule that helps when recurring when repeat is involved.
    ;; BOZO there's a better rule than this in str/arithmetic, but it case-splits.
    (implies (natp n)
             (equal (car (repeat (+ 1 n) x))
                    x)))

  (defthm cdr-of-repeat-increment
    ;; Goofy rule that helps when recurring when repeat is involved.
    (implies (natp n)
             (equal (cdr (repeat (+ 1 n) x))
                    (repeat n x))))

  (defthm member-of-repeat
    (equal (member a (repeat n b))
           (if (equal a b)
               (repeat n b)
             nil)))

  (encapsulate
    ()
    (local (defun dec-dec-induct (k n)
             (if (zp k)
                 nil
               (if (zp n)
                   nil
                 (dec-dec-induct (- k 1) (- n 1))))))

    (defthm take-of-repeat
      (equal (take n (repeat k a))
             (if (<= (nfix n) (nfix k))
                 (repeat n a)
               (append (repeat k a)
                       (repeat (- (nfix n) (nfix k)) nil))))
      :hints(("Goal" :induct (dec-dec-induct k n))))

    (defthm nthcdr-of-repeat
      (equal (nthcdr n (repeat k a))
             (if (<= (nfix n) (nfix k))
                 (repeat (- (nfix k) (nfix n)) a)
               nil))
      :hints(("Goal" :induct (dec-dec-induct k n)))))


  (defthm append-of-repeat-to-cons-of-same
    (equal (append (repeat n a) (cons a x))
           (cons a (append (repeat n a) x))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (equal (append (repeat n a) x) y)
                      (and (equal (repeat n a) (take n y))
                           (equal (nthcdr n y) x)))))

    (local (defthm l1
             (implies (not (<= (nfix n) (len y)))
                      (not (equal (append (repeat n a) x) y)))))

    (local (defthm l2
             (implies (and (<= n (len y))
                           (equal (repeat n a) (take n y))
                           (equal x (nthcdr n y)))
                      (equal (append (repeat n a) x) y))
             :hints(("Goal"
                     :in-theory (disable append-of-take-and-nthcdr)
                     :use ((:instance append-of-take-and-nthcdr
                                      (n n)
                                      (x y)))))))

    (defthm equal-of-append-repeat
      (implies (case-split (<= n (len y)))
               (equal (equal (append (repeat n a) x) y)
                      (and (equal (repeat n a) (take n y))
                           (equal x (nthcdr n y)))))
      :hints(("Goal"
              :use ((:instance l0)
                    (:instance l2))))))

  (defthm rev-of-repeat
    (equal (rev (repeat n a))
           (repeat n a)))

  (defthm subsetp-of-repeat
    (iff (subsetp-equal (repeat n x) y)
         (or (zp n) (member-equal x y)))
    :hints (("goal" :in-theory (enable subsetp-equal repeat))))

  (def-listp-rule element-list-p-of-repeat
    (iff (element-list-p (repeat n x))
         (or (element-p x)
             (zp n)))))


(local (in-theory (enable repeat)))


(defsection make-list-ac-removal
  :parents (repeat make-list)
  :short "Rewrite rule that eliminates @('make-list-ac') (and hence @(see
make-list)) in favor of @(see repeat)."

  (local (defun silly-repeat (n x acc)
           (if (zp n)
               acc
             (cons x (silly-repeat (- n 1) x acc)))))

  (local (defthm lemma1
           (equal (make-list-ac n x acc)
                  (silly-repeat n x acc))))

  (local (defthm lemma2
           (equal (silly-repeat n x acc)
                  (append (repeat n x) acc))))

  (defthm make-list-ac-removal
    (equal (make-list-ac n x acc)
           (append (repeat n x)
                   acc))))

(verify-guards repeat)


(defsection take-of-take-split
  :parents (std/lists/take)
  :short "Aggressive case splitting rule to reduce @('(take a (take b x))')."
  :long "@(def take-of-take-split)

<p>This rule may sometimes cause too much case splitting.  If you disable it,
nests of @('take') can still be reduced when ACL2 can determine the
relationship between @('a') and @('b'), using the following related rules:</p>

@(def take-of-take-same)
@(def take-more-of-take-fewer)
@(def take-fewer-of-take-more)"

  :autodoc nil

  (local (defun my-induct (a b x)
           (if (or (zp a)
                   (zp b))
               (list a b x)
             (my-induct (- a 1) (- b 1) (cdr x)))))

  (defthm take-more-of-take-fewer
    (implies (< (nfix b) (nfix a))
             (equal (take a (take b x))
                    (append (take b x) (repeat (- (nfix a) (nfix b)) nil))))
    :hints(("Goal" :induct (my-induct a b x))))

  (defthm take-of-take-split
    ;; This has a very aggressive case split.
    (equal (take a (take b x))
           (if (<= (nfix a) (nfix b))
               (take a x)
             (append (take b x) (repeat (- (nfix a) (nfix b)) nil))))))


(defsection take-of-too-many
  :parents (std/lists/take repeat)
  :short "Rewrite @('(take n x)') when @('n') is more than @('(len x)')."

  :long "<p>This rule may sometimes lead your proof in a bad direction.  If you
see unwanted @('repeat') terms, you may want to disable it.</p>"

  (defthm take-of-too-many
    (implies (<= (len x) (nfix n))
             (equal (take n x)
                    (append x (repeat (- (nfix n) (len x)) nil))))))


(defsection replicate
  :parents (repeat)
  :short "Alias for @(see repeat)."

  (defmacro replicate (n x)
    `(repeat ,n ,x))

  (add-macro-alias replicate repeat))
