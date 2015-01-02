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

(local (include-book "arithmetic"))
(include-book "ihs/ihs-lemmas" :dir :system)
(include-book "ash")

(in-theory (disable logtail))

(defthm logtail-when-i-is-zero
  (equal (logtail pos 0)
         0)
  :hints (("Goal" :in-theory (enable logtail))))

(in-theory (disable logtail-size-0))

(defthm logtail-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logtail pos i)
                  0))
  :hints
  (("Goal" :in-theory (enable logtail))))

(defthm logtail-when-pos-is-not-positive
  (implies (<= pos 0)
           (equal (logtail pos i)
                  (ifix i)
                  ))
  :hints (("Goal" :in-theory (enable logtail))))

(defthmd logtail-when-pos-is-not-positive-no-split
  (implies (and (<= pos 0)
                (integerp i))
           (equal (logtail pos i)
                  i))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-when-pos-is-not-an-integerp
  (implies (not (integerp pos))
           (equal (logtail pos i)
                  (ifix i)
                  ))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-1
  (equal (logtail 1 x)
         (logcdr x))
  :hints (("goal" :in-theory (enable logtail logcons))))


(defthm logtail--1
  (equal (logtail n -1)
         -1)
  :hints (("Goal" :in-theory (enable logtail))))

(encapsulate
 ()
 (local (defthmd logtail-ash-1-helper
          (implies (and (<= n1 n2)
                        (integerp n1)
                        (integerp n2)
                        (<= 0 n1)
                        )
                   (equal (logtail n1 (ash x n2))
                          (ash x (- n2 n1))))
          :hints (("Goal" :nonlinearp t
                   :in-theory (enable logtail ash)))))

 (defthm logtail-ash-1
   (implies (<= n1 n2)
            (equal (logtail n1 (ash x n2))
                   (if (integerp n2)
                       (ash x (- n2 (nfix n1)))
                     (logtail n1 x))))
   :hints (("Goal" :use (:instance logtail-ash-1-helper (n2 (ifix n2)))))))

(encapsulate
 ()
 (local (defthmd logtail-ash-2-helper
          (implies (and (<= n2 n1)
                        (integerp n1)
                        (integerp n2)
                        (<= 0 n1)
                        )
                   (equal (logtail n1 (ash x n2))
                          (logtail (- n1 n2) x)))
          :hints (("Goal" :in-theory (enable logtail ash)))))

;bzo combine this with logtail-ash-1?
 (defthm logtail-ash-2
   (implies (<= n2 n1)
            (equal (logtail n1 (ash x n2))
                   (if (and (integerp n1)
                            (<= 0 n1))
                       (if (integerp n2)
                           (logtail (- n1 n2) x)
                         (logtail n1 x)
                         )
                     (ifix (ash x n2)))))
   :hints (("Goal" :use (:instance  logtail-ash-2-helper)))))

(defthm ash-as-logtail
  (implies (<= n 0)
           (equal (ash x n)
                  (logtail (- n) x)))
  :hints (("goal" :in-theory (enable logtail ash))))

(defthm logtail-of-logcdr
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logtail n (logcdr i))
                  (logtail (+ 1 n) i)))
  :hints (("Goal" :in-theory (e/d (logtail logcdr ifloor ) (floor-of-shift-right-2)))))

(defthm logcdr-of-logtail
  (implies (and (<= 0 n)
                (integerp n))
           (equal (logcdr (logtail n i))
                  (logtail (+ 1 n) i)))
  :hints (("Goal" :in-theory (e/d (logtail logcdr ifloor ) (floor-of-shift-right-2)))))




(defthmd logtail*-better
  (equal (logtail pos i)
         (cond ((< (ifix pos) 0)  (ifix i))
               ((equal (ifix pos) 0) (ifix i))
               (t (logtail (1- pos) (logcdr i)))))
  :rule-classes
; Matt K.: Changed logtail to logtail$inline 11/10/2012 to accommodate change
; by Jared Davis to define logtail using defun-inline in
; ihs/basic-definitions.lisp.
  ((:definition :clique (logtail$inline)
                :controller-alist ((logtail$inline t t))))
  :hints (("Goal" :use (:instance logtail*))))

(in-theory (disable logtail*))

;the ifix was causing case splits
(defthm logtail-0-i-better
  (equal (logtail 0 i)
         (ifix i)))

(defthmd logtail-0-i-better-no-split
  (implies (integerp i)
           (equal (logtail 0 i)
                  i)))

(in-theory (disable logtail-0-i))

;dup
(defun sub1-sub1-induction (m n)
  (if (zp m)
      n
    (sub1-sub1-induction (1- m) (1- n))))

;; (thm
;;  (implies (and (integerp n)
;;                (< 0 n))
;;           (equal (LOGTAIL N (* 1/2 X))
;;                  (logtail (+ -1 n) x)))
;;  :hints (("Goal" :in-theory (enable logtail))))

(encapsulate
 ()

 (local
  (defthm logtail-*-expt-helper1
    (implies (and (integerp n)
                  (integerp n2)
                  (integerp x)
                  (<= n2 n)
                  (<= 0 n2))
             (equal (logtail n (* x (expt 2 n2)))
                    (logtail (- n n2) x)))
    :rule-classes nil
    :hints (("goal" :in-theory (enable logtail*-better EXPONENTS-ADD-UNRESTRICTED)
             :do-not '(generalize eliminate-destructors)
             :induct (sub1-sub1-induction n2 n)))))

 (local
  (defthm logtail-*-expt-helper2
    (implies (and (integerp n)
                  (integerp n2)
                  (integerp x)
                  (< n n2)
                  (<= 0 n))
             (equal (logtail n (* x (expt 2 n2)))
                    (* x (expt 2 (- n2 n)))))
    :rule-classes nil
    :hints (("goal" :in-theory (enable logtail*-better EXPONENTS-ADD-UNRESTRICTED)
             :do-not '(generalize eliminate-destructors)
             :induct (sub1-sub1-induction n n2)))))

 (defthm logtail-*-expt
   (implies (and (integerp n)
                 (integerp n2)
                 (integerp x)
                 (<= 0 n)
                 (<= 0 n2))
            (equal (logtail n (* x (expt 2 n2)))
                   (if (< n n2)
                       (* x (expt 2 (- n2 n)))
                     (logtail (- n n2) x))))
   :hints (("goal"
            :use (logtail-*-expt-helper1
                  logtail-*-expt-helper2)))))

(defthm logtail-*-expt-v2
  (implies (and (integerp n)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n)
                (<= 0 n2))
           (equal (logtail n (* x y (expt 2 n2)))
                  (if (< n n2)
                      (* x y (expt 2 (- n2 n)))
                    (logtail (- n n2) (* x y)))))
  :hints (("goal" :use (:instance logtail-*-expt (x (* x y))))))



(defthm logtail-logtail-better
  (implies (and (>= pos1 0)
                (integerp pos1)
                (integerp pos)
                (>= pos 0)
                )
           (equal (logtail pos1 (logtail pos i))
                  (logtail (+ pos pos1)
                           i)))
  :hints (("Goal" :use (:instance logtail-logtail)
           :in-theory (disable logtail-logtail))))

(in-theory (disable LOGTAIL-LOGTAIL))