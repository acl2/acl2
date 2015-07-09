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
(include-book "ihs/basic-definitions" :dir :system)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (local
  (include-book "arithmetic-3/bind-free/top" :dir :system))

 (local
  (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
                                                HIST PSPV))))

 (local
  (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

;;; RBK: These three are in arithmetic-4.

 (local
  (defthm crock-1
    (implies (and (syntaxp (quotep c))
                  (integerp c)
                  (integerp x))
             (equal (equal (- x) c)
                    (equal x (- c))))))

 (local
  (encapsulate
   ()

   (local
    (defun ind-fn (n)
      (if (zp n)
          42
        (ind-fn (+ -1 n)))))

   (local
    (scatter-exponents))

   (defthm crock-2
     (implies (and (integerp n)
                   (< 0 n))
              (not (integerp (/ (expt 2 n)))))
     :hints (("Goal" :induct (ind-fn n))))
   ))

 (local
  (encapsulate
   ()

   (local
    (defthm super-crock
      (implies (and (integerp a)
                    (integerp b))
               (integerp (* a b)))))

   (defthm crock-3
     (implies (and (integerp (* x (/ (expt 2 n))))
                   (integerp n)
                   (< 0 n)
                   (integerp x))
              (integerp (* 1/2 x)))
     :hints (("Goal" :use (:instance super-crock
                                     (a (* x (/ (expt 2 n))))
                                     (b (expt 2 (+ -1 n)))))))
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Here are the logop definitions from the IHS library we will be
;;; using.

;; [Jared]: removing these definitions by including ihs/basic-definitions
;; instead These ones are incompatible because the ihs definition are now
;; $inline.

 ;; (defun ifloor (i j)
 ;;  (declare (xargs :guard (and (integerp i)
 ;;                              (integerp j)
 ;;                              (not (= 0 j)))))
 ;;   (floor (ifix i) (ifix j)))

 ;; (defun imod (i j)
 ;;  (declare (xargs :guard (and (integerp i)
 ;;                              (integerp j)
 ;;                              (not (= 0 j)))))
 ;;   (mod (ifix i) (ifix j)))

 ;; (defun expt2 (n)
 ;;  (declare (xargs :guard (and (integerp n)
 ;;                              (<= 0 n))))
 ;;   (expt 2 (nfix n)))

 ;; (defun loghead (size i)
 ;;  (declare (xargs :guard (and (integerp size)
 ;;                              (>= size 0)
 ;;                              (integerp i))))
 ;;   (imod i (expt2 size)))

 ;; (defun logtail (pos i)
 ;;  (declare (xargs :guard (and (integerp pos)
 ;;                              (>= pos 0)
 ;;                              (integerp i))))
 ;;   (ifloor i (expt2 pos)))

 ;; (defun logapp (size i j)
 ;;  (declare (xargs :guard (and (integerp size)
 ;;                              (>= size 0)
 ;;                              (integerp i)
 ;;                              (integerp j))))
 ;;   (let ((j (ifix j)))
 ;;     (+ (loghead size i) (* j (expt2 size)))))

 (defun carry (n x y)
   (logtail n (+ (loghead n x) (loghead n y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some simple rules about logand and logior we will be using.  The
;;; first six rules seem like good rules to have around at all times,
;;; and are probably in the IHS and super-ihs libraries.  The last
;;; rule might be problematic in general, but was needed here.  Case
;;; splits can cause problems if used to freely.

 (local
  (defthm logand-commutes
    (implies (and (integerp x)
                  (integerp y))
             (equal (logand y x)
                    (logand x y)))))

 (local
  (defthm logior-commutes
    (implies (and (integerp x)
                  (integerp y))
             (equal (logior y x)
                    (logior x y)))))

;;; Some ``base case'' rules for logior

 (local
  (defthm logior-0-x
    (IMPLIES (AND (INTEGERP X))
             (EQUAL (LOGIOR 0 x)
                    x))))

 (local
  (defthm logior--1-x
    (implies (integerp x)
             (equal (LOGIOR -1 X)
                    -1))))

 (local
  (defthm logand-reduction
    (implies (and (integerp x)
                  (integerp y))
             (equal (logand x y)
                    (+ (* 2 (logand (floor x 2) (floor y 2)))
                       (logand (mod x 2) (mod y 2)))))))

 (local
  (in-theory (disable logand-reduction)))

 (local
  (defthm logior-reduction
    (implies (and (integerp x)
                  (integerp y))
             (equal (logior x y)
                    (+ (* 2 (logior (floor x 2) (floor y 2)))
                       (logior (mod x 2) (mod y 2)))))
    :hints (("Goal" :use (:instance logand-reduction
                                    (x (lognot x))
                                    (y (lognot y)))))))

 (local
  (in-theory (disable logior-reduction)))

 (local
  (encapsulate
   ()

   (local
    (defthm mod-by-2
      (implies (integerp x)
               (equal (mod x 2)
                      (if (evenp x)
                          0
                        1)))))

   (defthm logior-mod-2-mod-2
     (implies (and (integerp x)
                   (integerp y))
              (equal (logior (mod x 2) (mod y 2))
                     (if (and (evenp x)
                              (evenp y))
                         0
                       1))))
   ))

 (local
  (in-theory (disable logior)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; In logior-logapp-crock-gen-gen, we need some way to specify that
;;; the ``relevant'' bits of x and y do not overlap.  We will use
;;; int-length for this.  Without this, I had problems forming a
;;; good induction.  I believe that this would not be a problem if
;;; we could induct in a ``constructor'' way where, for instance:
;;;
;;; base-case:
;;; (or (equal x 0)
;;;     (equal x -1))
;;;
;;; inductive step:
;;; assume for x, prove for
;;; 1. (* 2 x)
;;; 2. if (<= x 0), (+ -1 (* 2 x))
;;; 3. if (<= 0 x), (+ 1 (* 2 x))
;;;
;;; or something similar where we are building up the bit-vector
;;; representing the integer x.
;;;
;;; But ACL2 likes to induct in a ``destructor'' manner as suggested
;;; by function definitions.
;;;
;;; base-case:
;;; (or (equal x 0)
;;;     (equal x -1))
;;;
;;; inductive step:
;;; assume for (floor x), prove for x.
;;;
;;; For many theorems, ACL2 does fine; but for arithmetic, I often
;;; find myself frustrated by ACL2's induction schemes.

 (local
  (defun int-length (x)
    (if (or (not (integerp x))
            (<= x 0))
        0
      (+ 1 (int-length (floor x 2))))))

 (local
  (defthm int-length-floor
    (implies (and (integerp x)
                  (< 0 x))
             (equal (int-length (floor x 2))
                    (+ -1 (int-length x))))))

 (local
  (defthm int-length-size
    (implies (and (integerp x)
                  (integerp n)
                  (<= 0 x)
                  (<= 0 n)
                  (< x (expt 2 n)))
             (<= (int-length x) n))
    :hints (("Goal" :do-not '(generalize)))))

;;; Our induction scheme

 (local
  (defun ind-fn (x y)
    (declare (xargs :measure (nfix (+ (abs x) (abs y)))))
    (if (or (not (integerp x))
            (not (integerp y))
            (equal x 0)
            (equal y 0)
            (equal x -1)
            (equal y -1))
        42
      (ind-fn (floor x 2) (floor y 2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Begining of proof proper.

 (local
  (defthm logior-logapp-crock-gen-gen
    (implies (and (integerp x)
                  (integerp y)
                  (<= 0 y)
                  (equal (mod x (expt 2 (int-length y))) 0))
             (equal (logior x y)
                    (+ x y)))
    :hints (("Goal" :induct (ind-fn x y))
            ("Subgoal *1/2" :use (:instance logior-reduction)))))

(defthm logior-logapp-crock-gen
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (< 0 n))
           (equal (logior (ash y n)
                          (loghead n x))
                  (logapp n x y)))
  :hints (("Goal" :use ((:instance int-length-size
                                   (x (MOD X (EXPT 2 N)))))
           :in-theory (disable int-length-size))))

 (defthm logior-logapp-crock
   (implies (and (integerp x)
                 (integerp y))
            (equal (logior (ash y 16)
                           (loghead 16 x))
                   (logapp 16 x y)))
   :hints (("Goal" :in-theory (disable ash loghead))))

 )
