; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "auto-termination")

; First, a basic test.

(defund my-dec (x) (1- x))

(defun my-max (x y)
  (declare (xargs :measure (+ (nfix x) (nfix y))
                  :hints (("Goal" :in-theory (enable my-dec)))))
  (cond ((zp x) y)
        ((zp y) x)
        (t (1+ (my-max (my-dec x) (my-dec y))))))

(with-auto-termination
; Notice that we are mangling the COND clauses, in particular using posp where
; we didn't previously.  We are also swapping the order of arguments.
 (defun my-sum (b a)
   (cond ((and (posp a) (posp b))
          (+ 2 (my-sum (my-dec b) (my-dec a))))
         ((zp b) a)
         (t b))))

; Next, let's search the database for not-quite-trivial termination arguments;
; e.g., (include-book "arithmetic-5/top" :dir :system) is not sufficient for
; the first one.

(local (include-book "projects/paco/paco" :dir :system))

(with-auto-termination ; finds PACO::ENNI
 (defun f1 (x y)
   (cond ((zp x) y)
         (t (f1 (floor x 10)
                (cons x y))))))

(local (verify-termination copy-ens1))

(with-auto-termination ; finds COPY-ENS1
 (defun g1 (i max array-name array ans)
   (declare (xargs :measure anything-here-is-ignored))
   (cond ((not (and (integerp i)
                    (<= 0 i)
                    (integerp max)
                    (<= 0 max)))
          nil)
         ((> i max) (revappend ans nil))
         ((aref1 array-name array i)
          (g1 (+ 1 i) max array-name array ans))
         (t (g1 (+ 1 i) max array-name array (cons i ans))))))

; Now let's mangle things somewhat, rearranging COND clauses, and introducing
; NATP and then changing the order of the two NATP calls above.

(with-auto-termination
 (defun g2 (i max array-name array ans)
   (declare (xargs :measure anything-here-is-ignored))
   (and (natp max)
        (natp i)
        (cond ((> i max) (revappend ans nil))
              ((not (aref1 array-name array i))
               (g2 (+ 1 i) max array-name array (cons i ans)))
              (t (g2 (+ 1 i) max array-name array ans))))))

; Ackermann presents a bit of a challenge, since the termination theorem for
; ack mentions ack, so won't literally subsume the termination theorem for a
; copy of ack.  (Technical note: Our auto-termination algorithm avoids this
; problem by replacing recursive calls in the induction-machine by calls of
; :FN.)

(include-book "std/basic/two-nats-measure" :dir :system)

(defun ack (x y)
  (declare (xargs :measure (nat-list-measure (list y x))))
  (if (zp x)
      1
    (if (zp y)
	(if (equal x 1) 2 (+ x 2))
      (ack (ack (1- x) y) (1- y)))))

; A :theory hint is required for "auto termination"; the usual small theory is
; insufficient.  Both :current and a more restrictive theory work.  The more
; restrictive one, which is immediately below, is interesting because it
; requires the generated :use hint.  The second one illustrates the use of
; :current to specify the current theory, but in that case we don't actually
; need the previous termination theorem for ack (we just reprove the
; corresponding theorem in the same way as was done for ack).

(with-auto-termination
 (defun ack2 (xx yy)
   (if (zp xx)
       1
     (if (zp yy)
	 (if (equal xx 1) 2 (+ xx 2))
       (ack2 (ack2 (1- xx) yy) (1- yy)))))
 :theory
 '(zp-compound-recognizer len nfix car-cons cdr-cons o<-of-nat-list-measure))

(with-auto-termination
 (defun ack3 (xx yy)
   (if (zp xx)
       1
     (if (zp yy)
	 (if (equal xx 1) 2 (+ xx 2))
       (ack3 (ack3 (1- xx) yy) (1- yy)))))
 :theory :current)

; TODO: Switching the arguments doesn't work because we have a reflexive
; function.  We can admit the following function directly with the measure
; (nat-list-measure (list y x)) and then prove (equal (ack x y) (ack-alt y
; x))), but our subsumption algorithm isn't clever enough to consider permuted
; arguments for reflexive functions.
#+skip
(with-auto-termination
 (defun ack-alt (y x)
   (if (zp x)
       1
     (if (zp y)
         (if (equal x 1) 2 (+ x 2))
       (ack-alt (1- y) (ack-alt y (1- x))))))
 :theory :current)

; Just for fun, let's mangle the form a bit.  We need to enable posp, though;
; that's automatic for the default :theory, which however we're not using here.
(with-auto-termination
 (defun ack4 (xx yy)
   (if (posp xx)
       (if (posp yy)
           (ack4 (ack4 (1- xx) yy) (1- yy))
         (if (not (eql xx 1)) (+ xx 2) 2))
     1))
 :theory '(zp-compound-recognizer posp len nfix car-cons cdr-cons
                                  o<-of-nat-list-measure))
