; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; We can get by with just "base" instead of "top" as of this writing.  But
; let's include the entire set-theory library here, so that it will be included
; when other books include the present book, which is the base book for this
; directory's development.
(include-book "projects/set-theory/top" :dir :system)

(include-book "projects/set-theory/utilities/defthme" :dir :system)

(defun-sk rational-setp (s)
  (forall x
    (implies (in x s)
             (rationalp x)))
  :rewrite :direct)

(defun-sk dr-closed-downward (s)
  (forall (x y)
    (implies (and (< x y)
                  (rationalp x)
                  (in y s))
             (in x s)))
  :rewrite :direct)

(defun-sk dr-boundp (b s)
  (forall y
    (implies (in y s)
             (<= y b)))
  :rewrite :direct)

(defun-sk dr-bounded-above (s)
  (exists b
    (and (rationalp b)
         (dr-boundp b s)))
  :skolem-name dr-bound)

(defun-sk dr-max-p (s)
  (exists b
    (and (dr-boundp b s)
         (in b s)))
  :skolem-name dr-max)

(defun drp (s)
  (and (not (equal s 0))
       (rational-setp s)
       (dr-closed-downward s)
       (dr-bounded-above s)
       (not (dr-max-p s))))

(zsub rationals ()
      x
      (v-omega)
      (rationalp x))

(defthmz rationsls-as-rationalp
  (equal (in x (rationals))
         (rationalp x))
  :props (zfc rationals$prop v$prop domain$prop prod2$prop inverse$prop))

; We prefer to rewrite (in x (rationals)) with rationsls-includes-rationalp
; rather than rationals$comprehension.
(in-theory (disable rationals$comprehension))

(zsub r2dr (r1)   ; name, args
      r2          ; x
      (rationals) ; s
      (< r2 r1))

(extend-zfc-table dr-prop0
                  zfc rationals$prop v$prop domain$prop prod2$prop inverse$prop
                  r2dr$prop)

; Disable defun-sk functions:
(in-theory (disable rational-setp dr-closed-downward dr-boundp dr-bounded-above
                    dr-max-p))

(defthmz drp-r2dr-1
  (implies (rationalp x)
           (dr-bounded-above (r2dr x)))
  :hints (("Goal"
           :in-theory (e/d (dr-boundp) (dr-bounded-above-suff))
           :use ((:instance dr-bounded-above-suff (b x)
                            (s (r2dr x))))))
  :props (dr-prop0))

(defthmz drp-r2dr-2
  (implies (rationalp x)
           (not (dr-max-p (r2dr x))))
  :hints (("Goal"
           :in-theory (e/d (dr-max-p) (dr-boundp-necc))
           :use ((:instance dr-boundp-necc
                            (b (dr-max (r2dr x)))
                            (s (r2dr x))
                            (y (/ (+ (dr-max (r2dr x))
                                     x)
                                  2))))))
  :props (dr-prop0))

(defthmz drp-r2dr-3-1
  (implies (rationalp x)
           (in (- x 1)
               (r2dr x)))
  :props (dr-prop0)
  :rule-classes nil)

(defthmz drp-r2dr-3
  (implies (rationalp x)
           (not (equal (r2dr x)
                       0)))
  :hints (("Goal" :use drp-r2dr-3-1))
  :props (dr-prop0))

(defthmz drp-r2dr
  (implies (rationalp x)
           (drp (r2dr x)))
  :hints (("Goal" :in-theory (enable rational-setp dr-closed-downward)))
  :props (dr-prop0))

(in-theory (disable drp))
