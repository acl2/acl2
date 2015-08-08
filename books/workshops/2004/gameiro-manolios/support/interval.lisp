; Copyright (C) 2004  Georgia Institute of Technology

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by: Marcio Gameiro and Panagiotis Manolios who can be
; reached as follows:

; Email: gameiro@math.gatech.edu

; Postal Mail:
; School of  Mathematics
; Georgia Institute of  Technology
; 686 Cherry Street
; Atlanta, Georgia 30332-0160 U.S.A.

; Email: manolios@cc.gatech.edu

; Postal Mail:
; College of Computing
; Georgia Institute of Technology
; 801 Atlantic Drive
; Atlanta, Georgia 30332-0280 U.S.A.

(in-package "ACL2")

(include-book "top-with-meta")

(include-book "nth-thms")

(in-theory (enable nth))

(defthm mv-nth-nth
  (equal (mv-nth x y)
         (nth x y)))

(in-theory (disable nth mv-nth))

(defun intervalp (x1 x2)
  (and (real/rationalp x1)
       (real/rationalp x2)
       (<= x1 x2)))

(defthm intervalp-real/rationalp
  (implies (intervalp x1 x2)
           (and (real/rationalp x1)
                (real/rationalp x2)))
  :rule-classes :forward-chaining)

(defthm intervalp-<=
  (implies (intervalp x1 x2)
           (<= x1 x2))
  :rule-classes :forward-chaining)

(defthm prove-interval
  (implies (and (real/rationalp x1)
                (real/rationalp x2)
                (<= x1 x2))
           (intervalp x1 x2)))

(in-theory (disable intervalp))

(defun in (x x1 x2)
  (and (real/rationalp x)
       (intervalp x1 x2)
       (<= x1 x)
       (<= x x2)))

(defthm in-real/rationalp
  (implies (in x x1 x2)
           (and (real/rationalp x)
                (real/rationalp x1)
                (real/rationalp x2)))
  :rule-classes :forward-chaining)

(defthm in-<=
  (implies (in x x1 x2)
           (and (<= x1 x)
                (<= x x2)))
  :rule-classes :forward-chaining)

(defthm not-in-<
  (implies (not (in x x1 x2))
           (or (not (intervalp x1 x2))
               (not (real/rationalp x))
               (< x x1)
               (< x2 x)))
  :rule-classes :forward-chaining)

(defthm prove-in
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp z)
                (<= y x)
                (<= x z))
           (in x y z)))

(defthm prove-not-in
  (implies (or (not (real/rationalp x))
               (not (real/rationalp y))
               (not (real/rationalp z))
               (< x y)
               (< z x))
           (not (in x y z))))

(in-theory (disable in))

(encapsulate
 (((i+ * * * *) => (mv * *)))

 (local (defun i+ (x1 x2 y1 y2)
          (mv (+ x1 y1)
              (+ x2 y2))))

 (defthm i+_ok
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (mv-let (z1 z2)
                    (i+ x1 x2 y1 y2)
                    (in (+ x y) z1 z2)))))

(defthm real/rationalp-i+
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (and (real/rationalp (nth 0 (i+ x1 x2 y1 y2)))
                (real/rationalp (nth 1 (i+ x1 x2 y1 y2)))))
  :hints (("goal" :use ((:instance i+_ok (x x1) (y y1))))))

(defthm intervalp-i+
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (intervalp (nth 0 (i+ x1 x2 y1 y2))
                      (nth 1 (i+ x1 x2 y1 y2))))
  :hints (("goal"
           :use ((:instance i+_ok (x x1) (y y1))))))

(defthm i+-expand-fc-1a
   (implies (and (in y x1 x2)
                 (in x y1 y2))
            (<= (nth 0 (i+ x1 x2 y1 y2)) (+ x y)))
   :hints (("goal"
            :use (:instance i+_ok (y x) (x y))))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 0 (i+ x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i+-expand-fc-1
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (<= (nth 0 (i+ x1 x2 y1 y2)) (+ x y)))
   :hints (("goal"
            :use (:instance i+_ok)))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 0 (i+ x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i+-expand-fc-2a
   (implies (and (in y x1 x2)
                 (in x y1 y2))
            (<= (+ x y) (nth 1 (i+ x1 x2 y1 y2))))
   :hints (("goal"
            :use (:instance i+_ok (x y) (y x))))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 1 (i+ x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i+-expand-fc-2
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (<= (+ x y) (nth 1 (i+ x1 x2 y1 y2))))
   :hints (("goal"
            :use (:instance i+_ok)))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 1 (i+ x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i+-ok-
  (let ((add (i+ x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2)
                  (equal xy (+ x y)))
             (in xy (nth 0 add) (nth 1 add))))
  :rule-classes ((:rewrite :match-free :all)))

(defthm i+-ok
  (let ((add (i+ x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2))
             (in (+ x y) (nth 0 add) (nth 1 add)))))

(encapsulate
 (((i- * * * *) => (mv * *)))

 (local (defun i- (x1 x2 y1 y2)
          (mv (- x1 y2)
              (- x2 y1))))

 (defthm i-_ok
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (mv-let (z1 z2)
                    (i- x1 x2 y1 y2)
                    (in (- x y) z1 z2)))))


(defthm real/rationalp-i-
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (and (real/rationalp (nth 0 (i- x1 x2 y1 y2)))
                (real/rationalp (nth 1 (i- x1 x2 y1 y2)))))
  :hints (("goal" :use ((:instance i-_ok (x x1) (y y1))))))

(defthm intervalp-i-
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (intervalp (nth 0 (i- x1 x2 y1 y2))
                      (nth 1 (i- x1 x2 y1 y2))))
  :hints (("goal"
           :use ((:instance i-_ok (x x1) (y y1))))))

(defthm i--expand-fc-1
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (<= (nth 0 (i- x1 x2 y1 y2)) (- x y)))
   :hints (("goal"
            :use (:instance i-_ok)))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 0 (i- x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i--expand-fc-2
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (<= (- x y) (nth 1 (i- x1 x2 y1 y2))))
   :hints (("goal"
            :use (:instance i-_ok)))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 1 (i- x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i--ok-
  (let ((sub (i- x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2)
                  (equal xy (- x y)))
             (in xy (nth 0 sub) (nth 1 sub))))
  :rule-classes ((:rewrite :match-free :all)))

(defthm i--ok2
  (let ((sub (i- x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2))
             (in (+ (- y) x) (nth 0 sub) (nth 1 sub))))
  :rule-classes ((:rewrite :match-free :all)))

(defthm i--ok
  (let ((sub (i- x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2))
             (in (- x y) (nth 0 sub) (nth 1 sub)))))

(encapsulate
 (((i* * * * *) => (mv * *)))

 (local (defun max4 (x1 x2 x3 x4)
          (max (max x1 x2)
               (max x3 x4))))

 (local (defun i* (x1 x2 y1 y2)
          (let ((m0 (max4 (abs x1) (abs x2) (abs y1) (abs y2))))
            (mv (- (* m0 m0)) (* m0 m0)))))

 (local (defthm l1
          (implies (and (real/rationalp x)
                        (real/rationalp y))
                   (<= (* x y)
                       (* (abs x) (abs y))))))

 (local (defthm l2
          (implies (and (real/rationalp x1)
                        (real/rationalp x2)
                        (real/rationalp x)
                        (<= x1 x)
                        (<= x x2)
                        (<= (abs x1) m)
                        (<= (abs x2) m))
                   (<= (abs x) m))))

 (local (defthm ratp-abs
          (implies (real/rationalp x)
                   (real/rationalp (abs x)))
          :rule-classes :type-prescription))

 (local (defthm ratp-max4
          (implies (and (real/rationalp x1)
                        (real/rationalp x2)
                        (real/rationalp x3)
                        (real/rationalp x4))
                   (real/rationalp (max4 x1 x2 x3 x4)))
          :rule-classes :type-prescription))

 (local (defthm l4
          (equal (* (abs x) (abs x)) (* x x))))

 (set-ignore-ok t)

 (local (defthm abs-m
          (implies (and (real/rationalp x1)
                        (real/rationalp x2)
                        (real/rationalp y1)
                        (real/rationalp y2)
                        (equal m (max4 (abs x1) (abs x2) (abs y1) (abs y2))))
                   (and (<= (abs x1) (abs m))
                        (<= (abs x2) (abs m))
                        (<= (abs y1) (abs m))
                        (<= (abs y2) (abs m))))))

 (local (in-theory (disable max4 abs)))

 (local (defthm i*_ok-b
          (implies (and (in x x1 x2)
                        (in y y1 y2))
                   (mv-let (z1 z2)
                           (i* x1 x2 y1 y2)
                           (<= (* x y) z2)))
          :hints (("goal"
                   :use
                   ((:instance l1)
                    (:instance l2 (m (abs (max4 (abs x1)
                                                (abs x2)
                                                (abs y1)
                                                (abs y2)))))
                    (:instance l2 (x1 y1) (x2 y2) (x y)
                               (m (abs (max4 (abs x1)
                                             (abs x2)
                                             (abs y1)
                                             (abs y2)))))
                    (:instance *-preserves->=-for-nonnegatives
                               (x2 (abs x)) (y2 (abs y))
                               (x1 (abs (max4 (abs x1)
                                              (abs x2)
                                              (abs y1)
                                              (abs y2))))
                               (y1 (abs (max4 (abs x1)
                                              (abs x2)
                                              (abs y1)
                                              (abs y2))))))
                   :in-theory (disable l1 l2 *-preserves->=-for-nonnegatives)))))

 (local (defthm l1-a
          (implies (and (real/rationalp x)
                        (real/rationalp y))
                   (<= (* ( - x) y)
                       (* (abs x) (abs y))))
          :hints (("goal" :in-theory (enable abs)))))

 (local (defthm i*_ok-a
          (implies (and (in x x1 x2)
                        (in y y1 y2))
                   (mv-let (z1 z2)
                           (i* x1 x2 y1 y2)
                           (<= z1 (* x y) )))
          :hints
          (("goal"
            :use
            ((:instance l1-a)
             (:instance l2 (m (abs (max4 (abs x1)
                                         (abs x2)
                                         (abs y1)
                                         (abs y2)))))
             (:instance l2 (x1 y1) (x2 y2) (x y)
                        (m (abs (max4 (abs x1)
                                      (abs x2)
                                      (abs y1)
                                      (abs y2)))))
             (:instance *-preserves->=-for-nonnegatives
                        (x2 (abs x)) (y2 (abs y))
                        (x1 (abs (max4 (abs x1)
                                       (abs x2)
                                       (abs y1)
                                       (abs y2))))
                        (y1 (abs (max4 (abs x1)
                                       (abs x2)
                                       (abs y1)
                                       (abs y2))))))
            :in-theory (disable l1-a l2 *-preserves->=-for-nonnegatives)))))

 (defthm i*_ok
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (mv-let (z1 z2) (i* x1 x2 y1 y2)
                    (in (* x y) z1 z2)))
   :hints (("goal"
            :use ((:instance i*_ok-a)
                  (:instance i*_ok-b))))))

(defthm real/rationalp-i*
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (and (real/rationalp (nth 0 (i* x1 x2 y1 y2)))
                (real/rationalp (nth 1 (i* x1 x2 y1 y2)))))
  :hints (("goal" :use ((:instance i*_ok (x x1) (y y1))))))

(defthm intervalp-i*
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (intervalp (nth 0 (i* x1 x2 y1 y2))
                      (nth 1 (i* x1 x2 y1 y2))))
  :hints (("goal"
           :use ((:instance i*_ok (x x1) (y y1))))))

(defthm i*-expand-fc-1a
   (implies (and (in y x1 x2)
                 (in x y1 y2))
            (<= (nth 0 (i* x1 x2 y1 y2)) (* x y)))
   :hints (("goal"
            :use (:instance i*_ok (x y) (y x))))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 0 (i* x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i*-expand-fc-1
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (<= (nth 0 (i* x1 x2 y1 y2)) (* x y)))
   :hints (("goal"
            :use (:instance i*_ok)))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 0 (i* x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i*-expand-fc-2a
   (implies (and (in y x1 x2)
                 (in x y1 y2))
            (<= (* x y) (nth 1 (i* x1 x2 y1 y2))))
   :hints (("goal"
            :use (:instance i*_ok (x y) (y x))))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 1 (i* x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i*-expand-fc-2
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (<= (* x y) (nth 1 (i* x1 x2 y1 y2))))
   :hints (("goal"
            :use (:instance i*_ok)))
   :rule-classes ((:rewrite)
                  (:forward-chaining
                   :trigger-terms ((nth 1 (i* x1 x2 y1 y2)))
                   :match-free :all)))

(defthm i*-ok-
  (let ((mul (i* x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2)
                  (equal xy (* x y)))
             (in xy (nth 0 mul) (nth 1 mul))))
  :rule-classes ((:rewrite :match-free :all)))

(defthm i*-ok2
  (let ((mul (i* x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in (- v u) y1 y2))
             (in (+ (- (* x u)) (* x v)) (nth 0 mul) (nth 1 mul)))))

(defthm i*-ok-1
  (let ((mul (i* x1 x2 y1 y2)))
    (implies (and (in -1 x1 x2)
                  (in y y1 y2))
             (in (- y) (nth 0 mul) (nth 1 mul)))))

(defthm i*-ok
  (let ((mul (i* x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2))
             (in (* x y) (nth 0 mul) (nth 1 mul)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; define the vector field function vec_fld and its interval version
;; i_vec_fld and prove that the value of the vec_fld function is in
;; the interval returned be i_vec_fld
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 (((vec_fld * *) => (mv * *))
  ((i_vec_fld * * * *) => (mv * * * *)))

 (local (defun vec_fld (x y)
          (let ((u (+ x y))
                (w (- x y)))
            (mv u w))))

 (local (defun i_vec_fld (x1 x2 y1 y2)
          (mv-let (u1 u2)
                  (i+ x1 x2 y1 y2)
                  (mv-let (w1 w2)
                          (i- x1 x2 y1 y2)
                          (mv u1 u2 w1 w2)))))

 (defthm vec_fld_ok
   (implies (and (in x x1 x2)
                 (in y y1 y2))
            (mv-let (u1 u2 w1 w2) (i_vec_fld x1 x2 y1 y2)
                    (mv-let (u w) (vec_fld x y)
                            (and (in u u1 u2)
                                 (in w w1 w2)))))))

(defthm real/rationalp-vec
   (implies (and (real/rationalp x)
                 (real/rationalp y))
            (and (real/rationalp (nth 0 (vec_fld x y)))
                 (real/rationalp (nth 1 (vec_fld x y)))))
   :hints (("goal"
            :use ((:instance vec_fld_ok (x1 x) (x2 x) (y1 y) (y2 y))))))

(defthm real/rationalp-vec_fld
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (and (real/rationalp (nth 0 (i_vec_fld x1 x2 y1 y2)))
                (real/rationalp (nth 1 (i_vec_fld x1 x2 y1 y2)))
                (real/rationalp (nth 2 (i_vec_fld x1 x2 y1 y2)))
                (real/rationalp (nth 3 (i_vec_fld x1 x2 y1 y2)))))
  :hints (("goal" :use ((:instance vec_fld_ok (x x1) (y y1))))))

(defthm intervalp-vec_fld
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (and (intervalp (nth 0 (i_vec_fld x1 x2 y1 y2))
                           (nth 1 (i_vec_fld x1 x2 y1 y2)))
                (intervalp (nth 2 (i_vec_fld x1 x2 y1 y2))
                           (nth 3 (i_vec_fld x1 x2 y1 y2)))))
  :hints (("goal"
           :use ((:instance vec_fld_ok (x x1) (y y1))))))

(defthm vec_fld-ok-1
  (let ((ivec (i_vec_fld x1 x2 y1 y2))
        (vec  (vec_fld x y)))
    (implies (and (in x x1 x2)
                  (in y y1 y2))
             (in (nth 0 vec) (nth 0 ivec)
                 (nth 1 ivec))))
  :hints (("Goal" :use ((:instance vec_fld_ok)))))

(defthm vec_fld-ok-2
  (let ((ivec (i_vec_fld x1 x2 y1 y2))
        (vec  (vec_fld x y)))
    (implies (and (in x x1 x2)
                  (in y y1 y2))
             (in (nth 1 vec) (nth 2 ivec)
                 (nth 3 ivec))))
  :hints (("Goal" :use ((:instance vec_fld_ok)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; define the dot product dot and the interval version i_dot and prove
;; that the dot product is in the interval returned by i_dot
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun dot (x y u v)
  (+ (* x u) (* y v)))

(defun i_dot (x1 x2 y1 y2 u1 u2 v1 v2)
  (mv-let (p11 p12)
          (i* x1 x2 u1 u2)
          (mv-let (p21 p22)
                  (i* y1 y2 v1 v2)
                  (mv-let (d1 d2)
                          (i+ p11 p12 p21 p22)
                          (mv d1 d2)))))

(defthm i_dot_ok
  (let ((idot (i_dot x1 x2 y1 y2 u1 u2 v1 v2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2)
                  (in u u1 u2)
                  (in v v1 v2))
             (in (dot x y u v) (nth 0 idot) (nth 1 idot)))))

(defthm real/rationalp-dot
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v))
           (real/rationalp (dot x y u v))))

(defthm real/rationalp-i_dot
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2)
                (intervalp u1 u2)
                (intervalp v1 v2))
           (and (real/rationalp (nth 0 (i_dot x1 x2 y1 y2 u1 u2 v1 v2)))
                (real/rationalp (nth 1 (i_dot x1 x2 y1 y2 u1 u2 v1 v2))))))

(defthm intervalp-i_dot
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2)
                (intervalp u1 u2)
                (intervalp v1 v2))
           (intervalp (nth 0 (i_dot x1 x2 y1 y2 u1 u2 v1 v2))
                      (nth 1 (i_dot x1 x2 y1 y2 u1 u2 v1 v2)))))

(in-theory (disable i_dot))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; define the function that returns the perpendicular of a vector perp and
;; its interval version i_perp, and prove that perp is contained in i_perp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun perp (x y)
  (mv (* -1 y) x))

(defthm perp_correct
  (let ((perp (perp x y)))
    (equal (dot x y (nth 0 perp) (nth 1 perp)) 0)))

(defthm nth0-perp
  (equal (nth 0 (perp x y))
         (* -1 y)))

(defthm nth1-perp
  (equal (nth 1 (perp x y))
         x))

(in-theory (disable dot))

(defun i_perp (x1 x2 y1 y2)
  (mv-let (ny1 ny2)
          (i* -1 -1 y1 y2)
          (mv ny1 ny2 x1 x2)))

(defthm i_perp_ok
  (let ((perp (perp x y))
        (iperp (i_perp x1 x2 y1 y2)))
    (implies (and (in x x1 x2)
                  (in y y1 y2))
             (and (in (nth 0 perp) (nth 0 iperp) (nth 1 iperp))
                  (in (nth 1 perp) (nth 2 iperp) (nth 3 iperp))))))

(defthm real/rationalp-perp
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (and (real/rationalp (nth 0 (perp x y)))
                (real/rationalp (nth 1 (perp x y))))))

(defthm real/rationalp-i_perp
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (and (real/rationalp (nth 0 (i_perp x1 x2 y1 y2)))
                (real/rationalp (nth 1 (i_perp x1 x2 y1 y2)))
                (real/rationalp (nth 2 (i_perp x1 x2 y1 y2)))
                (real/rationalp (nth 3 (i_perp x1 x2 y1 y2))))))

(defthm intervalp-i_perp
  (implies (and (intervalp x1 x2)
                (intervalp y1 y2))
           (and (intervalp (nth 0 (i_perp x1 x2 y1 y2))
                           (nth 1 (i_perp x1 x2 y1 y2)))
                (intervalp (nth 2 (i_perp x1 x2 y1 y2))
                           (nth 3 (i_perp x1 x2 y1 y2))))))

(in-theory (disable perp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; define the function that returns a normal vector to a given edge
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun normal_vec (u1 u2 v1 v2)
  (mv-let (w1 w2)
          (perp (- v1 u1) (- v2 u2))
          (mv w1 w2)))

(defun i_normal_vec (u1 u2 v1 v2)
  (mv-let (x1 x2)
          (i- v1 v1 u1 u1)
          (mv-let (y1 y2)
                  (i- v2 v2 u2 u2)
                  (mv-let (w11 w12 w21 w22)
                          (i_perp x1 x2 y1 y2)
                          (mv w11 w12 w21 w22)))))

(defthm i_normal_vec_ok
  (let ((nvec (normal_vec u1 u2 v1 v2))
        (invec (i_normal_vec u1 u2 v1 v2)))
    (implies (and (real/rationalp u1)
                  (real/rationalp u2)
                  (real/rationalp v1)
                  (real/rationalp v2))
             (and (in (nth 0 nvec) (nth 0 invec) (nth 1 invec))
                  (in (nth 1 nvec) (nth 2 invec) (nth 3 invec)))))
  :hints (("Goal" :use ((:instance i_perp_ok (x (- v1 u1))
                                             (y (- v2 u2))
                                             (x1 (nth 0 (i- v1 v1 u1 u1)))
                                             (x2 (nth 1 (i- v1 v1 u1 u1)))
                                             (y1 (nth 0 (i- v2 v2 u2 u2)))
                                             (y2 (nth 1 (i- v2 v2 u2 u2))))))))

(defthm real/rationalp-normal_vec
  (implies (and (real/rationalp u1)
                (real/rationalp u2)
                (real/rationalp v1)
                (real/rationalp v2))
           (and (real/rationalp (nth 0 (normal_vec u1 u2 v1 v2)))
                (real/rationalp (nth 1 (normal_vec u1 u2 v1 v2))))))

(defthm real/rationalp-i_normal_vec
  (implies (and (real/rationalp u1)
                (real/rationalp u2)
                (real/rationalp v1)
                (real/rationalp v2))
           (and (real/rationalp (nth 0 (i_normal_vec u1 u2 v1 v2)))
                (real/rationalp (nth 1 (i_normal_vec u1 u2 v1 v2)))
                (real/rationalp (nth 2 (i_normal_vec u1 u2 v1 v2)))
                (real/rationalp (nth 3 (i_normal_vec u1 u2 v1 v2))))))

(defthm intervalp-i_normal_vec
  (implies (and (real/rationalp u1)
                (real/rationalp u2)
                (real/rationalp v1)
                (real/rationalp v2))
           (and (intervalp (nth 0 (i_normal_vec u1 u2 v1 v2))
                           (nth 1 (i_normal_vec u1 u2 v1 v2)))
                (intervalp (nth 2 (i_normal_vec u1 u2 v1 v2))
                           (nth 3 (i_normal_vec u1 u2 v1 v2))))))

(in-theory (disable normal_vec i_normal_vec))
