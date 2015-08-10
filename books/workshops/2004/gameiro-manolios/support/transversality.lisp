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

(include-book "interval")

(defun vect_uv (u1 u2 v1 v2)
  (mv (- v1 u1) (- v2 u2)))

(defun i_vect_uv (u1 u2 v1 v2)
  (mv-let (w11 w12)
          (i- v1 v1 u1 u1)
          (mv-let (w21 w22)
                  (i- v2 v2 u2 u2)
                  (mv w11 w12 w21 w22))))

(defthm vect_uv_ok
  (let ((iuv (i_vect_uv u1 u2 v1 v2))
        (uv  (vect_uv u1 u2 v1 v2)))
    (let ((w11 (nth 0 iuv))
          (w12 (nth 1 iuv))
          (w21 (nth 2 iuv))
          (w22 (nth 3 iuv))
          (w1 (nth 0 uv))
          (w2 (nth 1 uv)))
      (implies (and (real/rationalp u1)
                    (real/rationalp u2)
                    (real/rationalp v1)
                    (real/rationalp v2))
               (and (in w1 w11 w12)
                    (in w2 w21 w22))))))

(defthm real/rationalp-vect_uv
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v))
           (and (real/rationalp (nth 0 (vect_uv x y u v)))
                (real/rationalp (nth 1 (vect_uv x y u v))))))

(defthm real/rationalp-i_vect_uv
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v))
           (and (real/rationalp (nth 0 (i_vect_uv x y u v)))
                (real/rationalp (nth 1 (i_vect_uv x y u v)))
                (real/rationalp (nth 2 (i_vect_uv x y u v)))
                (real/rationalp (nth 3 (i_vect_uv x y u v))))))

(defthm intervalp-i_vect_uv
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v))
           (and (intervalp (nth 0 (i_vect_uv x y u v))
                           (nth 1 (i_vect_uv x y u v)))
                (intervalp (nth 2 (i_vect_uv x y u v))
                           (nth 3 (i_vect_uv x y u v))))))

(in-theory (disable i_vect_uv vect_uv))

(defun vect_lbda (u1 u2 v1 v2 lbda)
  (mv-let (z1 z2)
          (vect_uv u1 u2 v1 v2)
          (mv (* lbda z1) (* lbda z2))))

(defun i_vect_lbda (u1 u2 v1 v2 l1 l2)
  (mv-let (w11 w12 w21 w22)
          (i_vect_uv u1 u2 v1 v2)
          (mv-let (z11 z12)
                  (i* l1 l2 w11 w12)
                  (mv-let (z21 z22)
                          (i* l1 l2 w21 w22)
                          (mv z11 z12 z21 z22)))))

(defun unitsubintervalp (l1 l2)
  (and (intervalp l1 l2)
       (<= 0 l1)
       (<= l2 1)))

(defthm i_vect_lbda_ok
  (let ((iuv (i_vect_lbda u1 u2 v1 v2 l1 l2))
        (uv  (vect_lbda u1 u2 v1 v2 lbda)))
    (let ((z11 (nth 0 iuv))
          (z12 (nth 1 iuv))
          (z21 (nth 2 iuv))
          (z22 (nth 3 iuv))
          (z1 (nth 0 uv))
          (z2 (nth 1 uv)))
      (implies (and (real/rationalp u1)
                    (real/rationalp u2)
                    (real/rationalp v1)
                    (real/rationalp v2)
                    (unitsubintervalp l1 l2)
                    (in lbda l1 l2))
               (and (in z1 z11 z12)
                    (in z2 z21 z22))))))

(defthm real/rationalp-vect_lbda
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v)
                (real/rationalp l))
           (and (real/rationalp (nth 0 (vect_lbda x y u v l)))
                (real/rationalp (nth 1 (vect_lbda x y u v l))))))

(defthm real/rationalp-i_vect_lbda
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v)
                (unitsubintervalp l1 l2))
           (and (real/rationalp (nth 0 (i_vect_lbda x y u v l1 l2)))
                (real/rationalp (nth 1 (i_vect_lbda x y u v l1 l2)))
                (real/rationalp (nth 2 (i_vect_lbda x y u v l1 l2)))
                (real/rationalp (nth 3 (i_vect_lbda x y u v l1 l2))))))

(defthm intervalp-i_vect_lbda
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v)
                (unitsubintervalp l1 l2))
           (and (intervalp (nth 0 (i_vect_lbda x y u v l1 l2))
                           (nth 1 (i_vect_lbda x y u v l1 l2)))
                (intervalp (nth 2 (i_vect_lbda x y u v l1 l2))
                           (nth 3 (i_vect_lbda x y u v l1 l2))))))

(in-theory (disable i_vect_lbda vect_lbda))

(defun edge_lbda (u1 u2 v1 v2 lbda)
  (mv-let (y1 y2)
          (vect_lbda u1 u2 v1 v2 lbda)
          (mv (+ u1 y1) (+ u2 y2))))

(defun i_edge_lbda (u1 u2 v1 v2 l1 l2)
  (mv-let (z11 z12 z21 z22)
          (i_vect_lbda u1 u2 v1 v2 l1 l2)
          (mv-let (y11 y12)
                  (i+ u1 u1 z11 z12)
                  (mv-let (y21 y22)
                          (i+ u2 u2 z21 z22)
                          (mv y11 y12 y21 y22)))))

(defthm i_edge_lbda_ok
  (let ((iuv (i_edge_lbda u1 u2 v1 v2 l1 l2))
        (uv  (edge_lbda u1 u2 v1 v2 lbda)))
    (let ((y11 (nth 0 iuv))
          (y12 (nth 1 iuv))
          (y21 (nth 2 iuv))
          (y22 (nth 3 iuv))
          (y1 (nth 0 uv))
          (y2 (nth 1 uv)))
      (implies (and (real/rationalp u1)
                    (real/rationalp u2)
                    (real/rationalp v1)
                    (real/rationalp v2)
                    (unitsubintervalp l1 l2)
                    (in lbda l1 l2))
               (and (in y1 y11 y12)
                    (in y2 y21 y22))))))

(defthm real/rationalp-edge_lbda
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v)
                (real/rationalp l))
           (and (real/rationalp (nth 0 (edge_lbda x y u v l)))
                (real/rationalp (nth 1 (edge_lbda x y u v l))))))

(defthm real/rationalp-i_edge_lbda
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v)
                (unitsubintervalp l1 l2))
           (and (real/rationalp (nth 0 (i_edge_lbda x y u v l1 l2)))
                (real/rationalp (nth 1 (i_edge_lbda x y u v l1 l2)))
                (real/rationalp (nth 2 (i_edge_lbda x y u v l1 l2)))
                (real/rationalp (nth 3 (i_edge_lbda x y u v l1 l2))))))

(defthm intervalp-i_edge_lbda
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp u)
                (real/rationalp v)
                (unitsubintervalp l1 l2))
           (and (intervalp (nth 0 (i_edge_lbda x y u v l1 l2))
                           (nth 1 (i_edge_lbda x y u v l1 l2)))
                (intervalp (nth 2 (i_edge_lbda x y u v l1 l2))
                           (nth 3 (i_edge_lbda x y u v l1 l2))))))

(in-theory (disable edge_lbda i_edge_lbda))

(defun check_trans_lbda (u1 u2 v1 v2 lbda)
  (and (real/rationalp u1)
       (real/rationalp u2)
       (real/rationalp v1)
       (real/rationalp v2)
       (in lbda 0 1)
       (mv-let (n1 n2)
               (normal_vec u1 u2 v1 v2)
               (mv-let (y1 y2)
                       (edge_lbda u1 u2 v1 v2 lbda)
                       (mv-let (f1 f2)
                               (vec_fld y1 y2)
                               (not (equal (dot f1 f2 n1 n2) 0)))))))

(defun i_check_trans_lbda (u1 u2 v1 v2 l1 l2)
  (and (real/rationalp u1)
       (real/rationalp u2)
       (real/rationalp v1)
       (real/rationalp v2)
       (unitsubintervalp l1 l2)
       (mv-let (n11 n12 n21 n22)
               (i_normal_vec u1 u2 v1 v2)
               (mv-let (y11 y12 y21 y22)
                       (i_edge_lbda u1 u2 v1 v2 l1 l2)
                       (mv-let (f11 f12 f21 f22)
                               (i_vec_fld y11 y12 y21 y22)
                               (mv-let (dot1 dot2)
                                       (i_dot f11 f12 f21 f22 n11 n12 n21 n22)
                                       (not (in 0 dot1 dot2))))))))

(defthm edge_trans_l1_l2
  (implies (and (i_check_trans_lbda u1 u2 v1 v2 l1 l2)
                (in lbda l1 l2))
           (check_trans_lbda u1 u2 v1 v2 lbda))
  :hints
  (("Goal"
    :use
    ((:instance
      i_dot_ok
      (x (nth 0 (vec_fld  (nth 0 (edge_lbda u1 u2 v1 v2 lbda))
                          (nth 1 (edge_lbda u1 u2 v1 v2 lbda)))))
      (y (nth 1 (vec_fld  (nth 0 (edge_lbda u1 u2 v1 v2 lbda))
                          (nth 1 (edge_lbda u1 u2 v1 v2 lbda)))))
      (u (nth 0 (normal_vec u1 u2 v1 v2)))
      (v (nth 1 (normal_vec u1 u2 v1 v2)))
      (x1 (nth 0 (i_vec_fld  (nth 0 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 1 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 2 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 3 (i_edge_lbda u1 u2 v1 v2 l1 l2)))))
      (x2 (nth 1 (i_vec_fld  (nth 0 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 1 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 2 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 3 (i_edge_lbda u1 u2 v1 v2 l1 l2)))))
      (y1 (nth 2 (i_vec_fld  (nth 0 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 1 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 2 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 3 (i_edge_lbda u1 u2 v1 v2 l1 l2)))))
      (y2 (nth 3 (i_vec_fld  (nth 0 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 1 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 2 (i_edge_lbda u1 u2 v1 v2 l1 l2))
                             (nth 3 (i_edge_lbda u1 u2 v1 v2 l1 l2)))))
      (u1 (nth 0 (i_normal_vec u1 u2 v1 v2)))
      (u2 (nth 1 (i_normal_vec u1 u2 v1 v2)))
      (v1 (nth 2 (i_normal_vec u1 u2 v1 v2)))
      (v2 (nth 3 (i_normal_vec u1 u2 v1 v2)))))
    :in-theory (disable i_dot_ok))))

(defun non-decreasing-unit (l)
  (cond ((or (endp l)
             (endp (cdr l)))
         nil)
        ((endp (cddr l))
         (and (intervalp (car l) (cadr l))
              (= (cadr l) 1)))
        (t (and (intervalp (car l) (cadr l))
                (non-decreasing-unit (cdr l))))))

(defun real/rationalp-hyps (u1 u2 v1 v2)
  (and (real/rationalp u1)
       (real/rationalp u2)
       (real/rationalp v1)
       (real/rationalp v2)))

(defun i_check_trans (u1 u2 v1 v2 l)
  (if (endp (cddr l))
      (i_check_trans_lbda u1 u2 v1 v2 (car l) (cadr l))
    (and (i_check_trans_lbda u1 u2 v1 v2 (car l) (cadr l))
         (i_check_trans u1 u2 v1 v2 (cdr l)))))

(in-theory (disable i_check_trans_lbda check_trans_lbda))

(defthm in-not-intervalp
  (implies (and (intervalp a b)
                (intervalp b c)
                (in x a c)
                (not (in x b c)))
           (in x a b))
  :hints (("goal"
           :in-theory (enable in intervalp))))

(defthm non-decreasing-unit-lemma
  (implies (and (non-decreasing-unit l)
                (in x (car l) 1)
                (not (in x (cadr l) 1))
                (non-decreasing-unit (cdr l)))
           (in x (car l) (cadr l)))
  :hints (("goal''"
           :in-theory (e/d (in) (non-decreasing-unit)))))

(defthm edge_trans_f-aux
  (implies (and (in lbda (car l) 1)
                (non-decreasing-unit l)
                (real/rationalp-hyps u1 u2 v1 v2)
                (i_check_trans u1 u2 v1 v2 l))
           (check_trans_lbda u1 u2 v1 v2 lbda))
  :hints (("goal"
           :induct (non-decreasing-unit l))))

(defun unit-partition (l)
  (and (non-decreasing-unit l)
       (= (car l) 0)))

(defthm edge_trans_f
  (implies (and (in lbda 0 1)
                (unit-partition l)
                (real/rationalp-hyps u1 u2 v1 v2)
                (i_check_trans u1 u2 v1 v2 l))
           (check_trans_lbda u1 u2 v1 v2 lbda))
  :hints (("goal"
           :use (:instance edge_trans_f-aux))))
