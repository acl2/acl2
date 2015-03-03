; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "RTL")

(local (include-book "trunc"))
(include-book "log")
(include-book "float")
(include-book "trunc")
(local (include-book "bits"))
(local (include-book "../../arithmetic/top"))
(local (in-theory (enable expt-minus)))

(defthm bits-trunc-2
  (implies (and (= n (1+ (expo x)))
;(rationalp x) ;(integerp x) 
                (>= x 0)
                ;(integerp n) 
;                (>= n k)
                (integerp k) 
                (> k 0)
                )
           (= (trunc x k)
              (* (expt 2 (- n k))
                 (bits x (1- n) (- n k)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable bits trunc-rewrite expt-split))))


(local
 (defthm bits-trunc-3
   (implies (and (integerp x) 
                 (> x 0)
                 (integerp n) (> n k)
                 (integerp k) (> k 0)
                 (= (expo x) (1- n)))
            (= (trunc x k)
               (logand x (- (expt 2 n) (expt 2 (- n k))))))
   :rule-classes ()
   :hints (("goal" :use ((:instance bits-trunc-2)
                         (:instance logand-slice (k (- n k)))))
           )))

(local
 (defthm bits-trunc-4
   (implies (and (integerp x) (> x 0)
                 (integerp n) (> n k)
                 (integerp k) (> k 0)
                 (>= x (expt 2 (1- n)))
                 (< x (expt 2 n)))
            (= (trunc x k)
               (logand x (- (expt 2 n) (expt 2 (- n k))))))
   :rule-classes ()
   :hints (("goal" :use ((:instance bits-trunc-3)
                         (:instance expo-unique (n (1- n))))))))

(local
 (defthm bits-trunc-5
   (implies (and (integerp x) (> x 0)
                 (integerp m) (>= m n)
                 (integerp n) (> n k)
                 (integerp k) (> k 0)
                 (>= x (expt 2 (1- n)))
                 (< x (expt 2 n)))
            (= (trunc x k)
               (logand x (mod (- (expt 2 m) (expt 2 (- n k))) (expt 2 n)))))
   :rule-classes ()
   :hints (("goal" :use ((:instance bits-trunc-4)
                         ;(:instance mod-2m-2n-k)
                         )))))

(include-book "land0")
(include-book "merge")

(defthm bits-trunc-original
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x) (> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0)
                )
           (= (trunc x k)
              (land0 x (- (expt 2 m) (expt 2 (- n k))) n)))
  :rule-classes ()
  :hints (("goal" :in-theory (e/d (bits-tail land0 expt-split) (expt-minus))
		  :use ((:instance bits-trunc-5)))))

#|
(defthm bits-trunc-6
  (implies (and (integerp x) (> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0)
                (>= x (expt 2 (1- n)))
                (< x (expt 2 n)))
           (= (trunc x k)
              (logand x (- (expt 2 m) (expt 2 (- n k))))))
  :rule-classes ()
  :hints (("goal" :use (;(:instance hack-82)
                        (:instance bits-trunc-5)
			(:instance expt-weak-monotone (n (- n k)))
			(:instance and-dist-d (y (- (expt 2 m) (expt 2 (- n k)))))))))
|#





