; Arithmetic-5 Library
; Copyright (C) 2009 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; types.lisp
;;;
;;; The neccesity for these theorems does not arise very often,
;;; but it can be very irritating when they do.  
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../../support/top"))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm one-a
   (implies (and (< 0 x)
		 (< x 1))
	    (not (integerp x)))))

(local
 (defthm one-b
   (implies (and (< x 0)
		 (< -1 x))
	    (not (integerp x)))))

(local
 (defthm two-a
   (implies (and (real/rationalp x)
		 (< 1 x))
	    (and (< 0 (/ x))
		 (< (/ x) 1)))
   :hints (("Goal" :in-theory (enable NORMALIZE-<-/-TO-*-2)))))

(local
 (defthm two-b
   (implies (and (real/rationalp x)
		 (< x -1))
	    (and (< (/ x) 0)
		 (< -1 (/ x))))
   :hints (("Goal" :in-theory (enable NORMALIZE-<-/-TO-*-1)))))

(local
 (defthm three
   (implies (complex/complex-rationalp x)
	    (not (integerp (/ x))))))

(defthm not-integerp-/-1
  (implies (< 1 x)
	   (not (integerp (/ x))))
  :hints (("Goal" :cases ((real/rationalp x)
			  (complex/complex-rationalp x)))))

(defthm not-integerp-/-2
  (implies (< x -1)
	   (not (integerp (/ x))))
  :hints (("Goal" :cases ((real/rationalp x)
			  (complex/complex-rationalp x)))))

(defthm integerp-/-helper
  (implies (integerp x)
	   (equal (integerp (/ x))
		  (or (equal x -1)
		      (equal x 0)
		      (equal x 1))))
  :hints (("Goal" :use ((:instance not-integerp-/-1)
			(:instance not-integerp-/-2))
	          :in-theory (disable not-integerp-/-1 
				      not-integerp-/-2))))
