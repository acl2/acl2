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
;;; mod-expt-fast.lisp
;;;
;;; This book is a modification of one submitted by Warren Hunt.  It
;;; contains an optimized version of mod-expt --- mod-expt-fast.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "floor-mod"))

(local
 (include-book "more-floor-mod"))

(local
 (include-book "truncate-rem"))

(local
 (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
					       HIST PSPV))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Here is a recursive definition (* acc (mod (expt a i) n)):

(defun mod-expt-fast-1 (a i n acc)
  (declare (xargs :guard (and (integerp a)
                              (natp i)
                              (integerp n)
                              (< 0 n)
                              (integerp acc)
                              )))
  (if (zp i)
      acc
    ;; Divide by 2 using right shift
    (let ((floor-i-by-2 (ash i -1)))
      (if (oddp i)
	  (mod-expt-fast-1 (mod (* a a) n)
			     floor-i-by-2
			     n
			     (mod (* a acc) n))
	(mod-expt-fast-1 (mod (* a a) n)
			   floor-i-by-2
			   n
			   acc)))))

(defun mod-expt-fast (a i n)
  (declare (xargs :guard (and (real/rationalp a)
                              (integerp i)
                              (not (and (eql a 0) (< i 0)))
                              (<= 0 i)
                              (real/rationalp n)
                              (not (eql n 0)))))
  (if (and (integerp a) (integerp n) (< 0 n))
      (mod-expt-fast-1 a i n 1)
    (mod (expt a i) n)))

(local
 (defthm mod-expt-fast-is-mod-expt-helper
   (implies (and (integerp a)
		 (natp i)
		 (integerp n)
		 (< 0 n)
		 (natp acc)
		 (< acc n))
	    (equal (mod-expt-fast-1 a i n acc)
		   (mod (* acc (expt a i)) n)))))

(defthm mod-expt-fast-is-mod-expt
  (implies (and (real/rationalp a)
                (natp i)
                (integerp n)
                (< 1 n))
           (equal (mod-expt-fast a i n)
                  (mod-expt a i n))))

(in-theory (disable mod-expt-fast))
