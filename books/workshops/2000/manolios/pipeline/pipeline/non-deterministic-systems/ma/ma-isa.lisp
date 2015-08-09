;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

(in-package "ACL2")

(include-book "../../top/nth-thms")
(include-book "../../top/meta")
(include-book "../top/non-det-encap-wfbisim")
(include-book "isa")
(include-book "ma")

(defun b-to-num (x)
  (if x 1 0))

(defun shift-pc (latch1 latch2)
  (+ (b-to-num (nth (latch1-validp) latch1))
     (b-to-num (nth (latch2-validp) latch2))))

(defun committed-MA (MA)
  (let ((pc (nth (MA-pc) MA))
	(regs (nth (MA-regs) MA))
	(mem (nth (MA-mem) MA))
	(latch1 (nth (MA-latch1) MA))
	(latch2 (nth (MA-latch2) MA)))
    (MA-state
     (- pc (shift-pc latch1 latch2))
     regs
     mem
     (update-nth (latch1-validp) nil latch1)
     (update-nth (latch2-validp) nil latch2))))

(defun MA-= (x y)
  (let ((x-latch1 (nth (MA-latch1) x))
	(x-latch2 (nth (MA-latch2) x))
	(y-latch1 (nth (MA-latch1) y))
	(y-latch2 (nth (MA-latch2) y)))
    (and (equal (nth (MA-pc) x)
		(nth (MA-pc) y))
	 (equal (nth (MA-regs) x)
		(nth (MA-regs) y))
	 (equal (nth (MA-mem) x)
		(nth (MA-mem) y))
	 (cond ((nth (latch1-validp) x-latch1)
		(equal x-latch1 y-latch1))
	       (t (not (nth (latch1-validp) y-latch1))))
	 (cond ((nth (latch2-validp) x-latch2)
		(equal x-latch2 y-latch2))
	       (t (not (nth (latch2-validp) y-latch2)))))))

(defun good-MA (MA)
  (and (rationalp (nth (MA-pc) MA))
       (let ((latch1 (nth (MA-latch1) MA))
	     (latch2 (nth (MA-latch2) MA))
	     (NMA (committed-MA MA)))
	 (case (shift-pc latch1 latch2)
	   (0 t)
	   (1 (MA-= (MA-step NMA nil) MA))
	   (otherwise (MA-= (MA-step (MA-step NMA nil) nil) MA))))))

(defun MA-to-ISA (MA)
  (let ((MA (committed-MA MA)))
    (ISA-state
     (nth (MA-pc) MA)
     (nth (MA-regs) MA)
     (nth (MA-mem) MA))))

(defun MA-rank (MA)
  (let ((latch1 (nth (MA-latch1) MA))
	(latch2 (nth (MA-latch2) MA)))
    (cond ((nth (latch2-validp) latch2)
	   0)
	  ((nth (latch1-validp) latch1)
	   1)
	  (t 2))))

(generate-full-system isa-step isa-p ma-step ma-p
		      ma-to-isa good-ma ma-rank)

(in-theory (disable value-of update-valuation))

(prove-web isa-step isa-p ma-step ma-p ma-to-isa ma-rank)

(wrap-it-up isa-step isa-p ma-step ma-p
	    good-ma ma-to-isa ma-rank)
