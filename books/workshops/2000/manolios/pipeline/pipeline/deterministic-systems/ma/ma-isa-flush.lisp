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

#|

A proof using flushing.

|#

(in-package "ACL2")

(include-book "../../top/nth-thms")
(include-book "../../top/meta")
(include-book "../top/det-encap-wfbisim")
(include-book "isa")
(include-book "ma")

(defun flush-step-MA (MA)
  (let ((pc (nth (MA-pc) MA))
	(mem (nth (MA-mem) MA))
	(latch1 (nth (MA-latch1) MA)))
    (MA-state pc
	      (step-regs MA)
	      mem
	      (if (stall-condp MA)
		  latch1
		(update-nth (latch1-validp) nil latch1))
	      (step-latch2 MA))))

#|
Notice that this will work, but it slows down things by a factor of 2

(defun flushed-MA (MA)
  (flush-step-ma (flush-step-ma (flush-step-ma ma))))

|#

(defun flushed-MA (MA)
  (let ((latch1 (nth (MA-latch1) MA))
	(latch2 (nth (MA-latch2) MA)))
    (cond ((stall-condp MA)
	   (flush-step-ma (flush-step-ma (flush-step-ma ma))))
	  ((nth (latch1-validp) latch1)
	   (flush-step-ma (flush-step-ma ma)))
	  ((nth (latch2-validp) latch2)
	   (flush-step-ma ma))
	  (t ma))))

(defun good-MA (ma)
  (ma-p ma))

(defun MA-to-ISA (MA)
  (let ((MA (flushed-MA MA)))
    (ISA-state
     (nth (MA-pc) MA)
     (nth (MA-regs) MA)
     (nth (MA-mem) MA))))

(defun MA-rank (MA)
  (let ((latch1 (nth (MA-latch1) MA))
	(latch2 (nth (MA-latch2) MA)))
    (cond ((stall-condp MA)
	   3)
	  ((nth (latch1-validp) latch1)
	   2)
	  ((nth (latch2-validp) latch2)
	   1)
	  (t 0))))

(generate-full-system isa-step isa-p ma-step ma-p
		      ma-to-isa good-ma ma-rank)

(in-theory (disable value-of update-valuation))
(in-theory (enable nth-over-if))

(prove-web isa-step isa-p ma-step ma-p ma-to-isa ma-rank)

(wrap-it-up isa-step isa-p ma-step ma-p
	    good-ma ma-to-isa ma-rank)
