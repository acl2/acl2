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

The MA specification of Sawada's machine with interrupts.

|#

(in-package "ACL2")

(include-book "isa-int")
(include-book "../top/non-det-macros")

(defun latch1 (validp op rc ra rb)
  (list 'latch1 validp op rc ra rb))

(defmacro latch1-validp () 1)

(defmacro latch1-op () 2)

(defmacro latch1-rc () 3)

(defmacro latch1-ra () 4)

(defmacro latch1-rb () 5)

(defun latch2 (validp op rc ra-val rb-val)
  (list 'latch2 validp op rc ra-val rb-val))

(defmacro latch2-validp () 1)

(defmacro latch2-op () 2)

(defmacro latch2-rc () 3)

(defmacro latch2-ra-val () 4)

(defmacro latch2-rb-val () 5)

(defun MA-state (pc regs mem latch1 latch2 int)
  (list 'MA pc regs mem latch1 latch2 int))

(defun MA-p (x)
  (equal (car x) 'MA))

(defmacro MA-pc () 1)

(defmacro MA-regs () 2)

(defmacro MA-mem () 3)

(defmacro MA-latch1 () 4)

(defmacro MA-latch2 () 5)

(defmacro MA-int () 6)

(defun ALU-output (op val1 val2)
  (cond ((equal op 0)
	 (+ val1 val2))
	(t (* val1 val2))))

(defun step-regs (MA)
  (let ((latch2 (nth (MA-latch2) MA)))
    (if (and (nth (latch2-validp) latch2)
	     (bor (equal (nth (latch2-op) latch2) 0)
		  (equal (nth (latch2-op) latch2) 1)))
	(update-valuation (nth (latch2-rc) latch2)
			  (ALU-output (nth (latch2-op) latch2)
				      (nth (latch2-ra-val) latch2)
				      (nth (latch2-rb-val) latch2))
			  (nth (MA-regs) MA))
      (nth (MA-regs) MA))))

(defun stall-condp (MA)
  (let ((latch1 (nth (MA-latch1) MA))
	(latch2 (nth (MA-latch2) MA)))
    (and (nth (latch2-validp) latch2)
	 (nth (latch1-validp) latch1)
	 (bor (equal (nth (latch1-ra) latch1)
		     (nth (latch2-rc) latch2))
	      (equal (nth (latch1-rb) latch1)
		     (nth (latch2-rc) latch2))))))

(defun step-latch1 (MA)
  (let ((latch1 (nth (MA-latch1) MA))
	(inst (value-of (nth (MA-pc) MA) (nth (MA-mem) MA))))
    (cond ((stall-condp MA)
	   latch1)
	  (t (latch1 t
		     (nth (Inst-opcode) inst)
		     (nth (Inst-rc) inst)
		     (nth (Inst-ra) inst)
		     (nth (Inst-rb) inst))))))

(defun step-latch2 (MA)
  (let ((latch1 (nth (MA-latch1) MA)))
    (if (nth (latch1-validp) latch1)
	(latch2 (not (stall-condp MA))
		(nth (latch1-op) latch1)
		(nth (latch1-rc) latch1)
		(value-of (nth (latch1-ra) latch1)
			  (nth (MA-regs) MA))
		(value-of (nth (latch1-rb) latch1)
			  (nth (MA-regs) MA)))
      (update-nth (latch2-validp) nil (nth (MA-latch2) MA)))))

(defun step-pc (MA)
  (if (stall-condp MA)
      (nth (MA-pc) MA)
    (1+ (nth (MA-pc) MA))))

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
	(latch2 (nth (MA-latch2) MA))
	(int (nth (MA-int) MA)))
    (MA-state
     (- pc (shift-pc latch1 latch2))
     regs
     mem
     (update-nth (latch1-validp) nil latch1)
     (update-nth (latch2-validp) nil latch2)
     int)))

(defun MA-step (MA i)
  (cond ((nth (MA-int) MA)
	 (update-nth (MA-mem)
		     (int-handler (nth (MA-regs) MA)
				  (nth (MA-mem) MA)
				  (nth (MA-int) MA))
		     (update-nth (MA-int)
				 nil
				 (committed-MA MA))))
	(i (update-nth (MA-int) i (committed-MA MA)))
	(t (MA-state (step-pc MA)
		     (step-regs MA)
		     (nth (MA-mem) MA)
		     (step-latch1 MA)
		     (step-latch2 MA)
		     nil))))
