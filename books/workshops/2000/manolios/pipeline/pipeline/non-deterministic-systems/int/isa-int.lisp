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

The ISA specification of Sawada's machine with interrupts.

|#

(in-package "ACL2")

(include-book "../../top/alist-thms")
(include-book "../top/inst")

(defun ISA-state (pc regs mem int)
  (list 'ISA pc regs mem int))

(defun ISA-p (x)
  (equal (car x) 'ISA))

(defmacro ISA-pc () 1)

(defmacro ISA-regs () 2)

(defmacro ISA-mem () 3)

(defmacro ISA-int () 4)

(defun add-rc (ra rb rc regs)
  (update-valuation rc
		    (+ (value-of ra regs)
		       (value-of rb regs))
		    regs))

(defun mul-rc (ra rb rc regs)
  (update-valuation rc
		    (* (value-of ra regs)
		       (value-of rb regs))
		    regs))

(defun ISA-add (rc ra rb ISA)
  (ISA-state (1+ (nth (ISA-pc) ISA))
	     (add-rc ra rb rc (nth (ISA-regs) ISA))
	     (nth (ISA-mem) ISA)
	     nil))

(defun ISA-mul (rc ra rb ISA)
  (ISA-state (1+ (nth (ISA-pc) ISA))
	     (mul-rc ra rb rc (nth (ISA-regs) ISA))
	     (nth (ISA-mem) ISA)
	     nil))

(defun ISA-default (ISA)
  (ISA-state (1+ (nth (ISA-pc) ISA))
	     (nth (ISA-regs) ISA)
	     (nth (ISA-mem) ISA)
	     nil))

(defstub int-handler (regs mem int) t)

(defun ISA-step (ISA i)
  (let ((pc (nth (ISA-pc) ISA))
	(regs (nth (ISA-regs) ISA))
	(mem (nth (ISA-mem) ISA))
	(int (nth (ISA-int) ISA)))
    (cond (int (ISA-state pc regs (int-handler regs mem int) nil))
	  (i (ISA-state pc regs mem i))
	  (t (let ((inst (value-of (nth (ISA-pc) ISA) (nth (ISA-mem) ISA))))
	       (let ((op (nth (Inst-opcode) inst))
		     (rc (nth (Inst-rc) inst))
		     (ra (nth (Inst-ra) inst))
		     (rb (nth (Inst-rb) inst)))
		 (cond ((equal op 0) ; add
			(ISA-add rc ra rb ISA))
		       ((equal op 1) ; mul
			(ISA-mul rc ra rb ISA))
		       (t (ISA-default ISA)))))))))
