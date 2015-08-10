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

(include-book "../../../top/alist-thms")
(include-book "../../top/inst")
(include-book "../../top/det-macros")

(defun ISA-state (pc regs mem exc-on)
  (list 'ISA pc regs mem exc-on))

(defun ISA-p (x)
  (equal (car x) 'ISA))

(defmacro ISA-pc () 1)

(defmacro ISA-regs () 2)

(defmacro ISA-mem () 3)

(defmacro ISA-exc-on () 4)

(defun ALU-output (op val1 val2)
  (cond ((equal op 0)
	 (mod (+ (nfix val1) (nfix val2)) (expt 2 128)))
	(t (mod (* (nfix val1) (nfix val2)) (expt 2 128)))))

(defun excp (op val1 val2)
  (cond ((equal op 0)
	 (not (equal (mod (+ (nfix val1) (nfix val2)) (expt 2 128))
		     (+ (nfix val1) (nfix val2)))))
	(t (not (equal (mod (* (nfix val1) (nfix val2)) (expt 2 128))
		       (* (nfix val1) (nfix val2)))))))

(defun ISA-step-regs (op rc ra-val rb-val regs)
  (update-valuation rc
		    (ALU-output op ra-val rb-val)
		    regs))

(defun ISA-step-pc (ISA)
  (1+ (nth (ISA-pc) ISA)))

