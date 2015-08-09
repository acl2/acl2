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

(include-book "isa128int")

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

(defun MA-state (pc regs mem latch1 latch2 exc-on int)
  (list 'MA pc regs mem latch1 latch2 exc-on int))

(defun MA-p (x)
  (equal (car x) 'MA))

(defmacro MA-pc () 1)

(defmacro MA-regs () 2)

(defmacro MA-mem () 3)

(defmacro MA-latch1 () 4)

(defmacro MA-latch2 () 5)

(defmacro MA-exc-on () 6)

(defmacro MA-int () 7)

(defun MA-step-regs (MA)
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
		(nfix (value-of (nth (latch1-ra) latch1)
				(nth (MA-regs) MA)))
		(nfix (value-of (nth (latch1-rb) latch1)
				(nth (MA-regs) MA))))
      (update-nth (latch2-validp) nil (nth (MA-latch2) MA)))))

(defthm alu-output-nfix
  (equal (alu-output op (nfix x) (nfix y))
	 (alu-output op x y)))

(defthm excp-nfix
  (equal (excp op (nfix x) (nfix y))
	 (excp op x y)))

(defun MA-step-pc (MA)
  (if (stall-condp MA)
      (nth (MA-pc) MA)
    (1+ (nth (MA-pc) MA))))

(encapsulate
 ((exc-step-pc (pc regs mem) t)
  (exc-step-regs (pc regs mem) t)
  (exc-step-mem (pc regs mem) t)
  (exc-step-latch1 (pc regs mem) t)
  (exc-step-latch2 (pc regs mem) t)
  (exc-step-exc-on (pc regs mem) t))

 (local (defun exc-step-pc (pc regs mem)
	  (declare (ignore pc regs mem))
	  0))

 (local (defun exc-step-regs (pc regs mem)
	  (declare (ignore pc regs mem))
	  nil))

 (local (defun exc-step-mem (pc regs mem)
	  (declare (ignore pc regs mem))
	  nil))

 (local (defun exc-step-latch1 (pc regs mem)
	  (declare (ignore pc regs mem))
	  nil))

 (local (defun exc-step-latch2 (pc regs mem)
	  (declare (ignore pc regs mem))
	  nil))

 (local (defun exc-step-exc-on (pc regs mem)
	  (declare (ignore pc regs mem))
	  nil))

 (defthm flushed-MA-exc-step
   (and (not (nth (latch1-validp) (exc-step-latch1 pc regs mem)))
	(not (nth (latch2-validp) (exc-step-latch2 pc regs mem)))))

 (defthm exc-step-pc-rational
   (rationalp (exc-step-pc pc regs mem))))

(defun n (v)
  (cond ((endp v) 0)
        ((car v) (+ 1 (* 2 (n (cdr v)))))
        (t (* 2 (n (cdr v))))))

(defun convert-regs (regs)
  (if (consp regs)
      (if (consp (car regs))
	  (acons (caar regs)
		 (n (cdar regs))
		 (convert-regs (cdr regs)))
	(cons (car regs) (convert-regs (cdr regs))))
    nil))

(defun convert-latch2 (l2)
  (let ((validp (nth (latch2-validp) l2))
	(op (nth (latch2-op) l2))
	(rc (nth (latch2-rc) l2))
	(ra-val (nth (latch2-ra-val) l2))
	(rb-val (nth (latch2-rb-val) l2)))
    (latch2 validp op rc (n ra-val) (n rb-val))))

(defstub int-handler (regs mem int) t)

(defun ISA-step (ISA i)
  (let* ((pc (nth (ISA-pc) ISA))
	 (regs (nth (ISA-regs) ISA))
	 (mem (nth (ISA-mem) ISA))
	 (exc-on (nth (ISA-exc-on) ISA))
	 (int (nth (ISA-int) ISA))
	 (inst (value-of pc mem))
	 (op (nth (Inst-opcode) inst))
	 (rc (nth (Inst-rc) inst))
	 (ra (nth (Inst-ra) inst))
	 (rb (nth (Inst-rb) inst))
	 (ra-val (value-of ra regs))
	 (rb-val (value-of rb regs)))
    (cond (int (ISA-state pc regs (int-handler regs mem int) exc-on nil))
	  (i (ISA-state pc regs mem exc-on i))
	  ((bor (equal op 0)
		(equal op 1))
	   (if (and exc-on
		    (excp op ra-val rb-val))
	       (ISA-state (exc-step-pc pc regs mem)
			  (convert-regs (exc-step-regs pc regs mem))
			  (exc-step-mem pc regs mem)
			  (exc-step-exc-on pc regs mem)
			  nil)
	     (ISA-state (ISA-step-pc ISA)
			(ISA-step-regs op rc ra-val rb-val regs)
			mem
			exc-on
			nil)))
	  (t (ISA-state (ISA-step-pc ISA) regs mem exc-on nil)))))

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
	(exc-on (nth (MA-exc-on) MA))
	(int (nth (MA-int) MA)))
    (MA-state
     (- pc (shift-pc latch1 latch2))
     regs
     mem
     (update-nth (latch1-validp) nil latch1)
     (update-nth (latch2-validp) nil latch2)
     exc-on
     int)))

(defun MA-step (MA i)
  (let* ((cMA (committed-MA MA))
	 (cpc (nth (MA-pc) cMA))
	 (regs (nth (MA-regs) MA))
	 (mem (nth (MA-mem) MA))
	 (latch2 (nth (MA-latch2) MA))
	 (exc-on (nth (MA-exc-on) MA))
	 (int (nth (MA-int) MA))
	 (op (nth (latch2-op) latch2))
	 (ra-val (nth (latch2-ra-val) latch2))
	 (rb-val (nth (latch2-rb-val) latch2)))
    (cond (int (update-nth (MA-mem)
			   (int-handler regs mem int)
			   (update-nth (MA-int)
				       nil
				       (committed-MA MA))))
	  (i (update-nth (MA-int) i (committed-MA MA)))
	  ((and exc-on
		(nth (latch2-validp) latch2)
		(excp op ra-val rb-val)
		(bor (equal op 0)
		     (equal op 1)))
	   (MA-state (exc-step-pc cpc regs mem)
		     (convert-regs (exc-step-regs cpc regs mem))
		     (exc-step-mem cpc regs mem)
		     (exc-step-latch1 cpc regs mem)
		     (convert-latch2 (exc-step-latch2 cpc regs mem))
		     (exc-step-exc-on cpc regs mem)
		     nil))
	  (t (MA-state (MA-step-pc MA)
		       (MA-step-regs MA)
		       mem
		       (step-latch1 MA)
		       (step-latch2 MA)
		       exc-on
		       nil)))))
