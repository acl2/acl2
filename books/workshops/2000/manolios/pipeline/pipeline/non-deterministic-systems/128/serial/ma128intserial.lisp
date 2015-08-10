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

(include-book "../../../deterministic-systems/128/serial/serial")
(include-book "../../../top/nth-thms")
(include-book "../../../top/meta")
(include-book "../../../top/defun-weak-sk")
(include-book "../../top/non-det-encap-wfbisim")
(include-book "../top/ma128int")

(defun MAserial-state (pc regs mem latch1 latch2 exc-on int)
  (list 'MAserial pc regs mem latch1 latch2 exc-on int))

(defun MAserial-p (MA)
  (equal (car MA) 'Maserial))

(defun serial-step-latch2 (MA)
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

(defun MAserial-step-regs (MA)
  (let ((latch2 (nth (MA-latch2) MA)))
    (if (and (nth (latch2-validp) latch2)
	     (bor (equal (nth (latch2-op) latch2) 0)
		  (equal (nth (latch2-op) latch2) 1)))
	(update-valuation (nth (latch2-rc) latch2)
			  (serial-ALU (nth (latch2-op) latch2)
				      (nth (latch2-ra-val) latch2)
				      (nth (latch2-rb-val) latch2))
			  (nth (MA-regs) MA))
      (nth (MA-regs) MA))))

(defun committed-MAserial (MA)
  (let ((pc (nth (MA-pc) MA))
	(regs (nth (MA-regs) MA))
	(mem (nth (MA-mem) MA))
	(latch1 (nth (MA-latch1) MA))
	(latch2 (nth (MA-latch2) MA))
	(exc-on (nth (MA-exc-on) MA))
	(int (nth (MA-int) MA)))
    (MAserial-state
     (- pc (shift-pc latch1 latch2))
     regs
     mem
     (update-nth (latch1-validp) nil latch1)
     (update-nth (latch2-validp) nil latch2)
     exc-on
     int)))

(defun MAserial-step (MA i)
  (let* ((cMA (committed-MAserial MA))
	 (cpc (nth (MA-pc) cMA))
	 (regs (convert-regs (nth (MA-regs) MA)))
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
				       (committed-MAserial MA))))
	  (i (update-nth (MA-int) i (committed-MAserial MA)))
	  ((and exc-on
		(nth (latch2-validp) latch2)
		(serial-excp op ra-val rb-val)
		(bor (equal op 0)
		     (equal op 1)))
	   (MAserial-state (exc-step-pc cpc regs mem)
			   (exc-step-regs cpc regs mem)
			   (exc-step-mem cpc regs mem)
			   (exc-step-latch1 cpc regs mem)
			   (exc-step-latch2 cpc regs mem)
			   (exc-step-exc-on cpc regs mem)
			   nil))
	  (t (MAserial-state (MA-step-pc MA)
			     (MAserial-step-regs MA)
			     mem
			     (step-latch1 MA)
			     (serial-step-latch2 MA)
			     exc-on
			     nil)))))

(defun good-MAserial (MA)
  (MAserial-p MA))

(defun MAserial-to-MA (MAserial)
  (MA-state
   (nth (MA-pc) MAserial)
   (convert-regs (nth (MA-regs) MAserial))
   (nth (MA-mem) MAserial)
   (nth (MA-latch1) MAserial)
   (convert-latch2 (nth (MA-latch2) MAserial))
   (nth (MA-exc-on) MAserial)
   (nth (MA-int) MAserial)))

; This is written this way because ACL2 otherwise stores a simplified
; version of the body as a definition and this screws up my Macros.

(defun MAserial-rank (MA)
  (if (MAserial-p MA)
      0
    1))

(defthm value-of-convert-regs
  (equal (value-of x (convert-regs r))
	 (if (consp (assoc-equal x r))
	     (n (value-of x r))
	   nil)))

(defthm value-of-x
  (implies (not (consp (assoc-equal x r)))
	   (equal (value-of x r)
		  nil)))

(defthm convert-regs-update-val
 (equal (convert-regs (update-valuation x y r))
	(update-valuation x (n y) (convert-regs r))))

(defthm nfix-n
 (equal (nfix (n x))
	(n x)))
