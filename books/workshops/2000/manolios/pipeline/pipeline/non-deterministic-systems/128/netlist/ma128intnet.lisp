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

(include-book "../../../deterministic-systems/128/netlist/netlist")
(include-book "../serial/ma128intserial")

(defun MAnet-state (pc regs mem latch1 latch2 exc-on int)
  (list 'MAnet pc regs mem latch1 latch2 exc-on int))

(defun MAnet-p (MA)
  (equal (car MA) 'Manet))

(defun MAnet-step-regs (MA)
  (let ((latch2 (nth (MA-latch2) MA)))
    (if (and (nth (latch2-validp) latch2)
	     (bor (equal (nth (latch2-op) latch2) 0)
		  (equal (nth (latch2-op) latch2) 1)))
	(update-valuation (nth (latch2-rc) latch2)
			  (net-ALU (nth (latch2-op) latch2)
				   (nth (latch2-ra-val) latch2)
				   (nth (latch2-rb-val) latch2))
			  (nth (MA-regs) MA))
      (nth (MA-regs) MA))))

(defun committed-MAnet (MA)
  (let ((pc (nth (MA-pc) MA))
	(regs (nth (MA-regs) MA))
	(mem (nth (MA-mem) MA))
	(latch1 (nth (MA-latch1) MA))
	(latch2 (nth (MA-latch2) MA))
	(exc-on (nth (MA-exc-on) MA))
	(int (nth (MA-int) MA)))
    (MAnet-state
     (- pc (shift-pc latch1 latch2))
     regs
     mem
     (update-nth (latch1-validp) nil latch1)
     (update-nth (latch2-validp) nil latch2)
     exc-on
     int)))

(defun MAnet-step (MA i)
  (let* ((cMA (committed-MAnet MA))
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
				       (committed-MAnet MA))))
	  (i (update-nth (MA-int) i (committed-MAnet MA)))
	  ((and exc-on
		(nth (latch2-validp) latch2)
		(net-excp op ra-val rb-val)
		(bor (equal op 0)
		     (equal op 1)))
	   (MAnet-state (exc-step-pc cpc regs mem)
			(exc-step-regs cpc regs mem)
			(exc-step-mem cpc regs mem)
			(exc-step-latch1 cpc regs mem)
			(exc-step-latch2 cpc regs mem)
			(exc-step-exc-on cpc regs mem)
			nil))
	  (t (MAnet-state (MA-step-pc MA)
			  (MAnet-step-regs MA)
			  mem
			  (step-latch1 MA)
			  (serial-step-latch2 MA)
			  exc-on
			  nil)))))

(defun good-MAnet (ma)
  (manet-p ma))

(defun MAnet-to-MAserial (MAnet)
  (MAserial-state
   (nth (MA-pc) MAnet)
   (nth (MA-regs) MAnet)
   (nth (MA-mem) MAnet)
   (nth (MA-latch1) MAnet)
   (nth (MA-latch2) MAnet)
   (nth (MA-exc-on) MAnet)
   (nth (MA-int) MAnet)))

(defun MAnet-rank (MA)
  (if (MAnet-p MA)
      0
    1))
