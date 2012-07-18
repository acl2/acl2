; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")

; Originally, I added (vl-gc) because calling (gc$) directly could sometimes
; lead to bad printing confusion.  (vl-gc) avoided this by calling "our-gc"
; from hons-raw.lisp, which sleeps until the GC actually happens.
;
; I later found that I wanted to GC less frequently in some cases.  So, now
; vl-gc only tries to garbage collect if more than 1 GB has been allocated
; since the last time it was called.  In some cases this might not quite work.
; In particular, intervening (gc$) calls and ordinary GC might cause the
; *vl-gc-previously-used* variable to have the "wrong" value.  But, I think
; that in the cases that (vl-gc) is called, it's called frequently enough that
; this shouldn't typically be that much of a problem.

(defun vl-gc ()
  (declare (xargs :guard t))
  nil)

(defparameter *vl-gc-previously-used*
  ;; Originally this was 0, but now I've upped it to 1 GB.  This only affects
  ;; the initial GC.  This is probably better than assuming the whole system
  ;; uses no memory.
  (expt 2 30))

(defun vl-gc ()

  #+Clozure
  (let* ((currently-used (ccl::%usedbytes))
         (allocated      (- currently-used *vl-gc-previously-used*)))
;     (cw "vl-gc: currently used: ~x0~%" currently-used)
;     (cw "vl-gc: previously used: ~x0~%" *vl-gc-previously-used*)
;     (cw "vl-gc: allocated since last: ~x0~%" allocated)
    (when (> allocated (expt 2 30))
      (finish-output)
      (acl2::hl-system-gc)
      (setq *vl-gc-previously-used* (ccl::%usedbytes)))
    nil)

  nil)
