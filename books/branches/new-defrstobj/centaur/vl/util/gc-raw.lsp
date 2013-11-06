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

(defparameter *vl-gc-baseline*
  ;; Originally this was 0, but now I've upped it to 1 GB.  This only affects
  ;; the initial GC.  This is probably better than assuming the whole system
  ;; uses no memory.
  (expt 2 30))

(defparameter *vl-gc-threshold*
  (expt 2 30))

(defun set-vl-gc-baseline ()
  #+Clozure
  (setq *vl-gc-baseline* (ccl::%usedbytes))
  nil)

(defun set-vl-gc-threshold (bytes)
  (setq *vl-gc-threshold* bytes)
  nil)

(defun vl-gc ()

  #+Clozure
  (let* ((currently-used (ccl::%usedbytes))
         (allocated      (- currently-used *vl-gc-baseline*)))
    (when (> allocated *vl-gc-threshold*)
      (finish-output)
      (acl2::hl-system-gc)
      (set-vl-gc-baseline)))

  nil)
