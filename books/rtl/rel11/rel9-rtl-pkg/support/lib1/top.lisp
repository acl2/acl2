; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(set-enforce-redundancy t)

; Optionally, one may wish to consider:
; (include-book "misc/rtl-untranslate" :dir :system)
; to inhibit expansion of macros in proof output.

; We deliberately exclude any *-helpers.lisp books that may appear here.

(include-book "rtl") ;semantics of the basic RTL primitives

(include-book "rtlarr") ;semantics RTL array primitives

(include-book "basic") ;properties of basic arithmetic functions: floor, ceiling, 
;                       exponential, and remainder

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "float") ;floating-point numbers

(include-book "reps") ;floating-point formats and representations

(include-book "round") ;floating-point rounding

(include-book "add") ;support for reasoning about floating-point addition
;                      (leading one prediction and sticky bit computation)

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../../arithmetic/top")
(include-book "arith") ;general arithmetic package

(include-book "util") ;misc helpful stuff including a few macros
