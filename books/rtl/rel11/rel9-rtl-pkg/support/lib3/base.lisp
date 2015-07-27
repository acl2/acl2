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
; (include-book "../../../misc/rtl-untranslate")
; to inhibit expansion of macros in proof output.

; We deliberately exclude any *-helpers.lisp books that may appear here.

(include-book "../lib2.delta1/rtl") ;semantics of the basic RTL primitives

(include-book "../lib2.delta1/rtlarr") ;semantics RTL array primitives

(include-book "../lib2/basic") ;properties of basic arithmetic functions: floor, ceiling, 
;                       exponential, and remainder;;  Wed Feb  4 16:40:37 2009

;(include-book "../lib1/bits") ;bit vectors
(include-book "../lib2.delta2/bits") ;bit vectors ;; Tue Feb 24 09:33:20 2009


(include-book "../lib2.delta2/log") ;logical operations ;; Tue Feb 24 09:33:47 2009

(include-book "../lib2.delta1/float") ;floating-point numbers

(include-book "../lib2.delta1/reps") ;floating-point formats and representations

(include-book "../lib2.delta1/round") ;floating-point rounding

(include-book "../lib2.delta2/add") ;support for reasoning about floating-point addition
;                      (leading one prediction and sticky bit computation)

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../arithmetic/top")

(include-book "../lib2.delta1/arith") ;general arithmetic package

;
; let go Thu Feb 19 09:43:32 2009

(include-book "../lib2.delta1/util") ;misc helpful stuff including a few macros


(include-book "../lib2.delta1/bvecp-raw-helpers")  
;; ; better bvecp-raw-helpers.lisp, Fri Jun 29 10:13:32 2007

(include-book "../lib2.delta1/simple-loop-helpers")  

(include-book "../lib2/rom-helpers")  


(include-book "../lib2.delta1/bvecp-helpers")

(include-book "../lib2.delta1/logn")


(include-book "../lib2.delta3/simplify-model-helpers") ; Tue Feb  8 15:06:05
  ; 2011. export new lemma.


(include-book "../lib2.delta1/logn2log")
