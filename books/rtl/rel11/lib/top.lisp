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

(include-book "doc")

;; The books included below are useful for most floating-point applications:

(include-book "basic") ;basic arithmetic functions: floor, ceiling, and remainder

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "reps") ;floating-point formats and representations

(include-book "float") ;floating-point numbers

(include-book "round") ;floating-point rounding

(include-book "util") ;misc helpful stuff including a few macros

;; Special-purpose theories:

(include-book "add") ;support for reasoning about addition

(include-book "mult") ;integer multiplication

(include-book "div") ;Newton-Raphson division

(include-book "srt") ;SRT division and square root

(include-book "sqrt") ;approximation to square root

(include-book "excps")

;; This is relevant to code derived from SystemC:

(include-book "masc")

;; This must be included to use GL with this library:

(include-book "gl")



