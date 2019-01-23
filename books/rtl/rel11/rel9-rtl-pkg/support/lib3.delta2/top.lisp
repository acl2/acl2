; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(set-enforce-redundancy t)

(include-book "basic") ;basic arithmetic functions: floor, ceiling, and mod

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "float") ;floating-point numbers

(include-book "round") ;floating-point rounding
