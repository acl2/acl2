; ACL2 books using the bdd hints
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann
; email:       Matt_Kaufmann@email.mot.com
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(ubt! 1)
(certify-book "bdd-primitives")
:u
(certify-book "pg-theory")
:u
(certify-book "alu")
:u
(certify-book "alu-proofs" 0 nil)
:u
(certify-book "hamming" 0 nil) ; No need to compile
:u
(certify-book "bool-ops" 0)
:u
(certify-book "cbf")
(write-benchmark-file "be/" state)
:u
(set-ld-pre-eval-print :never state)
(certify-book "benchmarks" 0 nil)
:u
