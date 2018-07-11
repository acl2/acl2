; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "utilities/top" :ttags :all)

;; ======================================================================

;; Proofs of correctness of various x86 programs: We exclude these
;; from the x86isa documentation.  There are a lot of name clashes
;; here.  The empty encapsulates below avoid this name clash problem
;; while ensuring that the books get built as a part of the
;; regression.

;; ----------------------------------------------------------------------
;; Application Programs:

;; The factorial program has been proved correct using two methods:
;; inductive assertions and wormhole abstraction.
(local
 (encapsulate
   ()
   (local (include-book "factorial/fact-inductive-assertions" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "factorial/fact-wormhole-abstraction" :ttags :all))))

;; A pretty simple proof of correctness of an application program that
;; determines whether a given input is a power of 2 or not.
(local
 (encapsulate
   ()
   (local (include-book "powOfTwo/powOfTwo" :ttags :all))))

;; The proof of correctness of a population count program was done
;; using the GL bit-blasting framework.
(local
 (encapsulate
   ()
   (local (include-book "popcount/popcount" :ttags :all))))

;; Same popcount program as popcount/popcount, but here we use our
;; lemma libraries to perform symbolic simulation.
(local
 (encapsulate
   ()
   (local (include-book "popcount/popcount-general" :ttags :all))))

(local
 (encapsulate
   ()
   (local (include-book "wordCount/wc" :ttags :all))))

;; Proof of correctness of a simple array copy sub-routine:
(local
 (encapsulate
   ()
   (local (include-book "dataCopy/dataCopy" :ttags :all))))

;; ----------------------------------------------------------------------
;; System Program:

;; The zeroCopy program has been proved correct in both the marking
;; and non-marking view of the x86 model.

(local
 (encapsulate
   ()
   (local (include-book "zeroCopy/non-marking-view/zeroCopy" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "zeroCopy/marking-view/zeroCopy" :ttags :all))))

;; ======================================================================

;; x86isa+Codewalker:

(local
 (encapsulate
   ()
   (local (include-book "codewalker-examples/factorial" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "codewalker-examples/popcount-32" :ttags :all))))

;; ======================================================================

;; The following books present small examples that Shilpi presents in
;; her PhD dissertation to illustrate how symbolic simulation is
;; controlled in all views of operation of the x86 model.

(local
 (encapsulate
   ()
   (local (include-book "dissertation-examples/clc-stc-app-view" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "dissertation-examples/clc-stc-system-level-marking-view" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "dissertation-examples/clc-stc-system-level-non-marking-view" :ttags :all))))

;; ======================================================================
