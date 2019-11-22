; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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
; Mertcan Temel         <mert@utexas.edu>


;; Some helper lemmas instead of definitions of basic functions
;; There's no well-developed heuristic developed for :definition rules.
;; they may be rewritten freely on any condition, so instead we don't allow
;; them but use rewrite rules instead.

(in-package "RP")

(include-book "../aux-functions")

(def-rp-rule len-cons
  (equal (len (cons a b))
         (+ 1 (len b))))

(def-rp-rule atom-cons
  (equal (atom (cons a b))
         nil))

(def-rp-rule consp-cons
  (consp (cons a b)))

(def-rp-rule equal-to-t
  (equal (equal a a)
         't))

(def-rp-rule boolean-listp-is-booleanp
  (booleanp (boolean-listp a))
  :hints (("goal"
           :in-theory (enable boolean-listp))))



;; add definitions from minimal theory.
(add-rp-rule car-cons)
(add-rp-rule cdr-cons)
(add-rp-rule return-last)
(add-rp-rule mv-nth)
(add-rp-rule the-check)
(add-rp-rule CONS-WITH-HINT)
(add-rp-rule IFF)
(add-rp-rule WORMHOLE-EVAL)
(add-rp-rule MV-LIST)
(add-rp-rule MINUSP)
(add-rp-rule PLUSP)
(add-rp-rule ZEROP)
(add-rp-rule LISTP)
(add-rp-rule SYNP)
(add-rp-rule CASE-SPLIT)
(add-rp-rule FORCE)
(add-rp-rule /=)
(add-rp-rule =)
(add-rp-rule atom)
(add-rp-rule null)
(add-rp-rule endp)
(add-rp-rule eql)
(add-rp-rule not)
(add-rp-rule implies)
(add-rp-rule eq)
(add-rp-rule eql)
(add-rp-rule cons-equal)
