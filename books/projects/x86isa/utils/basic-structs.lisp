; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2018, Shilpi Goel
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
; Shilpi Goel         <shigoel@gmail.com>

(in-package "X86ISA")
(include-book "centaur/fty/bitstruct" :dir :system)

(local (xdoc::set-default-parents structures))

;; Bitstruct field widths:

(defbitstruct  2bits  2)
(defbitstruct  3bits  3)
(defbitstruct  4bits  4)
(defbitstruct  5bits  5)
(defbitstruct  6bits  6)
(defbitstruct  7bits  7)
(defbitstruct  8bits  8)
(defbitstruct 10bits 10)
(defbitstruct 11bits 11)
(defbitstruct 12bits 12)
(defbitstruct 13bits 13)
(defbitstruct 16bits 16)
(defbitstruct 17bits 17)
(defbitstruct 19bits 19)
(defbitstruct 22bits 22)
(defbitstruct 24bits 24)
(defbitstruct 31bits 31)
(defbitstruct 32bits 32)
(defbitstruct 40bits 40)
(defbitstruct 54bits 54)
(defbitstruct 64bits 64)
