; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Shilpi Goel
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

;; ----------------------------------------------------------------------

; Some misc. functions used throughout the formal model:

(local (include-book "arithmetic/top-with-meta" :dir :system))

; Measure for log-2 below.
(defun log-2-measure (x)
  (cond ((or (not (natp x))
             (<= x 1))
         0)
        (t (floor x 1))))

; On powers of 2, this function is a base 2 logarithm:
; it maps 2^n to n+count -- count is the accumulator.
(defun log-2 (x count)
  (declare (xargs :measure (log-2-measure x)
                  :guard (natp count)))
  (if (natp x)
      (if (<= x 1)
          count
        (log-2 (* 1/2 x) (1+ count)))
    count))

; This function returns the list
; (start (+ by start) (+ (* 2 by) start) ... (+ (* (1- count) by) start)).
(defun increasing-list (start by count)
  (declare (xargs :guard (and (natp start)
                              (natp by)
                              (natp count))))
  (if (zp count)
      nil
    (cons start
          (increasing-list (+ by start) by (1- count)))))

; Maximum of a list of numbers (NIL if the list is empty).
(defun max-list (l)
  (if (or (endp l)
          (equal (len l) 1))
      (car l)
    (max (car l) (max-list (cdr l)))))

;; ----------------------------------------------------------------------
