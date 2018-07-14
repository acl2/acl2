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

;; ======================================================================

(in-package "X86ISA")
(include-book "row-wow-thms" :ttags :all :dir :proof-utils)

;; ======================================================================

(defthm nthcdr-true-listp
  (implies (true-listp xs)
           (true-listp (nthcdr n xs)))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
 ()

 (local
  (include-book "std/lists/take" :dir :system))

 (defthm take-true-listp
   (implies (true-listp xs)
            (true-listp (take n xs)))
   :rule-classes (:rewrite :type-prescription))

 )

(defthm nthcdr-of-bytes-of-obj-non-empty
  (implies (and (< 0 (len bytes-of-obj))
                (< obj-offset bytes-of-obj))
           (and (nthcdr obj-offset bytes-of-obj)
                (< 0 (len (nthcdr obj-offset bytes-of-obj))))))

(in-theory (e/d () (take nthcdr)))

;; ======================================================================

;; File descriptor and contents fields:

(defthm file-descriptor-fieldp-implies-natp-offset
  (implies (file-descriptor-fieldp x)
           (natp (cdr (assoc-equal :offset x))))
  :rule-classes (:type-prescription :forward-chaining))

(defthm file-contents-fieldp-implies-stringp-contents
  (implies (file-contents-fieldp x)
           (stringp (cdr (assoc-equal :contents x))))
  :rule-classes (:type-prescription :forward-chaining))

(defthm file-descriptor-fieldp-preserved
  (implies (file-descriptor-fieldp ss)
           (file-descriptor-fieldp (put-assoc-equal
                                    :offset
                                    (+ 1 (cdr (assoc-equal :offset ss)))
                                    ss))))

(in-theory (e/d ()
                (file-descriptor-fieldp
                 file-contents-fieldp)))

;; ======================================================================
