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

;; ======================================================================
;; INSTRUCTION: RDRAND
;; ======================================================================

;; Source: http://clhs.lisp.se/Body/f_random.htm
;; random limit &optional random-state => random-number

;; Arguments and Values:
;; limit---a positive integer, or a positive float.
;; random-state---a random state. The default is the current random
;; state.
;; random-number---a non-negative number less than limit and of the
;; same type as limit.

(defun HW_RND_GEN$notinline (size x86)
  (declare (xargs :mode :program :stobjs x86)
           (type (integer 2 8) size))

  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
                   t)
            (equal (f-get-global 'in-verify-flg
                                 ACL2::*the-live-state*)
                   t))
    (return-from HW_RND_GEN$notinline
      (HW_RND_GEN-logic size x86)))
  (let ((cf
         (multiple-value-bind (cf random-state)
             (random 2)
           (declare (ignorable random-state))
           cf))
        (rand
         (multiple-value-bind (rand random-state)
             (random (expt 2 (ash size 3)))
           (declare (ignorable random-state))
           rand)))
    (mv cf rand x86)))

;; This old function below called C libraries that invoked RDRAND via
;; inline assembly.  The downside of this function was that the
;; execution of RDRAND was supported only if the host machine
;; supported RDRAND.

;; (defun HW_RND_GEN$notinline (size x86)
;;   (declare (xargs :mode :program :stobjs x86)
;;            (type (integer 2 8) size))

;;   (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
;;                    t)
;;             (equal (f-get-global 'in-verify-flg
;;                                  ACL2::*the-live-state*)
;;                    t))
;;     (return-from HW_RND_GEN$notinline
;;                  (HW_RND_GEN-logic size x86)))
;;   (let ((rand-and-cf
;;          (case size
;;            (2
;;             (multiple-value-bind (_str ptr)
;;                                  ;; Note that ptr stands in for *num.
;;                                  (ccl::make-heap-ivector 1 '(unsigned-byte 16))
;;                                  (declare (ignorable _str))
;;                                  (let* ((cf (ccl::external-call "_rdrand16"
;;                                                                 :address ptr
;;                                                                 (:unsigned 64)))
;;                                         (num (ccl::%get-unsigned-word ptr 0)))
;;                                    (ccl::dispose-heap-ivector ptr)
;;                                    (cons num cf))))
;;            (4
;;             (multiple-value-bind (_str ptr)
;;                                  ;; Note that ptr stands in for *num.
;;                                  (ccl::make-heap-ivector 1 '(unsigned-byte 32))
;;                                  (declare (ignorable _str))
;;                                  (let* ((cf (ccl::external-call "_rdrand32"
;;                                                                 :address ptr
;;                                                                 (:unsigned 64)))
;;                                         (num (ccl::%get-unsigned-long ptr 0)))
;;                                    (ccl::dispose-heap-ivector ptr)
;;                                    (cons num cf))))
;;            (8
;;             (multiple-value-bind (_str ptr)
;;                                  ;; Note that ptr stands in for *num.
;;                                  (ccl::make-heap-ivector 1 '(unsigned-byte 64))
;;                                  (declare (ignorable _str))
;;                                  (let* ((cf (ccl::external-call "_rdrand64"
;;                                                                 :address ptr
;;                                                                 (:unsigned 64)))
;;                                         (num (ccl::%%get-unsigned-longlong ptr 0)))
;;                                    (ccl::dispose-heap-ivector ptr)
;;                                    (cons num cf))))
;;            (otherwise
;;             (er hard! 'HW_RND_GEN
;;                 "Illegal size specified for HW_RND_GEN!"))
;;            )))
;;     (mv rand-and-cf x86)))

;; ======================================================================
