; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation

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
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

(defun get-nth-uint64 (arr n)
  (logior (aref arr (* 8 n))
          (ash (aref arr (+ (* 8 n) 1)) (* 8 1))
          (ash (aref arr (+ (* 8 n) 2)) (* 8 2))
          (ash (aref arr (+ (* 8 n) 3)) (* 8 3))
          (ash (aref arr (+ (* 8 n) 4)) (* 8 4))
          (ash (aref arr (+ (* 8 n) 5)) (* 8 5))
          (ash (aref arr (+ (* 8 n) 6)) (* 8 6))
          (ash (aref arr (+ (* 8 n) 7)) (* 8 7))))


(defun get-gprs (x86)
  (loop for i from 0 to 15
        append (let* ((val (rgfi i x86)))
                 (list (logand #xff val)
                       (logand #xff (ash val -8))
                       (logand #xff (ash val -16))
                       (logand #xff (ash val -24))
                       (logand #xff (ash val -32))
                       (logand #xff (ash val -40))
                       (logand #xff (ash val -48))
                       (logand #xff (ash val -56))))))

(defun validate-inst (x86)
  (let* ((sock (ccl::make-socket :address-family :internet
                                 :type :stream
                                 :connect :active
                                 :remote-host "localhost"
                                 :remote-port 4425))
         (response (make-array (* 18 8) :element-type '(unsigned-byte 8))))
    (read-sequence response sock)
    (close sock)
    (b* ((real-rip (get-nth-uint64 response 16))
         (real-rflags (get-nth-uint64 response 17))
         (- (format t "real-rip: ~X~&" real-rip))
         (- (format t "real-rflags: ~X~&" real-rflags))
         ((mv success? x86) (run-until-rip-or-n real-rip 30 x86))
         (- (loop for i from 0 to 15
                  do (format t "~X " (n64 (rgfi i x86)))))
         ((when (not success?)) (mv nil x86))
         (- (format t "~&"))
         (- (format t "rflags ~X~&" (rflags x86)))
         (- (format t "rip: ~X~&" (rip x86)))
         (- (format t "diffs: "))
         (- (loop for i from 0 to 15
                  do (format t "~X " (- (get-nth-uint64 response i) (n64 (rgfi i x86))))))
         (- (format t "~&")))
        (mv (and (loop for i from 0 to 15
                       always (= (get-nth-uint64 response i) (n64 (rgfi i x86))))
                 ;; Doesn't make sense to compare all bits of rflags since many
                 ;; may be undefined, but we do want to compare intf, since
                 ;; that one is always defined
                 (equal (rflagsBits->intf (rflags x86))
                        (rflagsBits->intf real-rflags)))
            x86))))
