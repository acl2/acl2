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

(in-package "RP")

(include-book "../rp-state-functions")
(include-book "aux-function-lemmas")

(local
 (in-theory (enable rp-statep)))

(defthm rp-state-push-to-try-to-rw-stack-is-rp-statep
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 1 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                  rp-context
                                                                  rp-state))))
  :hints (("Goal"
           :in-theory (e/d (rp-state-push-to-try-to-rw-stack) ()))))

(defthm rp-statep-rp-state-push-to-result-to-rw-stack
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-push-to-result-to-rw-stack rule
                                                           index
                                                           failed
                                                           old-term
                                                           new-term
                                                           rp-state)))
  :hints (("Goal"
           :in-theory (e/d (rp-state-push-to-result-to-rw-stack) ()))))

(defthm RP-STATEP-RP-STAT-ADD-TO-RULES-USED
  (implies (rp-statep rp-state)
           (rp-statep (rp-stat-add-to-rules-used rule failed rp-state)))
  :hints (("Goal"
           :in-theory (e/d (RP-STAT-ADD-TO-RULES-USED
                            rp-statep
                            alistp
                            hons-acons) ()))))

(defthm rp-statep-rp-state-new-run
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-new-run rp-state)))
  :hints (("Goal"
           :in-theory (e/d (rp-state-new-run) ()))))

(defthm rp-statep-rp-state-push-meta-to-rw-stack
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-push-meta-to-rw-stack meta-rule old-term new-term rp-state)))
  :hints (("Goal"
           :in-theory (e/d (rp-state-push-meta-to-rw-stack) ()))))


