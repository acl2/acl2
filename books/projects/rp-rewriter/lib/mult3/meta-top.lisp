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

(include-book "fnc-defs")

(include-book "make-sc-fgl-ready")

(include-book "medw-compress")

(include-book "unpack-booth")

(include-book "summation-tree-meta-fncs")

(include-book "equal-meta")

(include-book "adder-rules-meta")

(local
 (include-book "summation-tree-meta-fncs-correct"))

(local
 (include-book "medw-compress-correct"))

(local
 (include-book "unpack-booth-correct"))

;;(include-book "verify-guards")

;;(include-book "4vec-to-binary-fncs-meta")

;; (defthm sort-sum-meta-valid-rp-meta-rulep
;;     (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                   (mult-formula-checks state))
;;              (let ((rule (make rp-meta-rule-rec
;;                                :fnc 'sort-sum-meta
;;                                :trig-fnc 'sort-sum
;;                                :dont-rw t
;;                                :valid-syntax t)))
;;                (and (valid-rp-meta-rulep rule state)
;;                     (rp-meta-valid-syntaxp-sk rule state))))
;;     :otf-flg t
;;     :hints (("Goal"
;;              :in-theory (e/d (rp-meta-valid-syntaxp)
;;                              (rp-termp
;;                               rp-term-listp
;;                               valid-sc)))))

;; (defthm c-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 'c-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc
;;                             )))))

;; (defthm s-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 's-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm s-c-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 's-c-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm c-s-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 'c-s-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm sort-sum-meta-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 'sort-sum-meta
;;                              :trig-fnc 'sort-sum
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

#|(rp::add-meta-rules
 mult-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 's-c-spec-meta
        :trig-fnc 's-spec
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 's-c-spec-meta
        :trig-fnc 'c-spec
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 's-c-spec-meta
        :trig-fnc 's-c-spec
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 's-c-spec-meta
        :trig-fnc 'c-s-spec
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 'sort-sum-meta
        :trig-fnc 'sort-sum
        :dont-rw t
        :valid-syntax t)))||#

(rp::add-meta-rule
 :meta-fnc sort-sum-meta
 :trig-fnc sort-sum
 :valid-syntaxp t
 :formula-checks mult-formula-checks
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc s-c-spec-meta
 :trig-fnc s-spec
 :valid-syntaxp t
 :formula-checks mult-formula-checks
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc s-c-spec-meta
 :trig-fnc c-spec
 :valid-syntaxp t
 :formula-checks mult-formula-checks
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc s-c-spec-meta
 :trig-fnc s-c-spec
 :valid-syntaxp t
 :formula-checks mult-formula-checks
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc s-c-spec-meta
 :trig-fnc c-s-spec
 :valid-syntaxp t
 :formula-checks mult-formula-checks
 :returns (mv term dont-rw))

#|(rp::add-meta-rule
 :meta-fnc medw-compress-meta
 :trig-fnc medw-compress
 :valid-syntaxp t
 :formula-checks mult-formula-checks
 :returns (mv term dont-rw))||#

(rp::add-meta-rule
 :meta-fnc unpack-booth-meta
 :trig-fnc unpack-booth
 :valid-syntaxp t
 :formula-checks mult-formula-checks
 :returns (mv term dont-rw))

(add-postprocessor
 :processor-fnc medw-compress-any
 :valid-syntaxp t
 :formula-checks mult-formula-checks)
