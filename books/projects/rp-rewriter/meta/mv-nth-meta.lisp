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

(include-book "../meta-rule-macros")

(defun mv-nth-meta-aux (index term)
  (declare (xargs :guard (natp index)))
  (case-match term
    (('cons first rest)
     (if (zp index)
         (mv first t)
       (mv-nth-meta-aux (1- index)
                        rest)))
    (& (mv term index))))

(defun mv-nth-meta (term)
  (declare (xargs :guard t))
  (case-match term
    (('mv-nth ('quote index) x)
     (if (natp index)
         (b* (((mv res res-ok)
               (mv-nth-meta-aux index x)))
           (if (equal res-ok t)
               (mv res t)
             (mv `(mv-nth ',res-ok ,res )
                 `(nil t t))))
       (mv term `(nil t t))))
    (('mv-nth & &)
     (mv term `(nil t t)))
    (& (mv term nil))))

(rp::def-formula-checks-default-evl
 rp::rp-evl
 (strip-cars rp::*small-evl-fncs*))

(rp::def-formula-checks mv-nth-formula-checks
                        (mv-nth
                         cons
                         mv-nth-meta))

(defthm rp-evl-of-mv-nth-meta
  (implies (and (rp-evl-meta-extract-global-facts)
                (mv-nth-formula-checks state))
           (equal (rp-evlt (mv-nth 0 (mv-nth-meta term)) a)
                  (rp-evlt term a)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (mv-nth) ()))))

(defthm rp-termp-of-mv-nth-meta
  (implies (rp::rp-termp term)
           (rp::rp-termp (mv-nth 0 (mv-nth-meta term))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (mv-nth) ()))))





(defthm valid-sc-of-mv-nth-meta
  (implies (rp::valid-sc term a)
           (rp::valid-sc (mv-nth 0 (mv-nth-meta term)) a))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::is-if
                            rp::is-rp) ()))))

(defthm dont-rw-syntaxp-mv-nth-meta
  (implies t
           (rp::dont-rw-syntaxp (mv-nth 0 (mv-nth-meta term))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::is-if
                            rp::is-rp) ()))))

(defthm valid-rp-meta-rulep-mv-nth-meta
  (implies (and (rp-evl-meta-extract-global-facts)
                (mv-nth-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'mv-nth-meta
                             :trig-fnc 'mv-nth
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                           (rp::RP-TERMP
                            mv-nth-meta
                            rp::VALID-SC)))))

(rp::add-meta-rules mv-nth-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc 'mv-nth-meta
                                :trig-fnc 'mv-nth
                                :dont-rw t
                                :valid-syntax t)))
