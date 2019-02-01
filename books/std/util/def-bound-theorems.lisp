; Standard Utilities Library -- Prove Bound Theorems

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
; Matt Kaufmann       <kaufmann@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STD")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defthm-natp
  :parents (std/util)
  :short "Prove rules about a term yielding values in @(tsee natp)."
  :long
  "<p>
   Use the macro @('defthm-natp') to prove
   a @('rewrite') rule saying that
   some term yields a @('natp'),
   a @('type-prescription') corollary saying that
   the term yields a @('natp'),
   and a @('linear') corollary saying that
   the term yields a value greater than or equal to zero.
   </p>
   <p>
   Usage:
   </p>
   @({
     (defthm-natp <theorem-name>
       :hyp <hypotheses>
       :concl <conclusion>
       :hints <usual ACL2 hints for the main theorem>)
       :gen-type <t or nil>    ;; Generate :type-prescription corollary
       :gen-linear <t or nil>  ;; Generate :linear corollary
       :hyp-t <hypotheses for the :type-prescription corollary>
       :hyp-l <hypotheses for the :linear corollary>
       :hints-t <usual ACL2 hints for the :type-prescription corollary>
       :hints-l <usual ACL2 hints for the :linear corollary>
       :otf-flg <t or nil>)
     })
   <p>
   The above form produces a theorem of the form
   (if both @(':gen-type') and @(':gen-linear') are @('t')):
   </p>
   @({
     (defthm <theorem-name>
       (implies <hypotheses>
                (natp <conclusion>))
       :hints <usual ACL2 hints>
       :otf-flg <t or nil>
       :rule-classes
       (:rewrite
        (:type-prescription
         :corollary
         (implies <hypotheses>
                  (natp <conclusion>))
         :hints <usual ACL2 hints for the :type-prescription corollary>)
        (:linear
         :corollary
         (implies <hypotheses>
                  (<= 0 <conclusion>))
         :hints <usual ACL2 hints for the :linear corollary>)))
     })
   <p>
   If @(':hints-t') is not supplied,
   hints to prove the type prescription corollary are generated automatically.
   In this case, the hypotheses for the type prescription corollary
   must trivially subsume the ones for the main theorem specified by @(':hyp');
   in particular, they may have additional conjuncts
   or additional calls to @(tsee force).
   Analogous remarks apply to @(':hints-l').
   </p>
   <p>
   Also see the related macros
   @(tsee defthm-unsigned-byte-p) and @(tsee defthm-signed-byte-p).
   </p>")

(defmacro defthm-natp (name &key
                            (hyp 't)
                            concl
                            gen-type
                            gen-linear
                            hints
                            hyp-t
                            hyp-l
                            hints-t
                            hints-l
                            otf-flg)
  (if concl
      (let ((hyp-t (or hyp-t hyp))
            (hyp-l (or hyp-l hyp))
            (hints-t (or hints-t
                         '(("Goal" :in-theory nil))))
            (hints-l (or hints-l
                         '(("Goal" :in-theory '(natp))))))
        `(defthm ,name
           ,(if (eq hyp t)
                `(natp ,concl)
              `(implies ,hyp
                        (natp ,concl)))
           ,@(and hints `(:hints ,hints))
           ,@(and otf-flg `(:otf-flg t))
           :rule-classes
           (:rewrite
            ,@(and gen-type
                   `((:type-prescription
                      :corollary
                      ,(if (eq hyp-t t)
                           `(natp ,concl)
                         `(implies ,hyp-t (natp ,concl)))
                      ;; If :HINTS-T is not supplied, the following hints,
                      ;; given that this corollary is identical to the main
                      ;; theorem, should suffice to prove the corollary from
                      ;; the main theorem, assuming that :HYP-T is a superset
                      ;; of :HYP, or perhaps has some extra calls to FORCE.
                      :hints ,hints-t)))
            ,@(and gen-linear
                   `((:linear
                      :corollary
                      ,(if (eq hyp-l t)
                           `(<= 0 ,concl)
                         `(implies ,hyp-l (<= 0 ,concl)))
                      ;; If :HINTS-L is not supplied, the following hints,
                      ;; given the definition of NATP, should suffice to prove
                      ;; the corollary from the main theorem, assuming that
                      ;; :HYP-T is a superset of :HYP, or perhaps has some
                      ;; extra calls to FORCE.
                      :hints ,hints-l))))))
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defthm-unsigned-byte-p
  :parents (std/util)
  :short "Prove rules about a term yielding values in @(tsee unsigned-byte-p)."
  :long
  "<p>
   Use the macro @('defthm-unsigned-byte-p') to prove
   a @('rewrite') rule saying that
   some term yields an @('unsigned-byte-p'),
   a @('type-prescription') corollary saying that
   the term yields a @('natp'),
   and a @('linear') corollary saying that
   the term yields a value greater than or equal to 0
   and less than <tt>(expt 2 bound)</tt>.
   </p>
   <p>
   Usage:
   </p>
   @({
     (defthm-unsigned-byte-p <theorem-name>
       :hyp <hypotheses>
       :bound <n>
       :concl <conclusion>
       :hints <usual ACL2 hints for the main theorem>
       :gen-type <t or nil>    ;; Generate :type-prescription corollary
       :gen-linear <t or nil>  ;; Generate :linear corollary
       :hyp-t <hypotheses for the :type-prescription corollary>
       :hyp-l <hypotheses for the :linear corollary>
       :hints-t <usual ACL2 hints for the :type-prescription corollary>
       :hints-l <usual ACL2 hints for the :linear corollary>
       :otf-flg <t or nil>)
     })
   <p>
   The above form produces a theorem of the following form
   (if both @(':gen-type') and @(':gen-linear') are @('t')):
   </p>
   @({
     (defthm <theorem-name>
       (implies <hypotheses>
                (unsigned-byte-p <n> <conclusion>))
       :hints <usual ACL2 hints for the main theorem>
       :otf-flg <t or nil>
       :rule-classes
       (:rewrite
        (:type-prescription
         :corollary
         (implies <hypotheses for the :type-prescription corollary>
                  (natp <conclusion>))
         :hints <usual ACL2 hints for the :type-prescription corollary>)
        (:linear
         :corollary
         (implies <hypotheses for the :linear corollary>
                  (and (<= 0 <conclusion>)
                       (< <conclusion> (expt 2 <n>))))
         :hints <usual ACL2 hints for the :linear corollary>)))
     })
   <p>
   If @(':hints-t') is not supplied,
   hints to prove the type prescription corollary are generated automatically.
   In this case, the hypotheses for the type prescription corollary
   must trivially subsume the ones for the main theorem specified by @(':hyp');
   in particular, they may have additional conjuncts
   or additional calls to @(tsee force).
   Analogous remarks apply to @(':hints-l').
   </p>
   <p>
   Also see the related macros
   @(tsee defthm-natp) and @(tsee defthm-signed-byte-p).
   </p>")

(defmacro defthm-unsigned-byte-p (name &key
                                       (hyp 't)
                                       bound
                                       concl
                                       gen-type
                                       gen-linear
                                       hyp-t
                                       hyp-l
                                       hints
                                       hints-t
                                       hints-l
                                       otf-flg)
  (if (and concl bound)
      (let ((hyp-t (or hyp-t hyp))
            (hyp-l (or hyp-l hyp))
            (hints-t (or hints-t
                         ;; If :HINTS-T is not supplied, the following hints,
                         ;; given the definitions of UNSIGNED-BYTE-P,
                         ;; INTEGER-RANGE-P, and NATP, should suffice to prove
                         ;; the corollary from the main theorem, assuming that
                         ;; :HYP-T is a superset of :HYP, or perhaps has some
                         ;; extra calls to FORCE.
                         '(("Goal" :in-theory '(unsigned-byte-p
                                                integer-range-p
                                                natp)))))
            (hints-l (or hints-l
                         ;; If :HINTS-L is not supplied, the following hints,
                         ;; given the definitions of UNSIGNED-BYTE-P and
                         ;; INTEGER-RANGE-P, should suffice to prove the
                         ;; corollary from the main theorem, assuming that
                         ;; :HYP-L is a superset of :HYP, or perhaps has some
                         ;; extra calls to FORCE. The (:E EXPT) is motivated by
                         ;; the fact that, if :BOUND is a number, the generated
                         ;; linear rule involves not a call of EXPT but
                         ;; directly the value of such a call (see 2^BOUND
                         ;; below).
                         '(("Goal" :in-theory '(unsigned-byte-p
                                                integer-range-p
                                                (:e expt))))))
            (2^bound (if (natp bound)
                         (expt 2 bound)
                       `(expt 2 ,bound))))
        `(defthm ,name
           ,(if (eq hyp t)
                `(unsigned-byte-p ,bound ,concl)
              `(implies ,hyp
                        (unsigned-byte-p ,bound ,concl)))
           ,@(and hints `(:hints ,hints))
           ,@(and otf-flg `(:otf-flg t))
           :rule-classes
           (:rewrite
            ,@(and gen-type
                   `((:type-prescription
                      :corollary
                      ,(if (eq hyp-t t)
                           `(natp ,concl)
                         `(implies ,hyp-t
                                   (natp ,concl)))
                      :hints ,hints-t)))
            ,@(and gen-linear
                   `((:linear
                      :corollary
                      ,(if (eq hyp-l t)
                           `(and
                             (<= 0 ,concl)
                             (< ,concl ,2^bound))
                         `(implies ,hyp-l
                                   (and
                                    (<= 0 ,concl)
                                    (< ,concl ,2^bound))))
                      :hints ,hints-l))))))
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defthm-signed-byte-p
  :parents (std/util)
  :short "Prove rules about a term yielding values in @(tsee signed-byte-p)."
  :long
  "<p>
   Use the macro @('defthm-signed-byte-p') to prove
   a @('rewrite') rule saying that
   some term yields a @('signed-byte-p'),
   a @('type-prescription') corollary saying that
   the term yields an @('integerp'),
   and a @('linear') corollary saying that
   the term yields a value
   greater than or equal to <tt>(- (expt 2 (1- bound)))</tt> and
   less than <tt>(expt 2 (1- bound))</tt>.
   </p>
   <p>
   Usage:
   </p>
   @({
     (defthm-signed-byte-p <theorem-name>
       :hyp <hypotheses>
       :bound <n>
       :concl <conclusion>
       :hints <usual ACL2 hints for the main theorem>
       :gen-type <t or nil>    ;; Generate :type-prescription corollary
       :gen-linear <t or nil>  ;; Generate :linear corollary
       :hyp-t <hypotheses for the :type-prescription corollary>
       :hyp-l <hypotheses for the :linear corollary>
       :hints-t <usual ACL2 hints for the :type-prescription corollary>
       :hints-l <usual ACL2 hints for the :linear corollary>
       :otf-flg <t or nil>)
     })
   <p>
   The above form produces a theorem of the form
   (if both @(':gen-type') and @(':gen-linear') are @('t')):
   </p>
   @({
     (defthm <theorem-name>
       (implies <hypotheses>
                (signed-byte-p <n> <conclusion>))
       :hints <usual ACL2 hints for the main theorem>
       :otf-flg <t or nil>
       :rule-classes
       (:rewrite
        (:type-prescription
         :corollary
         (implies <hypotheses for the :type-prescription corollary>
                  (integerp <conclusion>))
         :hints <usual ACL2 hints for the :type-prescription corollary>)
        (:linear
         :corollary
         (implies <hypotheses for the :linear corollary>
                  (and (<= (- (expt 2 (1- <n>)) <conclusion>))
                       (< <conclusion> (expt 2 (1- <n>)))))
         :hints <usual ACL2 hints for the :linear corollary>)))
     })
   <p>
   If @(':hints-t') is not supplied,
   hints to prove the type prescription corollary are generated automatically.
   In this case, the hypotheses for the type prescription corollary
   must trivially subsume the ones for the main theorem specified by @(':hyp');
   in particular, they may have additional conjuncts
   or additional calls to @(tsee force).
   Analogous remarks apply to @(':hints-l').
   </p>
   <p>
   Also see the related macros
   @(tsee defthm-natp) and @(tsee defthm-unsigned-byte-p).
   </p>")

(defmacro defthm-signed-byte-p (name &key
                                     (hyp 't)
                                     bound
                                     concl
                                     gen-type
                                     gen-linear
                                     hyp-t
                                     hyp-l
                                     hints
                                     hints-t
                                     hints-l
                                     otf-flg)
  (if (and concl bound)
      (let* ((hyp-t (or hyp-t hyp))
             (hyp-l (or hyp-l hyp))
             (hints-t (or hints-t
                          ;; If :HINTS-T is not supplied, the following hints,
                          ;; given the definitions of SIGNED-BYTE-P and
                          ;; INTEGER-RANGE-P, should suffice to prove the
                          ;; corollary from the main theorem, assuming that
                          ;; :HYP-T is a superset of :HYP, or perhaps has some
                          ;; extra calls to FORCE.
                          '(("Goal" :in-theory '(signed-byte-p
                                                 integer-range-p)))))
             (hints-l (or hints-l
                          ;; If :HINTS-L is not supplied, the following hints,
                          ;; given the definitions of UNSIGNED-BYTE-P and
                          ;; INTEGER-RANGE-P, should suffice to prove the
                          ;; corollary from the main theorem, assuming that
                          ;; :HYP-L is a superset of :HYP, or perhaps has some
                          ;; extra calls to FORCE. The (:E EXPT) is motivated
                          ;; by the fact that, if :BOUND is a number, the
                          ;; generated linear rule involves not calls of EXPT
                          ;; but directly the value of such calls (see
                          ;; 2^BOUND-1 and LOW-2^BOUND-1 below).
                          '(("Goal" :in-theory '(signed-byte-p
                                                 integer-range-p
                                                 (:e expt))))))
             (2^bound-1 (if (natp bound)
                            (expt 2 (1- bound))
                          `(expt 2 (1- ,bound))))
             (low-2^bound-1 (if (natp bound)
                                (- 2^bound-1)
                              `(- (expt 2 (1- ,bound))))))
        `(defthm ,name
           ,(if (eq hyp t)
                `(signed-byte-p ,bound ,concl)
              `(implies ,hyp
                        (signed-byte-p ,bound ,concl)))
           ,@(and hints `(:hints ,hints))
           ,@(and otf-flg `(:otf-flg t))
           :rule-classes
           (:rewrite
            ,@(and gen-type
                   `((:type-prescription
                      :corollary
                      ,(if (eq hyp-t t)
                           `(integerp ,concl)
                         `(implies ,hyp-t
                                   (integerp ,concl)))
                      :hints ,hints-t)))
            ,@(and gen-linear
                   `((:linear
                      :corollary
                      ,(if (eq hyp-l t)
                           `(and
                             (<= ,low-2^bound-1 ,concl)
                             (< ,concl ,2^bound-1))
                         `(implies ,hyp-l
                                   (and
                                    (<= ,low-2^bound-1 ,concl)
                                    (< ,concl ,2^bound-1))))
                      :hints ,hints-l))))))
    nil))
