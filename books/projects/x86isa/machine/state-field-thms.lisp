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

(include-book "abstract-state")

;; ======================================================================

(defsection state-field-theorems

  :parents (machine)

  :short "Theorems about the fields of @('x86')"

  :long "<p>A program's behavior can be described by the effects it
has to the state of the machine.  Given an initial state, the final
state may be described as a nest of updates made in program order to
the initial state.  In order to reason about the behavior of a
program, we need to develop lemmas to read from, write to, and
re-arrange these nests of updates.</p>

<p>For the @('x86') state, we prove the following kinds of theorems
  about all its fields in terms of @(see XR) and @(see XW).</p>

<ul>

<li>@(see x86-Preservation-Theorems): There are two kinds of
  preservation theorems. The first kind states that reading a specific
  field from a valid x86 state gives us a value of a specific type;
  for example, reading the @(':RGF') gives us a value which is a
  @('(signed-byte 64)'). The second kind states that writing a
  well-formed value into a valid x86 field returns a valid x86 state;
  for example, writing a @('(signed-byte 64)') to a valid component of
  the @(':RGF') field in a well-formed x86 state gives a well-formed
  x86 state.</li>

<li>@(see x86-Writing-the-Read-Theorem): <p>Informally, this kind of a
  theorem states that a write operation that writes the same value to
  a field that was already there, is superfluous, and can be
  eliminated.</p></li>

<li>@(see x86-RoW-Theorems): <p>There are two types of Read-Over-Write
  (RoW) theorems.  The first describes the independence or
  non-interference of different components of the x86 state.  The
  second asserts that reading a component after it is modified returns
  the value that was written to it during the modification.</p></li>

<li>@(see x86-WoW-Theorems): <p>Like the RoW theorems, there are two types
  of Write-over-Write (WoW) theorems.  The first asserts that
  independent writes to the x86 state can commute safely.  The second
  asserts that if consecutive writes are made to a component, the most
  recent write is the only visible write.</p></li>

</ul>"

  )

(defconst *x86-simple-fields-as-keywords*
  '(:RIP
    :RFLAGS
    :FP-CTRL
    :FP-STATUS
    :FP-TAG
    :FP-LAST-INST
    :FP-LAST-DATA
    :FP-OPCODE
    :MXCSR
    :MS
    :FAULT
    :ENV
    :UNDEF
    :APP-VIEW
    :MARKING-VIEW
    :OS-INFO))

(defconst *x86-array-fields-as-keywords*
  '(:RGF
    :SEG-VISIBLE
    :SEG-HIDDEN
    :STR
    :SSR-VISIBLE
    :SSR-HIDDEN
    :CTR
    :DBG
    :FP-DATA
    :XMM
    :MSR
    :MEM))

(assert-event
 (and (subsetp (append *x86-simple-fields-as-keywords*
                       *x86-array-fields-as-keywords*)
               *x86-field-names-as-keywords*)
      (subsetp *x86-field-names-as-keywords*
               (append *x86-simple-fields-as-keywords*
                       *x86-array-fields-as-keywords*))))

(local
 (defthm update-nth-thm-1
   (equal (update-nth i v2 (update-nth i v1 x))
          (update-nth i v2 x))))

(local
 (defthm update-nth-thm-2
   (implies (and (integerp i1)
                 (<= 0 i1)
                 (integerp i2)
                 (<= 0 i2)
                 (not (equal i1 i2)))
            (equal (update-nth i2 v2 (update-nth i1 v1 x))
                   (update-nth i1 v1 (update-nth i2 v2 x))))))

(local
 (defthm update-nth-thm-3
   (implies (and (integerp n)
                 (<= 0 n)
                 (< n (len x86))
                 (integerp i)
                 (<= 0 i)
                 (< i (len (nth n x86))))
            (equal (update-nth n
                               (update-nth i (nth i (nth n x86))
                                           (nth n x86))
                               x86)
                   x86))))

(local
 (defthm update-nth-thm-4
   (implies (and (integerp i)
                 (<= 0 i)
                 (< i (len x86)))
            (equal (update-nth i (nth i x86) x86)
                   x86))))

(local
 (defthm update-nth-thm-5
   (implies (and (equal (nth n x) e)
                 (natp n)
                 (< n (len x)))
            (equal (update-nth n e x) x))))

(local (in-theory (e/d () (nth update-nth))))

(defsection x86-Preservation-Theorems

  :parents (state-field-theorems)

  ;; Types of readers in terms of XR:

  (defun x86-stobj-field-thms-fn-1 (x86-model-field)
    ;; E.g., (x86-stobj-field-thms-fn-1 (car *pruned-x86-model-modified-mem*))

    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.

    (b* ((name (car x86-model-field))
         (end (search "$C" (symbol-name name)))
         (name (subseq (symbol-name name) 0 end))
         (keyword (intern name "KEYWORD"))
         (type (caddr x86-model-field)))

      (cond

       ((and (consp type)
             (equal (car type) 'array)
             (consp (cadr type)))
        (b* ((predicate (mk-name name "P"))
             (namei     (mk-name name "I"))
             (constant (mk-name "*" name "I*"))
             (getter    namei)
             (size      (cadr (cadr type))))
          `(
            ;; Field type theorem:
            ,(if (equal (car (cadr type)) 'unsigned-byte)
                 `(DEFTHM-USB ,(mk-name getter (if (< size 10) "-IS-N0" "-IS-N") size "P")
                    :hyp (FORCE (X86P X86))
                    :bound ,size
                    :concl (XR ,keyword I X86)
                    :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())
                             :USE ((:INSTANCE ,(mk-name predicate "-AUX-NECC")
                                              (I I)
                                              (X (NTH ,constant X86))))))
                    :gen-linear t
                    :gen-type t)

               `(DEFTHM-SB ,(mk-name getter "-IS-I" size "P")
                  :hyp (FORCE (X86P X86))
                  :bound ,size
                  :concl (XR ,keyword I X86)
                  :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())
                           :USE ((:INSTANCE ,(mk-name predicate "-AUX-NECC")
                                            (I I)
                                            (X (NTH ,constant X86))))))
                  :gen-type t
                  :gen-linear t)))))

       ((and (consp type)
             (equal (car type) 'unsigned-byte))
        (b* ((getter  (mk-name name))
             (size    (cadr type)))
          `( ;; Field Type Theorem:
            (DEFTHM-USB ,(mk-name getter "-IS-N" size "P")
              :hyp (FORCE (X86P X86))
              :bound ,size
              :concl (XR ,keyword I X86)
              :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())))
              :gen-type t
              :gen-linear t))))

       ((and (consp type)
             (equal (car type) 'signed-byte))
        (b* ((getter  (mk-name name))
             (size    (cadr type)))
          `( ;; Field Type Theorems:
            (DEFTHM-SB ,(mk-name getter "-IS-I" size "P")
              :hyp (FORCE (X86P X86))
              :bound ,size
              :concl (XR ,keyword I X86)
              :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())))
              :gen-linear t
              :gen-type t))))

       ((and (consp type)
             (equal (car type) 'integer))
        (b* ((predicate (mk-name name "P"))
             (getter  (mk-name name))
             (size    (caddr type)))
          `( ;; Field Type Theorem:

            (DEFTHM-NATP ,(mk-name "NATP-" getter)
              :hyp (FORCE (X86P X86))
              :concl (XR ,keyword I X86)
              :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))

            (DEFTHM ,(mk-name getter "-LESS-THAN-" size)
              (IMPLIES (FORCE (X86P X86))
                       (<= (XR ,keyword I X86) ,size))
              :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
              :RULE-CLASSES :LINEAR))))

       ((and (consp type)
             (equal (car type) 'satisfies))
        ;; Env field is dealt with in this case.
        (b* ((predicate (cadr type)))
          `( ;; Field Type Theorem:
            (DEFTHM ,(mk-name predicate "-" name)
              (IMPLIES (FORCE (X86P X86))
                       (,predicate (XR ,keyword I X86)))))))

       (t
        ;; type is presumably 'T (like MS and FAULT fields)
        `(
          ;; No Field Type Theorem

          )))))

  (defun x86-stobj-field-thms-fn (x86-model)
    (cond ((endp x86-model)
           '())
          (t
           `(,@(x86-stobj-field-thms-fn-1 (car x86-model))
             ,@(x86-stobj-field-thms-fn (cdr x86-model))))))

  (make-event
   `(PROGN
     ,@(x86-stobj-field-thms-fn *pruned-x86-model-modified-mem*)))

  (defthm booleanp-app-view-type
    (implies (force (x86p x86))
             (booleanp (xr :app-view i x86)))
    :rule-classes :type-prescription)

  (defthm booleanp-marking-view-type
    (implies (force (x86p x86))
             (booleanp (xr :marking-view i x86)))
    :rule-classes :type-prescription)

  ;; Type of writers in terms of XW:

  (defthm x86p-xw
    (implies (forced-and (member fld *x86-field-names-as-keywords*)
                         (case fld
                           (:rgf          (and (integerp index)
                                               (signed-byte-p 64 value)))
                           (:rip          (signed-byte-p 48 value))
                           (:rflags       (unsigned-byte-p 32 value))
                           (:seg-visible  (and (integerp index)
                                               (unsigned-byte-p 16 value)))
                           (:seg-hidden   (and (integerp index)
                                               (unsigned-byte-p 112 value)))
                           (:str          (and (integerp index)
                                               (unsigned-byte-p 80 value)))
                           (:ssr-visible  (and (integerp index)
                                               (unsigned-byte-p 16 value)))
                           (:ssr-hidden   (and (integerp index)
                                               (unsigned-byte-p 112 value)))
                           (:ctr          (and (integerp index)
                                               (unsigned-byte-p 64 value)))
                           (:dbg          (and (integerp index)
                                               (unsigned-byte-p 64 value)))
                           (:fp-data      (and (integerp index)
                                               (unsigned-byte-p 80 value)))
                           (:fp-ctrl      (unsigned-byte-p 16 value))
                           (:fp-status    (unsigned-byte-p 16 value))
                           (:fp-tag       (unsigned-byte-p 16 value))
                           (:fp-last-inst (unsigned-byte-p 48 value))
                           (:fp-last-data (unsigned-byte-p 48 value))
                           (:fp-opcode    (unsigned-byte-p 11 value))
                           (:xmm          (and (integerp index)
                                               (unsigned-byte-p 128 value)))
                           (:mxcsr        (unsigned-byte-p 32 value))
                           (:msr          (and (integerp index)
                                               (unsigned-byte-p 64 value)))
                           (:env          (env-alistp value))
                           (:app-view (booleanp value))
                           (:marking-view (booleanp value))
                           (:os-info      (keywordp value))
                           (:mem          (and (integerp index)
                                               (unsigned-byte-p 8 value)))
                           (otherwise     (equal index 0)))
                         (x86p x86))
             (x86p (xw fld index value x86)))
    :hints (("Goal"
             :in-theory (e/d*
                         (rgfp ripp rflagsp seg-visiblep
                               seg-hiddenp strp ssr-visiblep ssr-hiddenp
                               ctrp msrp dbgp fp-datap fp-ctrlp
                               fp-statusp fp-tagp fp-last-instp
                               fp-last-datap fp-opcodep xmmp mxcsrp msrp
                               msp faultp env-alistp undefp booleanp
                               memp)
                         ()))))

  (defthmd xr-irrelevant-index-for-simple-fields
    (implies (and (syntaxp (not (and (consp index)
                                     (eq (car index) ''0))))
                  (member fld *x86-simple-fields-as-keywords*))
             (equal (xr fld index x86)
                    (xr fld 0 x86))))

  (defthmd xw-irrelevant-index-for-simple-fields
    (implies (and (syntaxp (not (and (consp index)
                                     (eq (car index) ''0))))
                  (member fld *x86-simple-fields-as-keywords*))
             (equal (xw fld index value x86)
                    (xw fld 0     value x86)))))

(defsection x86-Writing-the-Read-Theorem

  :parents (state-field-theorems)

  (defthmd xw-xr
    (implies (and (equal v (xr fld i x86))
                  (x86p x86))
             (equal (xw fld i v x86) x86))))

(defsection x86-RoW-Theorems

  :parents (state-field-theorems)

  ;; [Shilpi]: Maybe I should write a single RoW theorem with meta
  ;; rules that weeds out all the independent writes.

  (defthm xr-xw-intra-array-field
    (implies (member fld *x86-array-fields-as-keywords*)
             (equal (xr fld i (xw fld j v x86))
                    (if (equal i j)
                        v
                      (xr fld i x86)))))

  (defthm xr-xw-intra-simple-field
    (implies (member fld *x86-simple-fields-as-keywords*)
             (equal (xr fld i (xw fld j v x86))
                    v)))

  (defthm xr-xw-inter-field
    (implies (case-split (not (equal fld1 fld2)))
             (equal (xr fld2 i2 (xw fld1 i1 v x86))
                    (xr fld2 i2 x86)))))

(defsection x86-WoW-Theorems

  :parents (state-field-theorems)

  (defthm xw-xw-intra-array-field-shadow-writes
    (implies (member fld *x86-array-fields-as-keywords*)
             (equal (xw fld i v2 (xw fld i v1 x86))
                    (xw fld i v2 x86))))

  (defthm xw-xw-intra-simple-field-shadow-writes
    (implies (member fld *x86-simple-fields-as-keywords*)
             (equal (xw fld i v2 (xw fld j v1 x86))
                    (xw fld i v2 x86))))

  (defthm xw-xw-intra-field-arrange-writes
    (implies (and (member fld *x86-array-fields-as-keywords*)
                  (not (equal i1 i2)))
             (equal (xw fld i2 v2 (xw fld i1 v1 x86))
                    (xw fld i1 v1 (xw fld i2 v2 x86))))
    :rule-classes ((:rewrite :loop-stopper ((i2 i1)))))

  (defthm xw-xw-inter-field-arrange-writes
    (implies (not (equal fld1 fld2))
             (equal (xw fld2 i2 v2 (xw fld1 i1 v1 x86))
                    (xw fld1 i1 v1 (xw fld2 i2 v2 x86))))
    :rule-classes ((:rewrite :loop-stopper ((fld2 fld1))))))

;; ======================================================================

;; Globally disabling abstract stobj functions like rgfi* but letting
;; rules like rgfi be enabled:

(globally-disable '(abstract-stobj-fns-ruleset xr xw x86p))

;; ======================================================================
