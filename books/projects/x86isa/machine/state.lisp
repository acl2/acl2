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
; Matt Kaufmann       <kaufmann@cs.utexas.edu>
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
; Robert Krug         <rkrug@cs.utexas.edu>
; Updated by Shilpi Goel <shilpi@centtech.com> in June, 2021 to use
; the bigmem and defrstobj books.

(in-package "X86ISA")

(include-book "utilities" :dir :utils)
(include-book "structures" :dir :utils)
(include-book "centaur/defrstobj2/defrstobj" :dir :system)
(include-book "centaur/bigmem/bigmem" :dir :system)
(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "std/strings/pretty" :dir :system)

; cert_param: (non-lispworks)

;; Matt Kaufmann discovered that LispWorks complained about making an
;; array whose length is more than twice the legal limit.  Here's the
;; exact error (from an email Matt sent to Shilpi):

;;   HARD ACL2 ERROR in ACL2::MAKE-ARRAY$:  The dimensions of an array must
;;   obey restrictions of the underlying Common Lisp:  each must be a non-
;;   negative integer less than the value of array-dimension-limit (here,
;;   536870911) and their product must be less than the value of array-
;;   total-size-limit (here, 536870911).  The call
;;   '(ACL2::MAKE-ARRAY$ 1342177280
;;                       :ELEMENT-TYPE '(UNSIGNED-BYTE 8)
;;                       :INITIAL-ELEMENT '0),
;;   which has dimensions 1342177280, is thus illegal.

;; Since other Lisps do not complain about the large array length, we
;; choose not to support LispWorks at this point.

;; ----------------------------------------------------------------------

(defsection machine
  :parents (x86isa)
  :short "Core elements of the x86 ISA, like the @('x86') state,
   decoder function, etc., and proofs about the x86 ISA
   specification.")

(local (xdoc::set-default-parents x86isa-state))

;; ----------------------------------------------------------------------
;; x86 state
;; ----------------------------------------------------------------------

(defsection environment-field

  :parents (x86isa-state)

  :short "An environment field that includes a simple model of the
  file system and an oracle"

  :long "<p>The environment allows reasoning about non-deterministic
  events and computations in the ISA, like the @('RDRAND') instruction
  and in the user-level mode, the @('SYSCALL') instruction.</p>"

  (define rip-ret-alistp (lst)
    :short "Recognizer for the @('oracle') sub-field of the environment
    field @('env')"
    :long "<p>A valid @('rip-ret-alistp') associates canonical linear
    addresses, i.e., 48-bit integers in our specification, to a list
    of arbitrary values.  For example, <tt>'((1 . ((-1 . 12) 5000)) (2
    . (0)))</tt> means that if the oracle in the environment field is
    consulted at address <tt>1</tt>, <tt>'(-1 . 12)</tt> will be
    popped out.  If the oracle is consulted again at the address
    <tt>1</tt>, then <tt>5000</tt> will be popped out.</p>"
    :parents (environment-field)
    (if (atom lst)
        (equal lst nil)
      (and (consp (car lst))
           (i48p (caar lst))
           (true-listp (cdar lst))
           (rip-ret-alistp (cdr lst))))
    ///

    (defthm rip-ret-alistp-fwd-chaining-alistp
      (implies (rip-ret-alistp x)
               (alistp x))
      :rule-classes :forward-chaining))

  (define env-alistp (env)
    :short "Recognizer of the environment field @('env')"
    :long "<p>As of now, @('env-alistp') consists of three sub-fields,
    all of which are basically alists --- file descriptors, file
    contents, and an oracle field.</p>"
    :parents (environment-field)
    (or (equal env nil)
        (and (alistp env)
             (equal (len env) 3)
             (consp (assoc :FILE-DESCRIPTORS env))
             (alistp (cdr (assoc :FILE-DESCRIPTORS env)))
             (consp (assoc :FILE-CONTENTS env))
             (alistp (cdr (assoc :FILE-CONTENTS env)))
             (consp (assoc :ORACLE env))
             (rip-ret-alistp (cdr (assoc :ORACLE env)))))

    ///

    (defun env-alist-fix (x)
      (declare (xargs :guard (env-alistp x)))
      (mbe :logic (if (env-alistp x) x nil)
           :exec x))

    (defthm env-alistp-fwd-chaining-alistp
      (implies (env-alistp x)
               (alistp x))
      :rule-classes :forward-chaining)

    (defrulel nth-and-assoc-equal-check
      (implies (and (alistp x)
                    (not (equal (car (nth 0 x)) :oracle))
                    (equal (car (nth 1 x)) :oracle))
               (equal (nth 1 x)
                      (assoc-equal :oracle x))))

    (defthm env-alistp-implies-rip-ret-alistp
      (implies (env-alistp x)
               (rip-ret-alistp (cdr (assoc-equal :oracle x))))
      :rule-classes (:rewrite :forward-chaining))

    (defthm env-alistp-implies-alistp-file-descriptors
      (implies (env-alistp x)
               (alistp (cdr (assoc-equal :file-descriptors x))))
      :rule-classes (:rewrite :forward-chaining))

    (defthm env-alistp-implies-alistp-file-contents
      (implies (env-alistp x)
               (alistp (cdr (assoc-equal :file-contents x))))
      :rule-classes (:rewrite :forward-chaining))))

(defn os-info-fix (x)
  (if (keywordp x) x :linux))

(defconst *x86isa-state*
  `(
    ;; --------------------------------------------------
    (:doc "<h5>Fields that govern the model's operation</h5>

    <p>These fields are an artifact of our x86 ISA model.</p>

    <ul>")

    (:doc "<li>@('MS'): Model state, used to indicate I/O or errors
    that our model does not handle yet.  Basically, we use the model
    state to assert partial correctness.  If the model state is nil
    till the end of execution, we expect the results to be correct.
    Otherwise, all bets are off.<br/>")
    (ms :type t :initially nil)
    (:doc "</li>")

    (:doc "<li>@('FAULT'): We need some way to pass exceptions and
    such around.  So we stuff them into the @('fault') slot, to be
    processed by the step function.<br/>")
    (fault :type t :initially nil)
    (:doc "</li>")

    (:doc "<li>@('ENV'): Environment for the programs running on our
    x86 model.<br/>")
    (env :type (satisfies env-alistp)
         :fix (ec-call (env-alist-fix x))
         :initially nil)
    (:doc "</li>")

    (:doc "<li>@('UNDEF'): Field that seeds unknown values that
    characterize commonly occurring undefined behavior.<br/>")
    (undef :type t :initially 0)
    (:doc "</li>")

    (:doc "<li>@('APP-VIEW'): This field acts as a switch.  When its
    value is @('t'), support for system features like paging is
    absent.  When its value is @('nil'), the model is in @('sys-view')
    and support for system features is present.<br/>")
    (app-view :type (satisfies booleanp)
              :fix (acl2::bool-fix x)
              :initially t)
    (:doc "</li>")

    (:doc "<li>@('MARKING-VIEW'): This field also acts as a
    switch. When its value is @('t'), then accessed and dirty bits in
    the paging structures are set during those data structure
    traversals, as expected. Otherwise, these bits are not set. This
    switch is meaningful only in when the model is in @('sys-view').<br/>")
    (marking-view :type (satisfies booleanp)
                  :fix (acl2::bool-fix x)
                  :initially t)
    (:doc "</li>")

    (:doc "<li>@('OS-INFO'): This field is meaningful only in
    @('app-view') mode to model system call behavior.<br/>")
    (os-info :type (satisfies keywordp)
             :fix (ec-call (os-info-fix x))
             :initially :linux)
    (:doc "</li>")

    (:doc "</ul>")

    ;; --------------------------------------------------

    (:doc "<h5>Components of the x86 state specified by this model</h5>

     <ul>")

    (:doc
     "<li>@('RGF'): The general-purpose registers are just an array of
     signed 64-bit integers.  Note that we choose to define the GPRs
     as signed integers for the sake of efficiency.  For instance,
     @('-1') in unsigned format would occupy 64 bits, a bignum.  But
     in the signed format, it would be a fixum.  See Intel Volume 1,
     Section 3.4.1 (General-Purpose Registers) for information about
     these registers.<br/>")
    (rgf :type (array (signed-byte 64)
                      (,*64-bit-general-purpose-registers-len*))
         :initially 0
         :fix (acl2::logext 64 (ifix x))
         :resizable nil
         :accessor rgfi
         :updater !rgfi)
    (:doc "</li>")

    (:doc "<li>@('RIP'): We choose the RIP to be a 48-bit signed
    integer.  RIP can contain only canonical addresses, which range
    from 0 to 2^47-1 and 2^64-2^47 to 2^64-1, inclusive, for the
    64-bit mode.  So, in our model, 0 to 2^47-1 represents the lower
    range of canonical addresses and -2^47 to -1 represents the upper
    range of canonical addresses.  See Intel manual, Jan'19, Volume 1,
    Section 3.5 for details about the instruction pointer.<br/>")
    (rip :type (signed-byte 48)
         :initially 0
         :fix (acl2::logext 48 (ifix x)))
    (:doc "</li>")

    (:doc "<li>@('RFLAGS'): We define the @('rflags') register as a
    32-bit field, even though in the 64-bit mode, rflags is a 64-bit
    register --- this is justified because Intel says that the top 32
    bits of rflags are reserved. See Intel manual, Jan'19A, Volume 1,
    Section 3.4.3 for details about @('rflags').<br/>")
    (rflags :type (unsigned-byte 32)
            ;; Bit 1 is always 1.
            :initially 2
            :fix (acl2::loghead 32 (ifix x)))
    (:doc "</li>")

    (:doc "<li>@('User Segment Registers'):
    <p>Visible portion:
    @({ 16-bit selector INDEX(13)::TI(1)::RPL(2) })</p>
    <p>Hidden/Cache portion (see Intel manual, Mar'17, Vol. 3A, Figure 3-7):
    @({ 16-bit Attributes
        32-bit Limit
        64-bit Base Address})</p>
    <p>See Intel manual, Jan'19, Volume 1, Section 3.4.2 and Intel
    manual, Jan'19, Volume 3, Sections 3.4.2 and 3.4.3 for
    details.</p><br/>")
    (seg-visible :type (array (unsigned-byte 16)
                              (#.*segment-register-names-len*))
                 :initially 0
                 :fix (acl2::loghead 16 (ifix x))
                 :resizable nil
                 :accessor seg-visiblei
                 :updater !seg-visiblei)
    (seg-hidden-base :type (array (unsigned-byte 64)
                                  (#.*segment-register-names-len*))
                     :fix (acl2::loghead 64 (ifix x))
                     :initially 0
                     :resizable nil
                     :accessor seg-hidden-basei
                     :updater !seg-hidden-basei)
    (seg-hidden-limit :type (array (unsigned-byte 32)
                                   (#.*segment-register-names-len*))
                      :fix (acl2::loghead 32 (ifix x))
                      :initially 0
                      :resizable nil
                      :accessor seg-hidden-limiti
                      :updater !seg-hidden-limiti)
    (seg-hidden-attr :type (array (unsigned-byte 16)
                                  (#.*segment-register-names-len*))
                     :fix (acl2::loghead 16 (ifix x))
                     :initially 0
                     :resizable nil
                     :accessor seg-hidden-attri
                     :updater !seg-hidden-attri)
    (:doc "</li>")

    (:doc "<li>@('System Table Registers (GDTR and IDTR)'): These
    registers point to bounded tables of (up to 8192) segment
    descriptors.  In 64-bit mode, the system table registers are
    extended from 48 to 80 bits.  See Intel manual, Jan'19, Volume 3,
    Figure 2-6.<br/>")
    (str :type (array (unsigned-byte 80)
                      (#.*gdtr-idtr-names-len*))
         :fix (acl2::loghead 80 (ifix x))
         :initially 0
         :resizable nil
         :accessor stri
         :updater !stri)
    (:doc "</li>")

    (:doc "<li>@('System Segment Registers (Task Register and LDTR)'):
     <p>Visible portion:
    @({ 16-bit selector INDEX(13)::TI(1)::RPL(2) })</p>
    <p>Hidden/Cache portion:
    @({ 16-bit Attributes
        32-bit Limit
        64-bit Base Address })</p>
    <p>See Intel manual, Jan'19, Volume 3, Figure 2-6 for details.</p><br/>")
    (ssr-visible :type (array (unsigned-byte 16)
                              (#.*ldtr-tr-names-len*))
                 :initially 0
                 :fix (acl2::loghead 16 (ifix x))
                 :resizable nil
                 :accessor ssr-visiblei
                 :updater !ssr-visiblei)
    (ssr-hidden-base :type (array (unsigned-byte 64)
                                  (#.*ldtr-tr-names-len*))
                     :initially 0
                     :fix (acl2::loghead 64 (ifix x))
                     :resizable nil
                     :accessor ssr-hidden-basei
                     :updater !ssr-hidden-basei)
    (ssr-hidden-limit :type (array (unsigned-byte 32)
                                   (#.*ldtr-tr-names-len*))
                      :initially 0
                      :fix (acl2::loghead 32 (ifix x))
                      :resizable nil
                      :accessor ssr-hidden-limiti
                      :updater !ssr-hidden-limiti)
    (ssr-hidden-attr :type (array (unsigned-byte 16)
                                  (#.*ldtr-tr-names-len*))
                     :fix (acl2::loghead 16 (ifix x))
                     :initially 0
                     :resizable nil
                     :accessor ssr-hidden-attri
                     :updater !ssr-hidden-attri)
    (:doc "</li>")

    (:doc "<li>@('CTR'): Control registers --- See Intel manual,
    Jan'19, Volume 3, Section 2.5.<br/>")
    ;; [Shilpi]:
    ;; Note that CR0 is still a 32-bit register in 64-bit mode.  All
    ;; other control registers are 64-bit wide.  Also, CR4 has all
    ;; but the low 21 bits reserved.  It'd be nice to define these
    ;; registers separately so that bignum creation can be avoided
    ;; during slicing operations involving these registers.
    (ctr  :type (array (unsigned-byte 64)
                       (#.*control-register-names-len*))
          :fix (acl2::loghead 64 (ifix x))
          :initially 0
          :resizable nil
          :accessor ctri
          :updater !ctri)
    (:doc "</li>")

    (:doc "<li>@('DBG'): Debug registers --- See Intel manual, Jan'19,
    Volume 3, Section 17.2.<br/>")
    (dbg :type (array (unsigned-byte 64)
                      (#.*debug-register-names-len*))
         :initially 0
         :fix (acl2::loghead 64 (ifix x))
         :resizable nil
         :accessor dbgi
         :updater !dbgi)
    (:doc "</li>")


    (:doc "<li>@('FPU 80-bit data registers'): The MMX
     registers (@('MM0') through @('MM7')) are aliased to the low
     64-bits of the FPU data registers.  See Intel manual, Jan'19,
     Volume 1, Section 8.1.2.")
    (fp-data :type (array (unsigned-byte 80)
                          (#.*fp-data-register-names-len*))
             :fix (acl2::loghead 80 (ifix x))
             :initially 0
             :resizable nil
             :accessor fp-datai
             :updater !fp-datai)
    (:doc "</li>")

    (:doc "<li>@('FPU 16-bit control register'): See Intel manual,
     Jan'19, Volume 1, Section 8.1.5.")
    (fp-ctrl :type (unsigned-byte 16)
             :fix (acl2::loghead 16 (ifix x))
             :initially 0)
    (:doc "</li>")

    (:doc "<li>@('FPU 16-bit status register'): See Intel manual,
     Jan'19, Volume 1, Section 8.1.3.")
    (fp-status :type (unsigned-byte 16)
               :fix (acl2::loghead 16 (ifix x))
               :initially 0)
    (:doc "</li>")

    (:doc "<li>@('FPU 16-bit tag register'): See Intel manual,
     Jan'19, Volume 1, Section 8.1.7.")
    (fp-tag :type (unsigned-byte 16)
            :fix (acl2::loghead 16 (ifix x))
            :initially 0)
    (:doc "</li>")

    (:doc "<li>@('FPU 48-bit last instruction pointer'): See Intel
     manual, Jan'19, Volume 1, Figure 8-1.")
    (fp-last-inst :type (unsigned-byte 48)
                  :fix (acl2::loghead 48 (ifix x))
                  :initially 0)
    (:doc "</li>")

    (:doc "<li>@('FPU 48-bit last data (operand) pointer'): See Intel
     manual, Jan'19, Volume 1, Figure 8-1.")
    (fp-last-data :type (unsigned-byte 48)
                  :fix (acl2::loghead 48 (ifix x))
                  :initially 0)
    (:doc "</li>")

    (:doc "<li>@('FPU 11-bit opcode:') See Intel manual, Jan'19,
     Volume 1, Figure 8-1.<br/>")
    (fp-opcode :type (unsigned-byte 11)
               :fix (acl2::loghead 11 (ifix x))
               :initially 0)
    (:doc "</li>")

    (:doc "<li>@('MXCSR') register")
    (mxcsr :type (unsigned-byte 32)
           ;; Bits 7 through 12 are the individual masks for the
           ;; SIMD floating point exceptions.  These are set upon
           ;; a power-up or reset.
           :fix (acl2::loghead 32 (ifix x))
           :initially 8064)
    (:doc "</li>")


    (:doc "<li>@('OPMASK'): 8 opmask registers are used for
    conditional execution and merging of data elements in the
    destination operands of AVX-512 EVEX-encoded instructions.  They
    are also used as operands in opmask instructions like KMOV, etc.")
    (opmsk :type (array (unsigned-byte 64)
                        (#.*opmsk-register-names-len*))
           :fix (acl2::loghead 64 (ifix x))
           :initially 0
           :resizable nil
           :accessor opmski
           :updater !opmski)
    (:doc "</li>")

    (:doc "<li>@('ZMM'): ZMM 512-bit data registers --- the lower
    256-bits of the ZMM registers are aliased to the respective
    256-bit YMM registers and the lower 128-bit are aliased to the
    respective 128-bit XMM registers.  Note that registers YMM16/XMM16
    to YMM31/XMM31 are available only via the EVEX prefix (AVX-512).")
    (zmm :type (array (unsigned-byte 512)
                      (#.*zmm-register-names-len*))
         :fix (acl2::loghead 512 (ifix x))
         :initially 0
         :resizable nil
         :accessor zmmi
         :updater !zmmi)
    (:doc "</li>")

    (:doc "<li>@('MSR'): Model-specific registers<br/>")
    (msr :type (array (unsigned-byte 64)
                      (#.*model-specific-register-names-len*))
         :fix (acl2::loghead 64 (ifix x))
         :initially 0
         :resizable nil
         :accessor msri
         :updater !msri)
    (:doc "</li>")

    (:doc "<li>@('MEM'): Field modeling @('2^52') bytes of physical
    memory in @('sys-view') and @('2^48') bytes of linear memory in
    @('app-view'). <br/>")
    (mem   :type (array (unsigned-byte 8) (,*mem-size-in-bytes*)) ;; 2^52
           :initially 0
           :fix (acl2::loghead 8 (ifix x))
           :child-stobj bigmem::mem
           :child-accessor bigmem::read-mem
           :child-updater  bigmem::write-mem
           :accessor memi
           :updater !memi)
    (:doc "</li>")

    (:doc "</ul>")))

(defun xdoc-x86-state (xs) ;; xs: *x86isa-state*
  (if (atom xs)
      ""
    (let* ((fld (car xs))
           (rest (xdoc-x86-state (cdr xs))))
      (if (equal (car fld) :doc)
          (str::cat (cadr fld) rest)
        (str::cat "@({ " (str::pretty fld
                                      :config (str::make-printconfig
                                               :home-package (pkg-witness "X86ISA")
                                               :print-lowercase t))
                  " })" rest)))))

(with-output
  :on summary
  :summary-off #!acl2(:other-than errors time)
  (make-event
   `(rstobj2::defrstobj x86
                        ,@(loop$ for fld in *x86isa-state* append
                                 (if (equal (car fld) :doc)
                                     nil
                                   (list fld)))
                        :inline t
                        :non-memoizable t
                        :enable '(bigmem::read-mem-over-write-mem
                                  bigmem::read-mem-from-nil
                                  bigmem::loghead-identity-alt)
                        :accessor xr
                        :updater  xw
                        :accessor-template ( x)
                        :updater-template (! x))))

(defthm x86p-xw
  (implies (x86p x86)
           (x86p (xw fld index val x86))))

(globally-disable '(x86p))

;; ----------------------------------------------------------------------

(make-event
 `(defxdoc x86isa-state
    :pkg "X86ISA"
    :parents (machine)
    :short "The state of the @('x86isa') model"
    :long ,(str::cat
            "<h4>Definition of the @('x86isa') state</h4>

 <p>The definition of the state uses nested and abstract stobjs by way
 of community books @(tsee rstobj2::defrstobj) and @(tsee
 bigmem::bigmem).  It may be interesting to read about the old
 definition to see how the current definition supports all of its
 functionality but in a more maintainable way; see @(see
 x86isa-state-history).</p>

 <p>The @('bigmem') books define a memory model similar to the old
 @('x86isa') memory model in that it provides a record representation
 for reasoning and an allocate-on-demand, array-like performance for
 execution. The x86 concrete stobj has the @('bigmem') stobj for its
 memory field; @('defrstobj') exports the @('bigmem') memory accessor
 and updater functions alongside those of other x86 fields and gives
 us a state definition that's logically a multi-typed record.
 @('defrstobj') also allows the definition of a universal accessor and
 updater, so we still retain that feature in the @('x86isa')
 books.</p>

 <p>Note that the @('bigmem') books define a 64-bit address space,
 though the @('x86isa') state restricts that to a 52-bit address space
 because the max. physical address allowed by the x86 architecture is
 52 (as of this writing in mid-2021).  If the max. allowed physical
 address is increased anywhere up to 64 bits, then we can simply
 change the size of the @('mem') field in the @('x86isa') stobj.</p>

 <h4>x86 ISA state components modeled by @('x86isa')</h4>"

            (xdoc-x86-state *x86isa-state*))))

(defxdoc x86isa-state-history
  :parents (x86isa-state)
  :short "A short history of the definition of the x86 state"

  :long "<h4>Old definition of the @('x86isa') state</h4>

 <p>Before @(tsee bigmem::bigmem) and @(tsee rstobj2::defrstobj)
 were used to define the x86 state, the x86 state's definition was
 rather tedious.  (For future reference, the following git revision
 has that old definition:
 @('dea40263247bd930077205526934bc596686bfb0')).</p>

 <p>This current file @('state.lisp') replaces the following old
 files, all of which are deleted now.</p>
 <ul>
  <li> @('concrete-state.lisp') </li>
  <li> @('concrete-memory.lisp') </li>
  <li> @('abstract-state.lisp') </li>
  <li> @('state-field-thms.lisp') </li>
 </ul>

 <p>The old x86isa memory model was based on the FMCAD'2012 paper \"A
 Formal Model of a Large Memory that Supports Efficient Execution\".
 The following comment from the old file @('concrete-state.lisp')
 describes it briefly:</p>

      <code>
      ....
      ;; For our ACL2 model, we define a paging-like mechanism to
      ;; model the complete x86 52-bit address space.  The memory is
      ;; laid out in a flat array, to be viewed as back-to-back
      ;; \"pseudo-pages\" each of size 2^27 bytes (128MB).  The address
      ;; of a byte is split into two pieces: a 25-bit pseudo-page
      ;; address and a 27-bit offset within a page.  The mem-table
      ;; data structure is of size *mem-table-size* = 2^25 -- thus,
      ;; indices are 25 bits -- and it maps these indices to 25-bit
      ;; pseudo-page addresses.  However, the mem-table values are
      ;; actually 26-bit values: the least significant bit is
      ;; initially 1, but is 0 when the entry is valid, in which case
      ;; the most significant 25 bits represent a pseudo-page address.
      ;; The offset of a byte address is a 27-bit wide address, which
      ;; when added to (ash pseudo-page-address 27), gives the \"real\"
      ;; address of a byte stored in mem-array.  Mem-array-next-addr
      ;; keeps track of the 25-bit index of the pseudo-page to be
      ;; allocated next.

      ;; Here is an example of how this works.  Suppose we have the
      ;; following, where again, the least significant bit of 0
      ;; indicates a valid entry, and where {i, 1'bx} denotes
      ;; concatenation of the bit-vector i with the single bit x.

      ;;   mem-table[#x0654321] = {0, 1'b0}
      ;;   mem-table[#x16789ab] = {1, 1'b0}
      ;;   mem-table[#x0111111] = {2, 1'b0}

      ;; All additional values in mem-table are the initial value of
      ;; 1, which means \"page is not present\".

      ;; Then mem-array starts as follows.

      ;;  2^27 bytes corresponding to byte addresses with top 25 bits = #x0654321
      ;;  2^27 bytes corresponding to byte addresses with top 25 bits = #x16789ab
      ;;  2^27 bytes corresponding to byte addresses with top 25 bits = #x0111111

      (mem-table :type (array (unsigned-byte #.*mem-table-size-bits+1*)
                              ;; *mem-table-size-bits* of pseudo-page
                              ;; address, followed by 1 extra bit
                              ;; (LSB) to indicate the
                              ;; absence/presence of pseudo-pages
                              (#.*mem-table-size*))
                 :initially 1
                 :resizable nil)

      (mem-array :type (array (unsigned-byte 8)
                              (#.*initial-mem-array-length*))
                 :initially 0
                 :resizable t)

      (mem-array-next-addr :type (integer 0 #.*mem-table-size*)
                           :initially 0)

      ...
      </code>

 <p>The proof of correctness of this memory model was pretty
  involved (see the old file @('concrete-memory.lisp')).  Then there
  was the overhead of introducing an abstract stobj to logically view
  this memory as a record (see old file @('abstract-stobj.lisp')).</p>

  <p>All of this was finished before nested stobjs were supported in
 ACL2, so there was not much incentive to simplify the memory model or
 the state definition.</p>

 <h5>Non-interference Properties</h5>

 <p>We used a neat trick for all the accessors and updaters of
 the @('x86isa') state's field that is worth mentioning here. Say
 @('RGFI*') is the name of the corresponding exported accessor from
 defabsstobj; during execution, @('RGFI*') calls are really
 @('RGF$CI') calls, the concrete accessor from the corresponding
 concrete stobj.</p>

 <code> Signature: (RGFI* index x86) </code>

 <p>We also defined a universal accessor function @('XR'), meant to be
 used only for reasoning:</p>

 <code> Signature: (XR fld-name index x86) </code>

 <p>@('XR') case-split on @('fld-name') and called the appropriate
 accessor function (e.g., if fld-name was @(':RGF'), @('XR') called
 @('RGFI*'), and so on).  We defined a similar universal updater
 function @('XW').  We then proved read-over-write/write-over-write,
 etc. lemmas about just @('XR') and @('XW'), thereby getting these
 properties for all fields of the x86 state. This way, we avoid a
 blow-up in the number of such lemmas as the number of fields in the
 state increase.</p>

 <p>We then defined another function, @('RGFI') (inlined), with the
  same signature as @('RGFI*'), whose body was an @('MBE') like
  so:</p>

 <code>
 (RGFI index x86) :=
  (mbe :logic (XR :RGF index x86)
       :exec (RGFI* index x86))
 </code>

 <p>We then used @('RGFI') as the canonical accessor function for the
 @('RGF') field --- we never used @('RGFI*') or @('XR') in our
 definitions from this point on, though @('XR') was often used in
 definitions where we didn't care about the execution speed (e.g.,
 non-executable functions used only for reasoning).  We kept @('RGFI')
 enabled and @('XR') disabled.</p>

 <p>The consequence of this was that whenever an @('RGFI') call was
 encountered during reasoning, it quickly opened up to @('XR') (about
 which we have all those nice theorems).  During execution, @('RGFI')
 was simply the efficient concrete accessor @('RGF$CI').</p>")

;; ----------------------------------------------------------------------
