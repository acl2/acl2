; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

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
; Alessandro Coglio <coglio@kestrel.edu>
; Contributing Author(s):
; Dmitry Nadezhin
; Shilpi Goel

(in-package "X86ISA")

;; ----------------------------------------------------------------------

(include-book "segmentation")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ----------------------------------------------------------------------

(defsection top-level-memory
  :parents (machine)
  :short "Top-level Memory Accessor and Updater Functions"
  )

(local (xdoc::set-default-parents top-level-memory))

;; ----------------------------------------------------------------------

(define address-aligned-p
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (operand-size :type (member 1 2 4 6 8 10 16 32 64))
   (memory-ptr? booleanp))
  :inline t
  :no-function t
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check the alignment of a linear address."
  :long
  "<p>
   Besides the address to check for alignment,
   this function takes as argument the operand size
   (from which the alignment to check is determined)
   and a flag indicating whether the address to check for alignment
   contains a memory operand of the form m16:16, m16:32, or m16:64
   (see Intel manual, Mar'17, Volume 2, Section 3.1.1.3).
   </p>
   <p>
   Words, doublewords, quadwords, and double quadwords
   must be aligned at boundaries of 2, 4, 8, or 16 bytes.
   Memory pointers of the form m16:xx must be aligned so that
   their xx portion is aligned as a word, doubleword, or quadword;
   this automatically guarantees that their m16 portion is aligned as a word.
   See Intel manual, Mar'17, Volume 1, Section 4.1.1.
   See AMD manual, Dec'17, Volume 2, Table 8-7
   (note that the table does not mention explicitly
   memory pointers of the form m16:64).
   </p>
   <p>
   If the operand size is 6, the operand must be an m16:32 pointer.
   If the operand size is 10, the operand must an m16:64 pointer.
   If the operand size is 4, it may be either an m16:16 pointer or not;
   in this case, the @('memory-ptr?') argument is used to
   determine whether the address should be aligned
   at a word or doubleword boundary.
   If the operand size is 1, 2, 8, or 16,
   it cannot be a memory pointer of the form m16:xx.
   </p>"
  (b* ((addr (the (signed-byte #.*max-linear-address-size*) addr))
       (operand-size (the (integer 0 65) operand-size)))
    (case operand-size
      ;; Every byte access is always aligned.
      (1 t)
      (6 (equal (logand addr #b11) 0))   ; m16:32
      (10 (equal (logand addr #b111) 0)) ; m16:64
      (otherwise
       (if (and memory-ptr?
                (eql operand-size 4))
           (equal (logand addr #b1) 0) ; m16:16
         (equal (logand addr (the (integer 0 65) (- operand-size 1)))
                0)))))

  ///

  (defthm memory-byte-accesses-are-always-aligned
    (equal (address-aligned-p addr 1 mem-ptr?) t))

  (defthm address-aligned-p-mem-ptr-input-irrelevant-for-all-but-bytes=4
    (implies (and (syntaxp (not (equal mem-ptr? ''nil)))
                  (not (equal nbytes 4)))
             (equal (address-aligned-p addr nbytes mem-ptr?)
                    (address-aligned-p addr nbytes nil)))))

;; ----------------------------------------------------------------------

;; Memory Read Functions:

(defthm-unsigned-byte-p n16p-xr-seg-hidden-attr
  :hyp t
  :bound 16
  :concl (xr :seg-hidden-attr i x86)
  :gen-linear t
  :gen-type t)

(define gen-read-function (&key
                           (size natp)
                           (signed? booleanp)
                           (check-alignment?-var booleanp)
                           (mem-ptr?-var booleanp))
  :mode :program

  (b* ((size-str (symbol-name (if (< size 10)
                                  (acl2::packn (list 0 size))
                                (acl2::packn (list size)))))
       (fn (str::cat (if signed? "RIME" "RME") size-str))
       (fn-name (intern$ fn "X86ISA"))
       (fn-call `(,fn-name proc-mode eff-addr seg-reg r-x
                           ,@(and check-alignment?-var
                                  '(check-alignment?))
                           x86
                           ,@(and mem-ptr?-var
                                  `(:mem-ptr? mem-ptr?))))
       (lin-mem-fn (str::cat (if signed? "RIML" "RML") size-str))
       (lin-mem-fn-name (intern$ lin-mem-fn "X86ISA"))
       (short-doc-string
        (str::cat
         "Read "
         (if signed? "a signed " "an unsigned ")
         (str::nat-to-dec-string size)
         "-bit value from memory via an effective address."))
       (long-doc-string
        (str::cat
         "<p>The effective address @('eff-addr') is translated to a canonical
          linear address using @(see ea-to-la).  If this translation is
          successful and no other errors (like alignment errors) occur, then
          @(see " lin-mem-fn ") is called.</p>
          <p>Prior to the effective address translation, we check whether read
          access is allowed.  The only case in which it is not allowed is when a
          read access is attempted on an execute-only code segment, in 32-bit
          mode.  In 64-bit mode, the R bit of the code segment descriptor is
          ignored (see Atmel manual, Dec'17, Volume 2, Section 4.8.1).</p>")))

    `(define ,fn-name ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
                       (eff-addr  :type (signed-byte 64))
                       (seg-reg   :type (integer 0 #.*segment-register-names-len-1*))
                       (r-x       :type (member :r :x))
                       ,@(and check-alignment?-var `((check-alignment? booleanp)))
                       x86
                       ,@(and mem-ptr?-var `(&key ((mem-ptr? booleanp) 'nil))))
       :inline t
       :no-function t
       :returns (mv flg
                    (value
                     (,(if signed? 'signed-byte-p 'unsigned-byte-p) ,size value)
                     :hyp (x86p x86))
                    (x86-new x86p :hyp (x86p x86)))
       :parents (top-level-memory)

       :short ,short-doc-string
       :long ,long-doc-string

       (b* (((when (and
                    (/= proc-mode #.*64-bit-mode*)
                    (= seg-reg #.*cs*)
                    (eq r-x :r)
                    (b* ((attr (loghead 16 (seg-hidden-attri seg-reg x86)))
                         (r (code-segment-descriptor-attributesBits->r attr)))
                      (= r 0))))
             (mv (list :execute-only-code-segment eff-addr) 0 x86))
            ((mv flg lin-addr)
             (ea-to-la proc-mode eff-addr seg-reg ,(/ size 8) x86))
            ((when flg) (mv flg 0 x86))
            ,@(and
               check-alignment?-var
               `(((unless (or (not check-alignment?)
                              (address-aligned-p
                               lin-addr
                               ,(/ size 8)
                               ,(if mem-ptr?-var 'mem-ptr? 'nil))))
                  (mv (list :unaligned-linear-address lin-addr) 0 x86)))))
         (,lin-mem-fn-name lin-addr r-x x86))
       ///

       (,(if signed? 'defthm-signed-byte-p 'defthm-unsigned-byte-p)
        ,(mk-name (if signed? "I" "N") size-str "P-OF-MV-NTH-1-" fn)
        :hyp t
        :bound ,size
        :concl (mv-nth 1 ,fn-call)
        :gen-linear t
        :gen-type t)

       (defrule ,(mk-name fn "-VALUE-WHEN-ERROR")
         (implies (mv-nth 0 ,fn-call)
                  (equal (mv-nth 1 ,fn-call) 0))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           ))
                  ))

       (defrule ,(mk-name fn "-DOES-NOT-AFFECT-STATE-IN-APP-VIEW")
         (implies (app-view x86)
                  (equal (mv-nth 2 ,fn-call) x86))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           ))
                  ))

       (defrule ,(mk-name "MV-NTH-2-" fn "-IN-SYSTEM-LEVEL-NON-MARKING-VIEW")
         (implies (and (not (app-view x86))
                       (not (marking-view x86))
                       (x86p x86)
                       (not (mv-nth 0 ,fn-call)))
                  (equal (mv-nth 2 ,fn-call) x86))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           ))))

       (defrule ,(mk-name "XR-" fn "-STATE-APP-VIEW")
         (implies (app-view x86)
                  (equal (xr fld index (mv-nth 2 ,fn-call))
                         (xr fld index x86)))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           ))))

       (defrule ,(mk-name "XR-" fn "-STATE-SYS-VIEW")
         (implies (and (not (app-view x86))
                       (not (equal fld :mem))
                       (not (equal fld :fault))
                       ,@(if (< size 10)
                             nil
                           `((member-equal fld *x86-field-names-as-keywords*))))
                  (equal (xr fld index (mv-nth 2 ,fn-call))
                         (xr fld index x86)))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           )))
         ,@(if (< size 10)
               nil
             `(:disable (rb unsigned-byte-p signed-byte-p member-equal))))

       (defrule ,(mk-name fn "-XW-APP-VIEW")
         (implies
          (and (app-view x86)
               (not (equal fld :mem))
               (not (equal fld :app-view))
               (not (equal fld :seg-hidden-base))
               (not (equal fld :seg-hidden-limit))
               (not (equal fld :seg-hidden-attr))
               (not (equal fld :seg-visible))
               (not (equal fld :msr)))
          (and
           (equal (mv-nth 0
                          ,(search-and-replace-once
                            'x86
                            '(xw fld index value x86)
                            fn-call))
                  (mv-nth 0 ,fn-call))
           (equal (mv-nth 1 ,(search-and-replace-once
                              'x86
                              '(xw fld index value x86)
                              fn-call))
                  (mv-nth 1 ,fn-call))
           ;; No need for the conclusion about the state; see
           ;; ,(mk-name fn "-DOES-NOT-AFFECT-STATE-IN-APP-VIEW")
           ))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           )))
         :disable (rb))

       (defrule ,(mk-name fn "-XW-SYS-VIEW")
         (implies
          (and (not (app-view x86))
               (not (equal fld :fault))
               (not (equal fld :seg-visible))
               (not (equal fld :seg-hidden-base))
               (not (equal fld :seg-hidden-limit))
               (not (equal fld :seg-hidden-attr))
               (not (equal fld :mem))
               (not (equal fld :ctr))
               (not (equal fld :msr))
               (not (equal fld :rflags))
               (not (equal fld :app-view))
               (not (equal fld :marking-view))
               ,@(if (< size 10)
                     nil
                   `((member-equal fld *x86-field-names-as-keywords*))))
          (and
           (equal
            (mv-nth 0 ,(search-and-replace-once
                        'x86
                        '(xw fld index value x86)
                        fn-call))
            (mv-nth 0 ,fn-call))
           (equal
            (mv-nth 1 ,(search-and-replace-once
                        'x86
                        '(xw fld index value x86)
                        fn-call))
            (mv-nth 1 ,fn-call))
           (equal
            (mv-nth 2 ,(search-and-replace-once
                        'x86
                        '(xw fld index value x86)
                        fn-call))
            (xw fld index value (mv-nth 2 ,fn-call)))))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           )))
         ,@(if (< size 10)
               nil
             `(:disable (rb unsigned-byte-p signed-byte-p member-equal))))

       (defrule ,(mk-name fn "-XW-SYS-VIEW-RFLAGS-NOT-AC")
         (implies
          (and (not (app-view x86))
               (equal (rflagsBits->ac value)
                      (rflagsBits->ac (rflags x86))))
          (and
           (equal
            (mv-nth 0 ,(search-and-replace-once
                        'x86
                        '(xw :rflags nil value x86)
                        fn-call))
            (mv-nth 0 ,fn-call))
           (equal
            (mv-nth 1 ,(search-and-replace-once
                        'x86
                        '(xw :rflags nil value x86)
                        fn-call))
            (mv-nth 1 ,fn-call))
           (equal
            (mv-nth 2 ,(search-and-replace-once
                        'x86
                        '(xw :rflags nil value x86)
                        fn-call))
            (xw :rflags nil value (mv-nth 2 ,fn-call)))))
         :enable (,@(and signed?
                         `(,lin-mem-fn-name
                           ;; ,(mk-name "RML" size-str)
                           )))
         :disable (rb unsigned-byte-p signed-byte-p))

       (defrule ,(mk-name fn "-WHEN-64-BIT-MODEP-AND-NOT-FS/GS")
         (implies (and (not (equal seg-reg #.*fs*))
                       (not (equal seg-reg #.*gs*))
                       (canonical-address-p eff-addr)
                       ,@(and check-alignment?-var
                              `((or (not check-alignment?)
                                    (address-aligned-p
                                     eff-addr ,(/ size 8)
                                     ,(if mem-ptr?-var 'mem-ptr? 'nil))))))
                  (equal ,(search-and-replace-once 'proc-mode
                                                   '#.*64-bit-mode*
                                                   fn-call)
                         (,lin-mem-fn-name eff-addr r-x x86))))

       ,@(and
          check-alignment?-var
          `((defrule ,(mk-name fn "-UNALIGNED-WHEN-64-BIT-MODEP-AND-NOT-FS/GS")
              (implies
               (and (not (equal seg-reg #.*fs*))
                    (not (equal seg-reg #.*gs*))
                    (not
                     (or (not check-alignment?)
                         (address-aligned-p
                          eff-addr
                          ,(/ size 8)
                          ,(if mem-ptr?-var 'mem-ptr? 'nil))))
                    (canonical-address-p eff-addr))
               (equal ,(search-and-replace-once 'proc-mode
                                                '#.*64-bit-mode*
                                                fn-call)
                      (list (list :unaligned-linear-address eff-addr)
                            0
                            x86))))))

       (defrule ,(mk-name fn "-WHEN-64-BIT-MODEP-AND-FS/GS")
         (implies
          (or (equal seg-reg #.*fs*)
              (equal seg-reg #.*gs*))
          (equal
           ,(search-and-replace-once 'proc-mode '#.*64-bit-mode* fn-call)
           (b* (((mv flg lin-addr)
                 (b* (((mv base & &)
                       (segment-base-and-bounds 0 seg-reg x86))
                      (lin-addr (i64 (+ base (n64 eff-addr)))))
                   (if (canonical-address-p lin-addr)
                       (mv nil lin-addr)
                     (mv (list :non-canonical-address lin-addr) 0))))
                ((when flg)
                 (mv flg 0 x86))
                ,@(and
                   check-alignment?-var
                   `(((unless (or (not check-alignment?)
                                  (address-aligned-p
                                   lin-addr
                                   ,(/ size 8)
                                   ,(if mem-ptr?-var 'mem-ptr? 'nil))))
                      (mv (list :unaligned-linear-address lin-addr) 0 x86)))))
             (,lin-mem-fn-name lin-addr r-x x86))))
         :hints (("Goal" :in-theory (e/d (ea-to-la) ())))))))

(make-event
 `(progn
    (local (in-theory (e/d ()
                           (unsigned-byte-p
                            signed-byte-p
                            force (force)))))
    ;; rme08
    ,(gen-read-function :size 8
                        :signed? nil
                        :check-alignment?-var nil
                        :mem-ptr?-var nil)
    ;; rime08
    ,(gen-read-function :size 8
                        :signed? t
                        :check-alignment?-var nil
                        :mem-ptr?-var nil)
    ;; rme16
    ,(gen-read-function :size 16
                        :signed? nil
                        :check-alignment?-var t
                        :mem-ptr?-var nil)
    ;; rime16
    ,(gen-read-function :size 16
                        :signed? t
                        :check-alignment?-var t
                        :mem-ptr?-var nil)
    ;; rme32
    ,(gen-read-function :size 32
                        :signed? nil
                        :check-alignment?-var t
                        :mem-ptr?-var t)
    ;; rime32
    ,(gen-read-function :size 32
                        :signed? t
                        :check-alignment?-var t
                        :mem-ptr?-var t)
    ;; rme48
    ,(gen-read-function :size 48 ;; typically a m16:32 pointer
                        :signed? nil
                        :check-alignment?-var t
                        :mem-ptr?-var nil)
    ;; rme64
    ,(gen-read-function :size 64
                        :signed? nil
                        :check-alignment?-var t
                        :mem-ptr?-var nil)
    ;; rime64
    ,(gen-read-function :size 64
                        :signed? t
                        :check-alignment?-var t
                        :mem-ptr?-var nil)
    ;; rme80
    ,(gen-read-function :size 80
                        :signed? nil
                        :check-alignment?-var t
                        :mem-ptr?-var nil)
    ;; rme128
    ;; Note: A #GP exception should be thrown here instead of an #AC fault when
    ;; the address is not aligned.  See Intel Manuals, Volume 3, Section 6.15,
    ;; Exception and Interrupt Reference, Interrupt 17 Alignment Check
    ;; Exception (#AC).
    ,(gen-read-function :size 128
                        :signed? nil
                        :check-alignment?-var t
                        :mem-ptr?-var nil)))

(define rme-size
  ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
   (nbytes :type (member 1 2 4 6 8 10 16))
   (eff-addr :type (signed-byte 64))
   (seg-reg :type (integer 0 #.*segment-register-names-len-1*))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (value natp)
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned value with the specified number of bytes
          from memory via an effective address."
  :long
  "<p>The effective address is translated to a canonical linear address using
   @(see ea-to-la). If this translation is successful and no other errors (like
   alignment errors) occur, then @(see rml-size) is called.</p>
   <p>Prior to the effective address translation, we check whether read
   access is allowed.  The only case in which it is not allowed is when a
   read access is attempted on an execute-only code segment, in 32-bit
   mode.  In 64-bit mode, the R bit of the code segment descriptor is
   ignored; see Intel manual, Dec'17, Volume 2, Section 4.8.1</p>"
  (b* (((when (and (/= proc-mode #.*64-bit-mode*)
                   (= seg-reg #.*cs*)
                   (eq r-x :r)
                   (b* ((attr (loghead 16 (seg-hidden-attri seg-reg x86)))
                        (r (code-segment-descriptor-attributesBits->r attr)))
                     (= r 0))))
        (mv (list :execute-only-code-segment eff-addr) 0 x86))
       ((mv flg lin-addr) (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
       ((when flg) (mv flg 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml-size nbytes lin-addr r-x x86))
  :inline t
  :no-function t

  ///

  (defrule rme-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr nbytes mem-ptr?)))
             (equal (rme-size #.*64-bit-mode*
                              nbytes eff-addr seg-reg r-x check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (rml-size nbytes eff-addr r-x x86))))

  (defrule rme-size-when-64-bit-modep-fs/gs
    (implies (or (equal seg-reg #.*fs*)
                 (equal seg-reg #.*gs*))
             (equal (rme-size #.*64-bit-mode*
                              nbytes eff-addr seg-reg r-x check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (b* (((mv flg lin-addr)
                          (b* (((mv base & &)
                                (segment-base-and-bounds 0 seg-reg x86))
                               (lin-addr (i64 (+ base (n64 eff-addr)))))
                            (if (canonical-address-p lin-addr)
                                (mv nil lin-addr)
                              (mv (list :non-canonical-address lin-addr) 0))))
                         ((when flg)
                          (mv flg 0 x86))
                         ((unless (or (not check-alignment?)
                                      (address-aligned-p
                                       lin-addr nbytes mem-ptr?)))
                          (mv (list :unaligned-linear-address lin-addr) 0 x86)))
                      (rml-size nbytes lin-addr r-x x86))))
    :in-theory (e/d (ea-to-la) ()))

  (defthm rme-size-unaligned-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of rme-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not
                   (or (not check-alignment?)
                       (address-aligned-p eff-addr nbytes mem-ptr?)))
                  (canonical-address-p eff-addr))
             (equal (rme-size #.*64-bit-mode*
                              nbytes eff-addr seg-reg r-x check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (list (list :unaligned-linear-address eff-addr)
                          0 x86)))
    :hints (("Goal" :in-theory (e/d (rme-size) ()))))

  (defthm rme-size-non-canonical-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of rme-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not (canonical-address-p eff-addr)))
             (equal (rme-size #.*64-bit-mode*
                              nbytes eff-addr seg-reg r-x check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (list (list :non-canonical-address eff-addr) 0 x86)))
    :hints (("Goal" :in-theory (e/d (rme-size) ()))))


  (defruled rme-size-of-1-to-rme08
    (equal
     (rme-size proc-mode 1 eff-addr seg-reg r-x check-alignment? x86
               :mem-ptr? mem-ptr?)
     (rme08 proc-mode eff-addr seg-reg r-x x86))
    :enable (rme-size rme08))

  (defruled rme-size-of-2-to-rme16
    (equal
     (rme-size proc-mode 2 eff-addr seg-reg r-x check-alignment? x86
               :mem-ptr? mem-ptr?)
     (rme16 proc-mode eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme16))

  (defruled rme-size-of-4-to-rme32
    (equal
     (rme-size proc-mode 4 eff-addr seg-reg r-x check-alignment? x86
               :mem-ptr? mem-ptr?)
     (rme32 proc-mode eff-addr seg-reg r-x check-alignment? x86
            :mem-ptr? mem-ptr?))
    :enable (rme-size rme32))

  (defruled rme-size-of-6-to-rme48
    (equal
     (rme-size proc-mode 6 eff-addr seg-reg r-x check-alignment? x86
               :mem-ptr? mem-ptr?)
     (rme48 proc-mode eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme48))

  (defruled rme-size-of-8-to-rme64
    (equal
     (rme-size proc-mode 8 eff-addr seg-reg r-x check-alignment? x86
               :mem-ptr? mem-ptr?)
     (rme64 proc-mode eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme64))

  (defruled rme-size-of-10-to-rme64
    (equal
     (rme-size proc-mode 10 eff-addr seg-reg r-x check-alignment? x86
               :mem-ptr? mem-ptr?)
     (rme80 proc-mode eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme80))

  (defruled rme-size-of-16-to-rme128
    (equal
     (rme-size proc-mode 16 eff-addr seg-reg r-x check-alignment? x86
               :mem-ptr? mem-ptr?)
     (rme128 proc-mode eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme128)))

(define rime-size
  ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
   (nbytes :type (member 1 2 4 8))
   (eff-addr :type (signed-byte 64))
   (seg-reg :type (integer 0 #.*segment-register-names-len-1*))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (value integerp :hyp (integerp nbytes))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read a signed value with the specified number of bytes
          from memory via an effective address."
  :long
  "<p>The effective address is translated to a canonical linear address using
   @(see ea-to-la). If this translation is successful and no other errors (like
   alignment errors) occur, then @(see riml-size) is called.</p>
   <p>Prior to the effective address translation, we check whether read
   access is allowed.  The only case in which it is not allowed is when a
   read access is attempted on an execute-only code segment, in 32-bit
   mode.  In 64-bit mode, the R bit of the code segment descriptor is
   ignored; see Atmel manual, Dec'17, Volume 2, Section 4.8.1</p>"
  (b* (((when (and (/= proc-mode #.*64-bit-mode*)
                   (= seg-reg #.*cs*)
                   (eq r-x :r)
                   (b* ((attr (loghead 16 (seg-hidden-attri seg-reg x86)))
                        (r (code-segment-descriptor-attributesBits->r attr)))
                     (= r 0))))
        (mv (list :execute-only-code-segment eff-addr) 0 x86))
       ((mv flg lin-addr) (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
       ((when flg) (mv flg 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (riml-size nbytes lin-addr r-x x86))
  :inline t
  :no-function t
  ///

  (defrule rime-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr nbytes mem-ptr?)))
             (equal (rime-size #.*64-bit-mode*
                               nbytes eff-addr seg-reg r-x check-alignment? x86
                               :mem-ptr? mem-ptr?)
                    (riml-size nbytes eff-addr r-x x86))))

  (defrule rime-size-when-64-bit-modep-fs/gs
    (implies (or (equal seg-reg #.*fs*)
                 (equal seg-reg #.*gs*))
             (equal (rime-size #.*64-bit-mode*
                               nbytes eff-addr seg-reg r-x check-alignment? x86
                               :mem-ptr? mem-ptr?)
                    (b* (((mv flg lin-addr)
                          (b* (((mv base & &)
                                (segment-base-and-bounds 0 seg-reg x86))
                               (lin-addr (i64 (+ base (n64 eff-addr)))))
                            (if (canonical-address-p lin-addr)
                                (mv nil lin-addr)
                              (mv (list :non-canonical-address lin-addr) 0))))
                         ((when flg)
                          (mv flg 0 x86))
                         ((unless (or (not check-alignment?)
                                      (address-aligned-p
                                       lin-addr nbytes mem-ptr?)))
                          (mv (list :unaligned-linear-address lin-addr) 0 x86)))
                      (riml-size nbytes lin-addr r-x x86))))
    :in-theory (e/d (ea-to-la) ()))

  (defthm rime-size-unaligned-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of rime-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not
                   (or (not check-alignment?)
                       (address-aligned-p eff-addr nbytes mem-ptr?)))
                  (canonical-address-p eff-addr))
             (equal (rime-size #.*64-bit-mode*
                               nbytes eff-addr seg-reg r-x check-alignment? x86
                               :mem-ptr? mem-ptr?)
                    (list (list :unaligned-linear-address eff-addr)
                          0 x86)))
    :hints (("Goal" :in-theory (e/d (rime-size) ()))))

  (defthm rime-size-non-canonical-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of rime-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not (canonical-address-p eff-addr)))
             (equal (rime-size #.*64-bit-mode*
                               nbytes eff-addr seg-reg r-x check-alignment? x86
                               :mem-ptr? mem-ptr?)
                    (list (list :non-canonical-address eff-addr) 0 x86)))
    :hints (("Goal" :in-theory (e/d (rime-size) ()))))

  (defruled rime-size-of-1-to-rime08
    (equal (rime-size proc-mode 1 eff-addr seg-reg r-x check-alignment? x86
                      :mem-ptr? mem-ptr?)
           (rime08 proc-mode eff-addr seg-reg r-x x86))
    :enable (rime-size rime08))

  (defruled rime-size-of-2-to-rime16
    (equal (rime-size proc-mode 2 eff-addr seg-reg r-x check-alignment? x86
                      :mem-ptr? mem-ptr?)
           (rime16 proc-mode eff-addr seg-reg r-x check-alignment? x86))
    :enable (rime-size rime16))

  (defruled rime-size-of-4-to-rime32
    (equal
     (rime-size proc-mode 4 eff-addr seg-reg r-x check-alignment? x86
                :mem-ptr? mem-ptr?)
     (rime32 proc-mode eff-addr seg-reg r-x check-alignment? x86
             :mem-ptr? mem-ptr?))
    :enable (rime-size rime32))

  (defruled rime-size-of-8-to-rime64
    (equal
     (rime-size proc-mode 8 eff-addr seg-reg r-x check-alignment? x86
                :mem-ptr? mem-ptr?)
     (rime64 proc-mode eff-addr seg-reg r-x check-alignment? x86))
    :enable (rime-size rime64)))

;; ----------------------------------------------------------------------

;; Memory Write Functions:

(define gen-write-function (&key
                            (size natp)
                            (signed? booleanp)
                            (check-alignment?-var booleanp)
                            (mem-ptr?-var booleanp))
  :mode :program

  (b* ((size-str (symbol-name (if (< size 10)
                                  (acl2::packn (list 0 size))
                                (acl2::packn (list size)))))
       (fn (str::cat (if signed? "WIME" "WME") size-str))
       (fn-name (intern$ fn "X86ISA"))
       (fn-call `(,fn-name proc-mode eff-addr seg-reg val
                           ,@(and check-alignment?-var
                                  '(check-alignment?))
                           x86
                           ,@(and mem-ptr?-var
                                  `(:mem-ptr? mem-ptr?))))
       (lin-mem-fn (str::cat (if signed? "WIML" "WML") size-str))
       (lin-mem-fn-name (intern$ lin-mem-fn "X86ISA"))
       (short-doc-string
        (str::cat
         "Write "
         (if signed? "a signed " "an unsigned ")
         (str::nat-to-dec-string size)
         "-bit value to memory via an effective address."))
       (long-doc-string
        (str::cat
         "<p>The effective address @('eff-addr') is translated to a canonical
          linear address.  If this translation is successful and no other error
          occurs (like alignment errors), then @(see " lin-mem-fn ") is
          called.</p>
          <p>Prior to the effective address translation, we check whether write
          access is allowed.  In 32-bit mode, write access is allowed in data
          segments (DS, ES, FS, GS, and SS) if the W bit in the segment
          descriptor is 1; write access is disallowed in code segments (this is
          not explicitly mentioned in Intel manual, May'18, Volume 3, Section
          3.4.5.1, but it seems reasonable).  In 64-bit mode, the W bit is
          ignored (see Atmel manual, Dec'17, Volume 2, Section 4.8.1); by
          analogy, we allow write access to the code segment as well.
          These checks may be slightly optimized using the invariant that
          SS.W must be 1 when SS is loaded.</p>")))

    `(define ,fn-name ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
                       (eff-addr  :type (signed-byte 64))
                       (seg-reg   :type (integer 0 #.*segment-register-names-len-1*))
                       (val       :type (,(if signed? 'signed-byte 'unsigned-byte) ,size))
                       ,@(and check-alignment?-var `((check-alignment? booleanp)))
                       x86
                       ,@(and mem-ptr?-var `(&key ((mem-ptr? booleanp) 'nil))))
       :inline t
       :no-function t
       :returns (mv flg
                    (x86-new x86p :hyp (x86p x86)))
       :parents (top-level-memory)

       :short ,short-doc-string
       :long ,long-doc-string

       (b* (((when (and (/= proc-mode #.*64-bit-mode*)
                        (or (= seg-reg #.*cs*)
                            (b* ((attr (loghead
                                        16 (seg-hidden-attri seg-reg x86)))
                                 (w (data-segment-descriptor-attributesBits->w
                                     attr)))
                              (= w 0)))))
             (mv (list :non-writable-segment eff-addr seg-reg) x86))
            ((mv flg lin-addr)
             (ea-to-la proc-mode eff-addr seg-reg ,(/ size 8) x86))
            ((when flg) (mv flg x86))
            ,@(and
               check-alignment?-var
               `(((unless (or (not check-alignment?)
                              (address-aligned-p
                               lin-addr
                               ,(/ size 8)
                               ,(if mem-ptr?-var 'mem-ptr? 'nil))))
                  (mv (list :unaligned-linear-address lin-addr) x86)))))
         (,lin-mem-fn-name lin-addr val x86))
       ///

       (defrule ,(mk-name fn "-WHEN-64-BIT-MODEP-AND-NOT-FS/GS")
         (implies (and (not (equal seg-reg #.*fs*))
                       (not (equal seg-reg #.*gs*))
                       (canonical-address-p eff-addr)
                       ,@(and check-alignment?-var
                              `((or (not check-alignment?)
                                    (address-aligned-p
                                     eff-addr ,(/ size 8)
                                     ,(if mem-ptr?-var 'mem-ptr? 'nil))))))
                  (equal ,(search-and-replace-once 'proc-mode
                                                   '#.*64-bit-mode*
                                                   fn-call)
                         (,lin-mem-fn-name eff-addr val x86))))

       ,@(and
          check-alignment?-var
          `((defrule ,(mk-name fn "-UNALIGNED-WHEN-64-BIT-MODEP-AND-NOT-FS/GS")
              (implies
               (and (not (equal seg-reg #.*fs*))
                    (not (equal seg-reg #.*gs*))
                    (not
                     (or (not check-alignment?)
                         (address-aligned-p
                          eff-addr
                          ,(/ size 8)
                          ,(if mem-ptr?-var 'mem-ptr? 'nil))))
                    (canonical-address-p eff-addr))
               (equal ,(search-and-replace-once 'proc-mode
                                                '#.*64-bit-mode*
                                                fn-call)
                      (list (list :unaligned-linear-address eff-addr) x86))))))

       (defrule ,(mk-name fn "-WHEN-64-BIT-MODEP-AND-FS/GS")
         (implies
          (or (equal seg-reg #.*fs*)
              (equal seg-reg #.*gs*))
          (equal
           ,(search-and-replace-once 'proc-mode '#.*64-bit-mode* fn-call)
           (b* (((mv flg lin-addr)
                 (b* (((mv base & &)
                       (segment-base-and-bounds 0 seg-reg x86))
                      (lin-addr (i64 (+ base (n64 eff-addr)))))
                   (if (canonical-address-p lin-addr)
                       (mv nil lin-addr)
                     (mv (list :non-canonical-address lin-addr) 0))))
                ((when flg)
                 (mv flg x86))
                ,@(and
                   check-alignment?-var
                   `(((unless (or (not check-alignment?)
                                  (address-aligned-p
                                   lin-addr
                                   ,(/ size 8)
                                   ,(if mem-ptr?-var 'mem-ptr? 'nil))))
                      (mv (list :unaligned-linear-address lin-addr) x86)))))
             (,lin-mem-fn-name lin-addr val x86))))
         :hints (("Goal" :in-theory (e/d (ea-to-la) ())))))))

(make-event
 `(progn
    (local (in-theory (e/d ()
                           (unsigned-byte-p
                            signed-byte-p
                            force (force)))))
    ;; wme08
    ,(gen-write-function :size 8
                         :signed? nil
                         :check-alignment?-var nil
                         :mem-ptr?-var nil)
    ;; wime08
    ,(gen-write-function :size 8
                         :signed? t
                         :check-alignment?-var nil
                         :mem-ptr?-var nil)
    ;; wme16
    ,(gen-write-function :size 16
                         :signed? nil
                         :check-alignment?-var t
                         :mem-ptr?-var nil)
    ;; wime16
    ,(gen-write-function :size 16
                         :signed? t
                         :check-alignment?-var t
                         :mem-ptr?-var nil)
    ;; wme32
    ,(gen-write-function :size 32
                         :signed? nil
                         :check-alignment?-var t
                         :mem-ptr?-var t)
    ;; wime32
    ,(gen-write-function :size 32
                         :signed? t
                         :check-alignment?-var t
                         :mem-ptr?-var t)
    ;; wme48
    ,(gen-write-function :size 48 ;; typically a m16:32 pointer
                         :signed? nil
                         :check-alignment?-var t
                         :mem-ptr?-var nil)
    ;; wme64
    ,(gen-write-function :size 64
                         :signed? nil
                         :check-alignment?-var t
                         :mem-ptr?-var nil)
    ;; wime64
    ,(gen-write-function :size 64
                         :signed? t
                         :check-alignment?-var t
                         :mem-ptr?-var nil)
    ;; wme80
    ,(gen-write-function :size 80
                         :signed? nil
                         :check-alignment?-var t
                         :mem-ptr?-var nil)
    ;; wme128
    ;; Note: A #GP exception should be thrown here instead of an #AC fault when
    ;; the address is not aligned.  See Intel Manuals, Volume 3, Section 6.15,
    ;; Exception and Interrupt Reference, Interrupt 17 Alignment Check
    ;; Exception (#AC).
    ,(gen-write-function :size 128
                         :signed? nil
                         :check-alignment?-var t
                         :mem-ptr?-var nil)))

(define wme-size
  ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
   (nbytes :type (member 1 2 4 6 8 10 16))
   (eff-addr :type (signed-byte 64))
   (seg-reg :type (integer 0 #.*segment-register-names-len-1*))
   (val :type (integer 0 *))
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :guard (case nbytes
           (1  (n08p val))
           (2  (n16p val))
           (4  (n32p val))
           (6  (n48p val))
           (8  (n64p val))
           (10 (n80p val))
           (16 (n128p val)))
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned value with the specified number of bytes
          to memory via an effective address."
  :long
  "<p>The effective address is translated to a canonical linear address.  If
   this translation is successful and no other errors occur (like alignment
   errors), then @(see wml-size) is called.</p>
   <p>Prior to the effective address translation, we check whether write
   access is allowed.  In 32-bit mode, write access is allowed in data
   segments (DS, ES, FS, GS, and SS) if the W bit in the segment
   descriptor is 1; write access is disallowed in code segments (this is
   not explicitly mentioned in Intel manual, May'18, Volume 3, Section
   3.4.5.1, but it seems reasonable).  In 64-bit mode, the W bit is
   ignored (see Atmel manual, Dec'17, Volume 2, Section 4.8.1); by
   analogy, we allow write access to the code segment as well.
   These checks may be slightly optimized using the invariant that
   SS.W must be 1 when SS is loaded.</p>"
  (b* (((when (and (/= proc-mode #.*64-bit-mode*)
                   (or (= seg-reg #.*cs*)
                       (b* ((attr (loghead
                                   16 (seg-hidden-attri seg-reg x86)))
                            (w (data-segment-descriptor-attributesBits->w
                                attr)))
                         (= w 0)))))
        (mv (list :non-writable-segment eff-addr seg-reg) x86))
       ((mv flg lin-addr) (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
       ((when flg) (mv flg x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml-size nbytes lin-addr val x86))
  :inline t
  :no-function t
  ///

  (defrule wme-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr nbytes mem-ptr?)))
             (equal
              (wme-size #.*64-bit-mode*
                        nbytes eff-addr seg-reg val check-alignment? x86
                        :mem-ptr? mem-ptr?)
              (wml-size nbytes eff-addr val x86))))

  (defrule wme-size-when-64-bit-modep-fs/gs
    (implies (or (equal seg-reg #.*fs*)
                 (equal seg-reg #.*gs*))
             (equal (wme-size #.*64-bit-mode*
                              nbytes eff-addr seg-reg val check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (b* (((mv flg lin-addr)
                          (b* (((mv base & &)
                                (segment-base-and-bounds 0 seg-reg x86))
                               (lin-addr (i64 (+ base (n64 eff-addr)))))
                            (if (canonical-address-p lin-addr)
                                (mv nil lin-addr)
                              (mv (list :non-canonical-address lin-addr) 0))))
                         ((when flg)
                          (mv flg x86))
                         ((unless (or (not check-alignment?)
                                      (address-aligned-p
                                       lin-addr nbytes mem-ptr?)))
                          (mv (list :unaligned-linear-address lin-addr) x86)))
                      (wml-size nbytes lin-addr val x86))))
    :in-theory (e/d (ea-to-la) ()))

  (defthm wme-size-64-bit-unaligned-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of wme-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not
                   (or (not check-alignment?)
                       (address-aligned-p eff-addr nbytes mem-ptr?)))
                  (canonical-address-p eff-addr))
             (equal (wme-size #.*64-bit-mode*
                              nbytes eff-addr seg-reg val check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (list (list :unaligned-linear-address eff-addr) x86)))
    :hints (("Goal" :in-theory (e/d (wme-size) ()))))

  (defthm wme-size-non-canonical-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of rme-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not (canonical-address-p eff-addr)))
             (equal (wme-size #.*64-bit-mode*
                              nbytes eff-addr seg-reg val check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (list (list :non-canonical-address eff-addr) x86)))
    :hints (("Goal" :in-theory (e/d (wme-size) ())))))

(define wime-size
  ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
   (nbytes :type (member 1 2 4 8))
   (eff-addr :type (signed-byte 64))
   (seg-reg :type (integer 0 #.*segment-register-names-len-1*))
   (val :type integer)
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :inline t
  :no-function t
  :guard (case nbytes
           (1  (i08p val))
           (2  (i16p val))
           (4  (i32p val))
           (8  (i64p val)))
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write a signed value with the specified number of bytes
          to memory via an effective address."
  :long
  "<p>The effective address is translated to a canonical linear address.  If
   this translation is successful and no other errors occur (like alignment
   errors), then @(see wiml-size) is called.</p>
   <p>Prior to the effective address translation, we check whether write
   access is allowed.  In 32-bit mode, write access is allowed in data
   segments (DS, ES, FS, GS, and SS) if the W bit in the segment
   descriptor is 1; write access is disallowed in code segments (this is
   not explicitly mentioned in Intel manual, May'18, Volume 3, Section
   3.4.5.1, but it seems reasonable).  In 64-bit mode, the W bit is
   ignored (see Atmel manual, Dec'17, Volume 2, Section 4.8.1); by
   analogy, we allow write access to the code segment as well.
   These checks may be slightly optimized using the invariant that
   SS.W must be 1 when SS is loaded.</p>"
  (b* (((when (and (/= proc-mode #.*64-bit-mode*)
                   (or (= seg-reg #.*cs*)
                       (b* ((attr (loghead
                                   16 (seg-hidden-attri seg-reg x86)))
                            (w (data-segment-descriptor-attributesBits->w
                                attr)))
                         (= w 0)))))
        (mv (list :non-writable-segment eff-addr seg-reg) x86))
       ((mv flg lin-addr) (ea-to-la proc-mode eff-addr seg-reg nbytes x86))
       ((when flg) (mv flg x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wiml-size nbytes lin-addr val x86))

  ///

  (defrule wime-size-when-64-bit-modep-and-not-fs/gs
    (implies
     (and (not (equal seg-reg #.*fs*))
          (not (equal seg-reg #.*gs*))
          (canonical-address-p eff-addr)
          (or (not check-alignment?)
              (address-aligned-p eff-addr nbytes mem-ptr?)))
     (equal (wime-size #.*64-bit-mode*
                       nbytes eff-addr seg-reg val check-alignment? x86
                       :mem-ptr? mem-ptr?)
            (wiml-size nbytes eff-addr val x86))))

  (defrule wime-size-when-64-bit-modep-fs/gs
    (implies (or (equal seg-reg #.*fs*)
                 (equal seg-reg #.*gs*))
             (equal (wime-size #.*64-bit-mode*
                               nbytes eff-addr seg-reg val check-alignment? x86
                               :mem-ptr? mem-ptr?)
                    (b* (((mv flg lin-addr)
                          (b* (((mv base & &)
                                (segment-base-and-bounds 0 seg-reg x86))
                               (lin-addr (i64 (+ base (n64 eff-addr)))))
                            (if (canonical-address-p lin-addr)
                                (mv nil lin-addr)
                              (mv (list :non-canonical-address lin-addr) 0))))
                         ((when flg)
                          (mv flg x86))
                         ((unless (or (not check-alignment?)
                                      (address-aligned-p
                                       lin-addr nbytes mem-ptr?)))
                          (mv (list :unaligned-linear-address lin-addr) x86)))
                      (wiml-size nbytes lin-addr val x86))))
    :in-theory (e/d (ea-to-la) ()))

  (defthm wime-size-unaligned-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of wime-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not
                   (or (not check-alignment?)
                       (address-aligned-p eff-addr nbytes mem-ptr?)))
                  (canonical-address-p eff-addr))
             (equal (wime-size #.*64-bit-mode*
                               nbytes eff-addr seg-reg val check-alignment? x86
                               :mem-ptr? mem-ptr?)
                    (list (list :unaligned-linear-address eff-addr) x86))))

  (defthm wime-size-non-canonical-when-64-bit-modep-and-not-fs/gs
    ;; [Shilpi] Added for guard proof obligations generated from the expansion
    ;; of rme-size-opt.
    (implies (and (not (equal seg-reg #.*fs*))
                  (not (equal seg-reg #.*gs*))
                  (not (canonical-address-p eff-addr)))
             (equal (wime-size #.*64-bit-mode*
                               nbytes eff-addr seg-reg val check-alignment? x86
                               :mem-ptr? mem-ptr?)
                    (list (list :non-canonical-address eff-addr) x86)))
    :hints (("Goal" :in-theory (e/d (wime-size) ())))))

;; ----------------------------------------------------------------------

;; Macro definitions for efficient 64-bit mode execution:

;; The idea here is that in 64-bit mode, when we already know that eff-addr is
;; a canonical address (e.g., because it is produced by a function that always
;; returns a canonical address) and if the seg-reg is *cs* (which is the common
;; case), then we needn't check for canonicity of eff-addr.

(defmacro rme08-opt (proc-mode eff-addr seg-reg r-x x86
                               &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rme08 ,proc-mode ,eff-addr ,seg-reg ,r-x ,x86)
    :exec
    (if (eql proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86)))
          (rml08 lin-addr ,r-x ,x86))
      (rme08 ,proc-mode ,eff-addr ,seg-reg ,r-x ,x86))))

(defmacro rime08-opt (proc-mode eff-addr seg-reg r-x x86
                                &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rime08 ,proc-mode ,eff-addr ,seg-reg ,r-x ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86)))
          (riml08 lin-addr ,r-x ,x86))
      (rime08 ,proc-mode ,eff-addr ,seg-reg ,r-x ,x86))))

(defmacro wme08-opt (proc-mode eff-addr seg-reg val x86
                               &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wme08 ,proc-mode ,eff-addr ,seg-reg ,val ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86)))
          (wml08 lin-addr ,val ,x86))
      (wme08 ,proc-mode ,eff-addr ,seg-reg ,val ,x86))))

(defmacro wime08-opt (proc-mode eff-addr seg-reg val x86
                                &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wime08 ,proc-mode ,eff-addr ,seg-reg ,val ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86)))
          (wiml08 lin-addr ,val ,x86))
      (wime08 ,proc-mode ,eff-addr ,seg-reg ,val ,x86))))

(defmacro rme16-opt (proc-mode eff-addr seg-reg r-x check-alignment? x86
                               &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rme16 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 2 nil)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (rml16 lin-addr ,r-x ,x86))
      (rme16 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86))))

(defmacro rime16-opt (proc-mode eff-addr seg-reg r-x check-alignment? x86
                                &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rime16 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 2 nil)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (riml16 lin-addr ,r-x ,x86))
      (rime16 ,proc-mode ,eff-addr ,seg-reg ,r-x ,x86))))

(defmacro wme16-opt (proc-mode eff-addr seg-reg val check-alignment? x86
                               &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wme16 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 2 nil)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (wml16 lin-addr ,val ,x86))
      (wme16 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86))))

(defmacro wime16-opt (proc-mode eff-addr seg-reg val check-alignment? x86
                                &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wime16 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 2 nil)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (wiml16 lin-addr ,val ,x86))
      (wime16 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86))))

(defmacro rme32-opt (proc-mode eff-addr seg-reg r-x check-alignment? x86
                               &key
                               (mem-ptr? 'nil)
                               (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rme32 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
           :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 4 ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (rml32 lin-addr ,r-x ,x86))
      (rme32 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
             :mem-ptr? ,mem-ptr?))))

(defmacro rime32-opt (proc-mode eff-addr seg-reg r-x check-alignment? x86
                                &key
                                (mem-ptr? 'nil)
                                (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rime32 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
            :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 4 ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (riml32 lin-addr ,r-x ,x86))
      (rime32 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
              :mem-ptr? ,mem-ptr?))))

(defmacro wme32-opt (proc-mode eff-addr seg-reg val check-alignment? x86
                               &key
                               (mem-ptr? 'nil)
                               (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wme32 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
           :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 4 ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) x86)))
          (wml32 lin-addr ,val ,x86))
      (wme32 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
             :mem-ptr? ,mem-ptr?))))

(defmacro wime32-opt (proc-mode eff-addr seg-reg val check-alignment? x86
                                &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wime32 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 4 nil)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (wiml32 lin-addr ,val ,x86))
      (wime32 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86))))

(defmacro rme48-opt (proc-mode eff-addr seg-reg r-x check-alignment? x86
                               &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rme48 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 6 t)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (rml48 lin-addr ,r-x ,x86))
      (rme48 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86))))

(defmacro wme48-opt (proc-mode eff-addr seg-reg val check-alignment? x86
                               &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wme48 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 6 t)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (wml48 lin-addr ,val ,x86))
      (wme48 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86))))

(defmacro rme64-opt (proc-mode eff-addr seg-reg r-x check-alignment? x86
                               &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rme64 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 8 nil)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (rml64 lin-addr ,r-x ,x86))
      (rme64 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86))))

(defmacro rime64-opt (proc-mode eff-addr seg-reg r-x check-alignment? x86
                                &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (rime64 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 8 nil)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (riml64 lin-addr ,r-x ,x86))
      (rime64 ,proc-mode ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86))))

(defmacro wme64-opt (proc-mode eff-addr seg-reg val check-alignment? x86
                               &key
                               (mem-ptr? 'nil)
                               (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wme64 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
           :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr 8 ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) x86)))
          (wml64 lin-addr ,val ,x86))
      (wme64 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
             :mem-ptr? ,mem-ptr?))))

(defmacro wime64-opt (proc-mode eff-addr seg-reg val check-alignment? x86
                                &key (check-canonicity 'nil))
  (declare (xargs :guard (natp seg-reg)))
  `(mbe
    :logic
    (wime64 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              ,(if (or (eql seg-reg #.*fs*)
                       (eql seg-reg #.*gs*))
                   `(b* (((mv (the (unsigned-byte 64) base) & &)
                          (segment-base-and-bounds 0 ,seg-reg ,x86))
                         ((the (signed-byte 64) lin-addr)
                          (i64 (+ base (n64 ,eff-addr)))))
                      (if (canonical-address-p lin-addr)
                          (mv nil lin-addr)
                        (mv (list :non-canonical-address lin-addr) 0)))
                 (if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr ,8 nil)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (wiml64 lin-addr ,val ,x86))
      (wime64 ,proc-mode ,eff-addr ,seg-reg ,val ,check-alignment? ,x86))))

;; Note that unlike the macros above, the generic rme/wme*-size macros work for
;; all kinds of seg-reg values.

(defmacro rme-size-opt
    (proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86
               &key
               (mem-ptr? 'nil)
               (check-canonicity 'nil))
  `(mbe
    :logic
    (rme-size
     ,proc-mode ,nbytes ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
     :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              (if (or (eql ,seg-reg #.*fs*)
                      (eql ,seg-reg #.*gs*))
                  (b* (((mv (the (unsigned-byte 64) base) & &)
                        (segment-base-and-bounds 0 ,seg-reg ,x86))
                       ((the (signed-byte 64) lin-addr)
                        (i64 (+ base (n64 ,eff-addr)))))
                    (if (canonical-address-p lin-addr)
                        (mv nil lin-addr)
                      (mv (list :non-canonical-address lin-addr) 0)))
                ,(if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr ,nbytes ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (rml-size ,nbytes lin-addr ,r-x ,x86))
      (rme-size
       ,proc-mode ,nbytes ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
       :mem-ptr? ,mem-ptr?))))

(defmacro rime-size-opt
    (proc-mode nbytes eff-addr seg-reg r-x check-alignment? x86
               &key
               (mem-ptr? 'nil)
               (check-canonicity 'nil))
  `(mbe
    :logic
    (rime-size
     ,proc-mode ,nbytes ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
     :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              (if (or (eql ,seg-reg #.*fs*)
                      (eql ,seg-reg #.*gs*))
                  (b* (((mv (the (unsigned-byte 64) base) & &)
                        (segment-base-and-bounds 0 ,seg-reg ,x86))
                       ((the (signed-byte 64) lin-addr)
                        (i64 (+ base (n64 ,eff-addr)))))
                    (if (canonical-address-p lin-addr)
                        (mv nil lin-addr)
                      (mv (list :non-canonical-address lin-addr) 0)))
                ,(if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg 0 ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr ,nbytes ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) 0 ,x86)))
          (riml-size ,nbytes lin-addr ,r-x ,x86))
      (rime-size
       ,proc-mode ,nbytes ,eff-addr ,seg-reg ,r-x ,check-alignment? ,x86
       :mem-ptr? ,mem-ptr?))))

(defmacro wme-size-opt
    (proc-mode nbytes eff-addr seg-reg val check-alignment? x86
               &key
               (mem-ptr? 'nil)
               (check-canonicity 'nil))
  `(mbe
    :logic
    (wme-size
     ,proc-mode ,nbytes ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
     :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              (if (or (eql ,seg-reg #.*fs*)
                      (eql ,seg-reg #.*gs*))
                  (b* (((mv (the (unsigned-byte 64) base) & &)
                        (segment-base-and-bounds 0 ,seg-reg ,x86))
                       ((the (signed-byte 64) lin-addr)
                        (i64 (+ base (n64 ,eff-addr)))))
                    (if (canonical-address-p lin-addr)
                        (mv nil lin-addr)
                      (mv (list :non-canonical-address lin-addr) 0)))
                ,(if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr ,nbytes ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (wml-size ,nbytes lin-addr ,val ,x86))
      (wme-size
       ,proc-mode ,nbytes ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
       :mem-ptr? ,mem-ptr?))))

(defmacro wime-size-opt
    (proc-mode nbytes eff-addr seg-reg val check-alignment? x86
               &key
               (mem-ptr? 'nil)
               (check-canonicity 'nil))
  `(mbe
    :logic
    (wime-size
     ,proc-mode ,nbytes ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
     :mem-ptr? ,mem-ptr?)
    :exec
    (if (equal ,proc-mode #.*64-bit-mode*)
        (b* (((mv flg (the (signed-byte #.*max-linear-address-size*) lin-addr))
              (if (or (eql ,seg-reg #.*fs*)
                      (eql ,seg-reg #.*gs*))
                  (b* (((mv (the (unsigned-byte 64) base) & &)
                        (segment-base-and-bounds 0 ,seg-reg ,x86))
                       ((the (signed-byte 64) lin-addr)
                        (i64 (+ base (n64 ,eff-addr)))))
                    (if (canonical-address-p lin-addr)
                        (mv nil lin-addr)
                      (mv (list :non-canonical-address lin-addr) 0)))
                ,(if check-canonicity
                     `(b* (((unless (canonical-address-p ,eff-addr))
                            (mv (list :non-canonical-address ,eff-addr) 0)))
                        (mv nil ,eff-addr))
                   `(mv nil ,eff-addr))))
             ((when flg)
              (mv flg ,x86))
             ((unless (or (not ,check-alignment?)
                          (address-aligned-p lin-addr ,nbytes ,mem-ptr?)))
              (mv (list :unaligned-linear-address lin-addr) ,x86)))
          (wiml-size ,nbytes lin-addr ,val ,x86))
      (wime-size
       ,proc-mode ,nbytes ,eff-addr ,seg-reg ,val ,check-alignment? ,x86
       :mem-ptr? ,mem-ptr?))))

;; ----------------------------------------------------------------------
