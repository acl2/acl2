; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Shilpi Goel
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
; Shilpi Goel         <shigoel@gmail.com>

(in-package "X86ISA")
(include-book "init-page-tables" :ttags :all)
(include-book "projects/execloader/elf-reader" :dir :system)
(include-book "projects/execloader/mach-o-reader" :dir :system)

(local (xdoc::set-default-parents program-execution))

;; ----------------------------------------------------------------------

(local (in-theory (e/d () (unsigned-byte-p))))

(local
 (defthm canonical-address-p-implies-acl2-numberp
   (implies (canonical-address-p x)
            (acl2-numberp x))))

(local
 (defthm acl2-byte-listp-and-x86isa-byte-listp
   (implies (acl2::byte-listp xs)
            (x86isa::byte-listp xs))
   :hints (("Goal" :in-theory (e/d (x86isa::byte-listp
                                    acl2::byte-listp)
                                   ())))))

;;----------------------------------------------------------------------
;; Functions to load the x86 stobj based on the information in the
;; elf stobj:
;;----------------------------------------------------------------------

(define load-elf-sections ((sections exld::section-info-list-p)
                           x86)
  :returns (mv flg
               (new-x86 x86p :hyp (x86p x86)))
  (b* (((when (atom sections)) (mv nil x86))
       ((mv flg x86) (load-elf-sections (cdr sections) x86))
       ((exld::section-info section) (car sections))
       ((exld::elf-section-header header) section.header)
       ((unless section.bytes)
        (prog2$
         (cw "~%Empty ~s0 section! Nothing loaded.~%" header.name-str)
         (mv flg x86))))
    ;; Source: https://refspecs.linuxfoundation.org/elf/elf.pdf
    ;; Section Attribute Flags, sh_flags

    ;; SHF_WRITE 0x1
    ;; The section contains data that should be writable during
    ;; process execution.

    ;; SHF_ALLOC 0x2
    ;; The section occupies memory during process execution. Some
    ;; control sections do not reside in the memory image of an
    ;; object file; this attribute is off for those sections.

    ;; SHF_EXECINSTR 0x4
    ;; The section contains executable machine instructions.

    ;; SHF_MASKPROC 0xf0000000
    ;; All bits included in this mask are reserved for
    ;; processor-specific semantics.
    (if (logbitp 1 header.flags) ;; SHF_ALLOC
        (if (and (canonical-address-p header.addr)
                 (canonical-address-p (+ (len section.bytes) header.addr)))
            (write-bytes-to-memory header.addr section.bytes x86)
          (mv (cons header.name-str flg) x86))
      (prog2$
       (cw "~%Section ~s0 is not marked as SHF_ALLOC in its ELF section header, ~
 so we don't allocate memory for it in the RV model.~%" header.name-str)
       (mv nil x86)))))

;;----------------------------------------------------------------------
;; Functions to load the x86 stobj based on the information in the
;; mach-o stobj:
;; ----------------------------------------------------------------------

;; (exld::populate-mach-o-contents <file-byte-list> mach-o state)

;; (load-qwords-into-physical-memory-list *1-gig-page-tables* x86)

(defun mach-o-load-text-section (exld::mach-o x86)
  (declare (xargs :stobjs (exld::mach-o x86)))
  (b* ((text-sec-load-addr (exld::@TEXT-text-section-addr exld::mach-o))
       (text-section-bytes (exld::@TEXT-text-section-bytes exld::mach-o))
       (- (if (equal text-section-bytes nil)
              (cw "~%Text section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p text-sec-load-addr))
                  (not (canonical-address-p (+ text-sec-load-addr
                                               (len text-section-bytes))))))
        (mv (cons 'text-sec-load-addr text-sec-load-addr) x86)))
    (write-bytes-to-memory text-sec-load-addr text-section-bytes x86)))

(defun mach-o-load-data-section (exld::mach-o x86)
  (declare (xargs :stobjs (exld::mach-o x86)))
  (b* ((data-sec-load-addr (exld::@DATA-data-section-addr exld::mach-o))
       (data-section-bytes (exld::@DATA-data-section-bytes exld::mach-o))
       (- (if (equal data-section-bytes nil)
              (cw "~%Data section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p data-sec-load-addr))
                  (not (canonical-address-p (+ (len
                                                data-section-bytes)
                                               data-sec-load-addr)))))
        (mv (cons 'data-sec-load-addr data-sec-load-addr) x86)))
    (write-bytes-to-memory data-sec-load-addr data-section-bytes x86)))

#||

(let* ((cr0        (ctri *cr0*       x86))
       (cr4        (ctri *cr4*       x86))
       (ia32e-efer (msri *ia32_efer-idx* x86))

       (cr0        (!cr0Bits>pg         1 cr0))
       (cr4        (!cr4Bits->pae       1 cr4))
       (ia32e-efer (!ia32_eferBits->lme 1 ia32e-efer))

       (x86 (!ctri *cr0*           cr0        x86))
       (x86 (!ctri *cr4*           cr4        x86))
       (x86 (!msri *ia32_efer-idx* ia32e-efer x86))

       (x86 (!ctri *cr3* #x0 x86)))
  x86)

(mach-o-load-text-section exld::mach-o x86)

||#

;; ----------------------------------------------------------------------

(define binary-file-load-fn ((filename stringp)
                             exld::elf
                             exld::mach-o x86 state
                             &key
                             ((elf booleanp) 't)
                             ((mach-o booleanp) 'nil))
  :parents (program-execution)
  :short "Function to read in an ELF or Mach-O binary and load text
  and data sections into the x86 ISA model's memory"
  :long "<p>The following macro makes it convenient to call this
  function to load a program:</p>
<code> (binary-file-load \"fib.o\" :elf t) ;; or :mach-o t</code>"
  :returns (mv (new-elf exld::good-elf-p :hyp (exld::elfp exld::good-elf-p))
               (new-mach-o exld::good-mach-o-p :hyp (exld::mach-op exld::good-mach-o-p))
               (new-x86 x86p :hyp (x86p x86))
               state)
  (cond
   ((and elf (not mach-o))
    (b* (((mv exld::elf state)
          (exld::populate-elf filename exld::elf state))
         ((mv flg x86)
          (load-elf-sections (exld::@sections exld::elf) x86))
         ((when flg)
          (prog2$
           (raise "[ELF]: Error encountered while loading sections in the x86 model's memory!~%")
           (mv exld::elf exld::mach-o x86 state))))
      (mv exld::elf exld::mach-o x86 state)))
   ((and mach-o (not elf))
    (b* (((mv ?alst exld::mach-o state)
          (exld::populate-mach-o filename exld::mach-o state))
         ((mv flg0 x86)
          (mach-o-load-text-section exld::mach-o x86))
         ((mv flg1 x86)
          (mach-o-load-data-section exld::mach-o x86))
         ((when (or flg0 flg1))
          (prog2$
           (raise "[Mach-O]: Error encountered while loading sections in the x86 model's memory!~%")
           (mv exld::elf exld::mach-o x86 state))))
      (mv exld::elf exld::mach-o x86 state)))
   (t
    (prog2$
     (raise "~%We support only ELF and Mach-O files for now! Use this function with either :elf t ~
 or :mach-o t.~%")
     (mv exld::elf exld::mach-o x86 state)))))

(defmacro binary-file-load (filename &key (elf 't) (mach-o 'nil))
  `(binary-file-load-fn ,filename exld::elf exld::mach-o x86 state :elf ,elf :mach-o ,mach-o))

;; ----------------------------------------------------------------------
