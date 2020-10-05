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

(defun elf-load-text-section (el::elf x86)  
  (declare (xargs :stobjs (el::elf x86)))
  (b* ((text-section-addr (el::@text-addr el::elf))
       (text-section-bytes (el::@text-bytes el::elf))
       (- (if (equal text-section-bytes nil)
              (cw "~%Text section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p text-section-addr))
                  (not (canonical-address-p (+ text-section-addr
                                               (len text-section-bytes))))))
        (mv (cons 'text-section-addr text-section-addr) x86)))
    (write-bytes-to-memory text-section-addr text-section-bytes x86)))

(defun elf-load-data-section (el::elf x86)
  (declare (xargs :stobjs (el::elf x86)))
  (b* ((data-section-addr (el::@data-addr el::elf))
       (data-section-bytes (el::@data-bytes el::elf))
       (- (if (equal data-section-bytes nil)
              (cw "~%Data section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p data-section-addr))
                  (not (canonical-address-p (+ (len
                                                data-section-bytes)
                                               data-section-addr)))))
        (mv (cons 'data-section-addr data-section-addr) x86)))
    (write-bytes-to-memory data-section-addr data-section-bytes x86)))

(defun elf-load-bss-section (el::elf x86)
  (declare (xargs :stobjs (el::elf x86)))
  (b* ((bss-section-addr (el::@bss-addr el::elf))
       (bss-section-bytes (el::@bss-bytes el::elf))
       (- (if (equal bss-section-bytes nil)
              (cw "~%Bss section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p bss-section-addr))
                  (not (canonical-address-p (+ (len
                                                bss-section-bytes)
                                               bss-section-addr)))))
        (mv (cons 'bss-section-addr bss-section-addr) x86)))
    (write-bytes-to-memory bss-section-addr bss-section-bytes x86)))

(defun elf-load-rodata-section (el::elf x86)
  (declare (xargs :stobjs (el::elf x86)))
  (b* ((rodata-section-addr (el::@rodata-addr el::elf))
       (rodata-section-bytes (el::@rodata-bytes el::elf))
       (- (if (equal rodata-section-bytes nil)
              (cw "~%Rodata section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p rodata-section-addr))
                  (not (canonical-address-p (+ (len
                                                rodata-section-bytes)
                                               rodata-section-addr)))))
        (mv (cons 'rodata-section-addr rodata-section-addr) x86)))
    (write-bytes-to-memory rodata-section-addr rodata-section-bytes x86)))

;;----------------------------------------------------------------------
;; Functions to load the x86 stobj based on the information in the
;; mach-o stobj:
;; ----------------------------------------------------------------------

;; (el::populate-mach-o-contents <file-byte-list> mach-o state)

;; (load-qwords-into-physical-memory-list *1-gig-page-tables* x86)

(defun mach-o-load-text-section (el::mach-o x86)
  (declare (xargs :stobjs (el::mach-o x86)))
  (b* ((text-sec-load-addr (el::@TEXT-text-section-addr el::mach-o))
       (text-section-bytes (el::@TEXT-text-section-bytes el::mach-o))
       (- (if (equal text-section-bytes nil)
              (cw "~%Text section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p text-sec-load-addr))
                  (not (canonical-address-p (+ text-sec-load-addr
                                               (len text-section-bytes))))))
        (mv (cons 'text-sec-load-addr text-sec-load-addr) x86)))
    (write-bytes-to-memory text-sec-load-addr text-section-bytes x86)))

(defun mach-o-load-data-section (el::mach-o x86)
  (declare (xargs :stobjs (el::mach-o x86)))
  (b* ((data-sec-load-addr (el::@DATA-data-section-addr el::mach-o))
       (data-section-bytes (el::@DATA-data-section-bytes el::mach-o))
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

(mach-o-load-text-section el::mach-o x86)

||#

;; ----------------------------------------------------------------------

(define binary-file-load-fn ((filename stringp)
                             el::elf
                             el::mach-o x86 state
                             &key
                             ((elf booleanp) 't)
                             ((mach-o booleanp) 'nil))
  :parents (program-execution)
  :short "Function to read in an ELF or Mach-O binary and load text
  and data sections into the x86 ISA model's memory"
  :long "<p>The following macro makes it convenient to call this
  function to load a program:</p>
<code> (binary-file-load \"fib.o\" :elf t) ;; or :mach-o t</code>"
  :returns (mv alst
               (new-elf el::good-elf-p :hyp (el::elfp el::good-elf-p))
               (new-mach-o el::good-mach-o-p :hyp (el::mach-op el::good-mach-o-p))
               (new-x86 x86p :hyp (x86p x86))
               state)
  (cond
   ((and elf (not mach-o))
    (b* (((mv header section-headers el::elf state)
          (el::populate-elf filename el::elf state))
         ((mv flg0 x86)
          (elf-load-text-section el::elf x86))
         ((mv flg1 x86)
          (elf-load-data-section el::elf x86))
         ((when (or flg0 flg1))
          (prog2$
           (raise "[ELF]: Error encountered while loading sections in the x86 model's memory!~%")
           (mv t el::elf el::mach-o x86 state))))
      (mv (list (cons :HEADER header)
                (cons :SECTION-HEADERS section-headers))
          el::elf el::mach-o x86 state)))
   ((and mach-o (not elf))
    (b* (((mv alst el::mach-o state)
          (el::populate-mach-o filename el::mach-o state))
         ((mv flg0 x86)
          (mach-o-load-text-section el::mach-o x86))
         ((mv flg1 x86)
          (mach-o-load-data-section el::mach-o x86))
         ((when (or flg0 flg1))
          (prog2$
           (raise "[Mach-O]: Error encountered while loading sections in the x86 model's memory!~%")
           (mv t el::elf el::mach-o x86 state))))
      (mv alst el::elf el::mach-o x86 state)))
   (t
    (prog2$
     (raise "~%We support only ELF and Mach-O files for now! Use this function with either :elf t ~
 or :mach-o t.~%")
     (mv nil el::elf el::mach-o x86 state)))))
  
(defmacro binary-file-load (filename &key (elf 't) (mach-o 'nil))
  `(binary-file-load-fn ,filename el::elf el::mach-o x86 state :elf ,elf :mach-o ,mach-o))

;; ----------------------------------------------------------------------
