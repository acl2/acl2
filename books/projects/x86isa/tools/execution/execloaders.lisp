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

(local (include-book "std/io/top" :dir :system))

(local (defthm unsigned-byte-p-8-read-byte$
               (implies (and (state-p1 state)
                             (open-input-channel-p1 channel :byte state)
                             (mv-nth 0 (read-byte$ channel state)))
                 (unsigned-byte-p 8 (mv-nth 0 (read-byte$ channel state))))
               :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

(define read-channel-into-byte-list1 ((channel symbolp)
                                      (limit natp)
                                      acc
                                      state)
  :guard (open-input-channel-p channel :byte state)
  :returns (mv (bytes byte-listp
                      :hyp (and (state-p1 state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state)
                                (byte-listp acc))
                      :hints (("Goal" :in-theory (enable byte-listp))))
               (state state-p1 :hyp (and (state-p1 state)
                                         (symbolp channel)
                                         (open-input-channel-p1 channel :byte state))))
  (if (zp limit)
    (mv acc state)
    (b* (((mv current-byte state) (read-byte$ channel state)))
        (if (not current-byte)
          (mv acc state)
          (read-channel-into-byte-list1 channel (1- limit) (cons current-byte acc) state))))
  ///
  (defthm read-channel-into-byte-list1-leaves-channel-open
          (implies (open-input-channel-p1 channel :byte state)
                   (open-input-channel-p1 channel :byte
                                          (mv-nth 1 (read-channel-into-byte-list1 channel limit acc state))))))

;; Read from the given byte channel into the returned list. Reads limit
;; bytes or until EOF, whichever comes first.
(defmacro read-channel-into-byte-list (channel limit state)
  `(b* (((mv result state) (read-channel-into-byte-list1 ,channel ,limit nil ,state)))
      (mv (reverse result) state)))

(define chars-to-c-str ((char-lst character-listp))
  :returns (c-str byte-listp :hints (("Goal" :in-theory (enable unsigned-byte-p))))
  (if (mbt (character-listp char-lst))
    (if (not char-lst)
     '(0)
     (cons (char-code (car char-lst))
           (chars-to-c-str (cdr char-lst))))
    nil))

(define string-to-c-str ((str stringp))
  :returns (c-str byte-listp)
  (b* ((lst (coerce str 'list)))
      (chars-to-c-str lst)))

(defmacro pack-u (value bytes)
  (if (equal bytes 0)
    nil
    `(cons (logand #xFF ,value) (pack-u (ash ,value -8) ,(- bytes 1)))))

(define pack-u32 ((val n32p))
  :returns (bytes byte-listp)
  (pack-u val 4)
  ///
  (defthm len-of-pack-u32-is-4
          (equal (len (pack-u32 x))
                 4)))

(define pack-u64 ((val n64p))
  :returns (bytes byte-listp)
  (pack-u val 8)
  ///
  (defthm len-of-pack-u64-is-8
          (equal (len (pack-u64 x))
                 8)))

;; From linux/arch/x86/include/asm/segment.h
;; /*
;;  * Constructor for a conventional segment GDT (or LDT) entry.
;;  * This is a macro so it can be used in initializers.
;;  */
;; #define GDT_ENTRY(flags, base, limit)			\
;; 	((((base)  & _AC(0xff000000,ULL)) << (56-24)) |	\
;; 	 (((flags) & _AC(0x0000f0ff,ULL)) << 40) |	\
;; 	 (((limit) & _AC(0x000f0000,ULL)) << (48-16)) |	\
;; 	 (((base)  & _AC(0x00ffffff,ULL)) << 16) |	\
;; 	 (((limit) & _AC(0x0000ffff,ULL))))
(define gdt-entry ((flags :type (unsigned-byte 16))
                   (base :type (unsigned-byte 32))
                   (limit :type (unsigned-byte 20)))
  :returns (entry n64p)
  (logior (ash (logand base #xff000000) (- 56 24))
          (ash (logand flags #x0000f0ff) 40)
          (ash (logand limit #x000f0000) (- 48 16))
          (ash (logand base #x00ffffff) 16)
          (logand limit #x0000ffff)))

(local (defthm reverse-of-byte-listp-is-byte-listp
               (implies (byte-listp x)
                        (byte-listp (acl2::rev x)))))

(local (defthm byte-listp-is-true-listp (implies (byte-listp x)
                                                 (true-listp x))))

(define load-file-into-memory ((filename stringp)
                               (ptr canonical-address-p)
                               x86
                               state)
  :returns (mv (file-contents byte-listp :hyp (and (stringp filename)
                                                   (canonical-address-p ptr)
                                                   (state-p1 state)))
               (x86 x86p :hyp (x86p x86))
               (state state-p1 :hyp (and (stringp filename)
                                         (state-p1 state))))
  (b* (((mv channel state) (open-input-channel filename :byte state))
       ((when (not channel)) (mv nil x86 state))
       ((mv file-contents state) (read-channel-into-byte-list channel (1- (ash 1 60)) state))
       ((unless (canonical-address-p (+ ptr (len file-contents)))) (mv nil x86 state))
       ((mv & x86) (write-bytes-to-memory ptr file-contents x86)) 
       (state (close-input-channel channel state)))
      (mv file-contents x86 state)))

(define init-zero-page ((zero-page-ptr canonical-address-p)
                        (command-line-ptr canonical-address-p)
                        (disk-image-ptr canonical-address-p)
                        (disk-image-size natp)
                        (kernel-ptr n32p)
                        (kernel-image byte-listp)
                        x86)
  :guard (and (canonical-address-p (+ zero-page-ptr #xFFF)))
  (b* (((unless (> (len kernel-image) #x211)) x86) ;; Make sure the kernel-image has the initial loadflags
       ((unless (> (len kernel-image) (+ #x26c #x1f1))) x86) ;; Make sure the kernel image has the setup header
       (setup-header (take #x26c (nthcdr #x1f1 kernel-image)))
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x1f1) setup-header x86))
       ;; Set various setup-header fields (all fields are little endian)
       ;; Set vid_mode to normal (0xffff)
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x1fa) '(#xff #xff) x86))
       ;; Set type_of_loader
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x210) '(#xff) x86))
       ;; Set loadflags
       ;; This is a bit field. We want to set QUIET_FLAG (bit 5) to 0 (print early messages)
       ;; and set CAN_USE_HEAP (bit 7) to 0 (i.e. heap_end_ptr is invalid)
       (loadflags (logand (nth #x211 kernel-image) #x5F))
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x211) (list loadflags) x86))
       ;; We (may be) loading the kernel at a nonstandard address, so we may need to relocate code32_start.
       ;; kernel-ptr could theoretically be a 64-bit pointer and this is a 32-bit field, so I don't
       ;; think it is relevant if we're launching the kernel through the 64-bit entrypoint, but I set
       ;; it anyways.
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x214) (pack-u32 kernel-ptr) x86))
       ;; Set ramdisk_image
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x218) (pack-u32 (logand #xFFFFFFFF disk-image-ptr)) x86))
       ;; Set ramdisk_size
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x21c) (pack-u32 (logand #xFFFFFFFF disk-image-size)) x86))
       ;; Linux docs state setting heap_end_ptr is obligatory, but we CAN_USE_HEAP to 0, so I don't think we have to
       ;; Set cmd_line_ptr
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x228) (pack-u32 (logand #xFFFFFFFF command-line-ptr)) x86))
       ;; Theoretically, we should be making sure we're loading the kernel at a properly aligned address
       ;; That being said, the kernel I am looking at while building this seems to have a preferred alignment of 0x1.
       ;; However, it also seems to have a min_alignment of 0x15 or 2^21, which is clearly contradictory.
       ;; I'm going to hope loading at 0x100000 is fine

       ;; boot_params is now populated

       ;; We need to fill out the rest of the zero page. It isn't nearly as well documented.
       ;; I'm going to hope we can get away with leaving most of this info zeroed out
       ;; Lots of it involves info about things we don't have (like a screen or BIOS).
       ;; Set ext_ramdisk_image
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x0c0) (pack-u32 (logand #xFFFFFFFF (ash disk-image-ptr -32))) x86))
       ;; Set ext_ramdisk_size
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x0c4) (pack-u32 (logand #xFFFFFFFF (ash disk-image-size -32))) x86))
       ;; Set ext_cmd_line_ptr
       ((mv & x86) (write-bytes-to-memory (+ zero-page-ptr #x0c8) (pack-u32 (logand #xFFFFFFFF (ash command-line-ptr -32))) x86)))
      x86))

;; ----------------------------------------------------------------------
;; Load linux. We load a linux kernel image (i.e. vmlinuz),
;; a compressed cpio ram disk image, and the kernel command line into
;; memory. We then setup the various options the kernel expects to be set
;; in memory. We then setup the state in the way the kernel expects and
;; then jump to the kernel 64-bit entrypoint.
;; Run (init-sys-view #x10000000 x86) to setup paging and set model to system view before running this function
(define linux-load ((kernel-image-filename stringp)
                    (disk-image-filename stringp)
                    (command-line stringp)
                    x86
                    state)
  :guard-debug t
  (b* (;; Enable some features in cr0
       (x86 (!ctri 0 (logior #x60000010 ;; initial value of cr0 using vmx on an i7 10700k
                             (ash 1 0)  ;; Protected mode enable
                             (ash 1 31) ;; paging enable
                             ) x86))

       (kernel-ptr #x1000000)
       ((mv kernel-image x86 state) (load-file-into-memory kernel-image-filename kernel-ptr x86 state))

       (zero-page-ptr #x1000)
       (gdt-ptr (+ zero-page-ptr #x1000))
       (gdt-size #x20)
       (command-line-ptr (+ gdt-ptr gdt-size))
       (disk-image-ptr #x100000)

       ;; Setup command line
       (command-line-c-str (string-to-c-str command-line))
       ((unless (canonical-address-p (+ command-line-ptr (len command-line-c-str)))) (mv x86 state))
       ((mv & x86) (write-bytes-to-memory command-line-ptr command-line-c-str x86))

       ((mv disk-image x86 state) (load-file-into-memory disk-image-filename disk-image-ptr x86 state))
       (disk-image-size (len disk-image))

       ;; Setup Zero page

       ;; We assume the memory is zero initialized on loading
       ;; The zero page is a struct boot_params as defined in
       ;; arch/x86/include/uapi/asm/bootparam.h in the linux source
       ;; Copy over the setup header from the kernel image
       (x86 (init-zero-page zero-page-ptr command-line-ptr disk-image-ptr disk-image-size kernel-ptr kernel-image x86))

       ;; From https://www.kernel.org/doc/html/latest/arch/x86/boot.html
       ;;
       ;; In 64-bit boot protocol, the kernel is started by jumping to the
       ;; 64-bit kernel entry point, which is the start address of loaded 64-bit
       ;; kernel plus 0x200.
       ;;
       ;; At entry, the CPU must be in 64-bit mode with paging enabled. The
       ;; range with setup_header.init_size from start address of loaded kernel
       ;; and zero page and command line buffer get ident mapping; a GDT must be
       ;; loaded with the descriptors for selectors __BOOT_CS(0x10) and
       ;; __BOOT_DS(0x18); both descriptors must be 4G flat segment; __BOOT_CS
       ;; must have execute/read permission, and __BOOT_DS must have read/write
       ;; permission; CS must be __BOOT_CS and DS, ES, SS must be __BOOT_DS;
       ;; interrupt must be disabled; %rsi must hold the base address of the
       ;; struct boot_params.

       ;; Setup GDT
       (cs-descriptor (gdt-entry #xa09b 0 #xfffff))
       ((mv & x86) (write-bytes-to-memory (+ gdt-ptr #x10) (pack-u64 cs-descriptor) x86))
       (ds-descriptor (gdt-entry #xc093 0 #xfffff))
       ((mv & x86) (write-bytes-to-memory (+ gdt-ptr #x18) (pack-u64 ds-descriptor) x86))
       (x86 (!stri *gdtr* (!gdtr/idtrBits->base-addr gdt-ptr (!gdtr/idtrBits->limit (1- gdt-size) 0)) x86))
       ;; Set CS = 0x10 and DS = ES = SS = 0x18
       (x86 (load-segment-reg *CS* #x10 x86))
       (x86 (load-segment-reg *DS* #x18 x86))
       (x86 (load-segment-reg *ES* #x18 x86))
       (x86 (load-segment-reg *SS* #x18 x86))

       ;; Clear the interrupt flag (bit 9 of rflags)
       (x86 (!rflags (logand (lognot (ash 1 9))
                             (rflags x86))
                     x86))

       (x86 (!rgfi *rsi* zero-page-ptr x86))

       ((unless (and (> (len kernel-image) #x1F1)
                     (canonical-address-p (+ kernel-ptr (* (nth #x1F1 kernel-image) 512) #x400)))) (mv x86 state))
       ((mv & x86) (init-x86-state-64 
                     nil 
                     (+ kernel-ptr (* (nth #x1F1 kernel-image) 512) #x400)
                     nil
                     nil 
                     nil 
                     nil 
                     nil 
                     nil 
                     nil 
                     (rflags x86) 
                     nil
                     x86)))
      (mv x86 state)))
