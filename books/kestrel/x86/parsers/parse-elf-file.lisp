; A parser for ELF executables
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; References:
;; https://refspecs.linuxfoundation.org/elf/elf.pdf
;; https://www.uclibc.org/docs/elf-64-gen.pdf
;; https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.eheader.html
;; https://en.wikipedia.org/wiki/Executable_and_Linkable_Format
;; https://github.com/nasa/elf2cfetbl/blob/main/ELF_Structures.h
;; https://gabi.xinuos.com/elf/a-emachine.html

(include-book "parser-utils")
(include-book "kestrel/alists-light/lookup-equal-safe" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system) ; reduce?
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/typed-lists-light/alist-listp" :dir :system)
(include-book "kestrel/bv-lists/byte-listp" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/typed-lists-light/true-list-listp" :dir :system))

(in-theory (disable mv-nth))

(local
  (defthm integerp-when-unsigned-byte-p-32
    (implies (unsigned-byte-p 32 x)
             (integerp x))))

(local
  (defthm acl2-numberp-when-bytep
    (implies (bytep x)
             (acl2-numberp x))))

(local
  (defthm alistp-of-lookup-equal
    (implies (alist-listp (strip-cdrs x))
             (alistp (lookup-equal key x)))
    :hints (("Goal" :in-theory (enable lookup-equal)))))

(local
  (defthm symbolp-of-lookup-equal
    (implies (symbol-listp (strip-cdrs alist))
             (symbolp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal)))))

(local (in-theory (enable unsigned-byte-p-of-mv-nth-1-of-parse-u8
                          unsigned-byte-p-of-mv-nth-1-of-parse-u16
                          unsigned-byte-p-of-mv-nth-1-of-parse-u32
                          unsigned-byte-p-of-mv-nth-1-of-parse-u64
                          byte-listp-of-mv-nth-2-of-parse-u8
                          byte-listp-of-mv-nth-2-of-parse-u16
                          byte-listp-of-mv-nth-2-of-parse-u32
                          byte-listp-of-mv-nth-2-of-parse-u64
                          alistp-of-cdr-when-alist-listp-of-strip-cdrs
                          acl2-numberp-when-integerp
                          <=-of-0-when-natp)))

(local (in-theory (disable natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *elf-magic-number* #x464C457F) ; 7F"ELF" (but note the byte order)

(defconst *classes*
  `(;; (0 . :invalid)
    (1 . :elfclass32)
    (2 . :elfclass64)))

(defconst *data-encodings*
  `(;; (0 . :invalid)
    (1 . :elfdata2lsb)
    (2 . :elfdata2msb)))

(defconst *segment-mask-flag-alist*
  `((#x1 . :pf_x)
    (#x2 . :pf_w)
    (#x4 . :pf_r)))

;; Usually each car of the mask-flag-alist has a single bit set
(defund decode-val-with-mask-flag-alist (val mask-flag-alist)
  (declare (xargs :guard (and (integerp val)
                              (alistp mask-flag-alist)
                              (nat-listp (strip-cars mask-flag-alist)))))
  (if (endp mask-flag-alist)
      nil
    (let* ((pair (first mask-flag-alist))
           (mask (car pair))
           (flag (cdr pair)))
      (if (not (equal 0 (logand val mask)))
          (cons flag (decode-val-with-mask-flag-alist val (rest mask-flag-alist)))
        (decode-val-with-mask-flag-alist val (rest mask-flag-alist))))))

;; todo: There is an entry for Linux, but I don't see it being used.
(defconst *osabis*
  `((0 . :elfosabi_sysv)
    (1 . :elfosabi_hpux)
    (255 . :elfosabi_standalone)))

(defconst *program-header-types*
  `((0 . :PT_NULL)
    (1 . :PT_LOAD)
    (2 . :PT_DYNAMIC)
    (3 . :PT_INTERP)
    (4 . :PT_NOTE)
    (5 . :PT_SHLIB)
    (6 . :PT_PHDR)
    (7 . :PT_TLS)
    ;; From https://raw.githubusercontent.com/wiki/hjl-tools/linux-abi/linux-abi-draft.pdf (System V Application Binary Interface Linux Extensions, Version 0.1, November 28, 2018)
    ;; and https://refspecs.linuxbase.org/LSB_4.1.0/LSB-Core-generic/LSB-Core-generic/progheader.html:
    (#x6474e550 . :PT_GNU_EH_FRAME)
    (#x6474e551 . :PT_GNU_STACK)
    (#x6474e552 . :PT_GNU_RELRO)
    (#x6474e553 . :PT_GNU_PROPERTY)
    ))

;; Returns (mv erp p_type).
(defun decode-program-header-type (p_type)
  (declare (xargs :guard (unsigned-byte-p 32 p_type)))
  (let ((res (lookup p_type *program-header-types*)))
    (if res
        (mv nil res)
      (if (and (<= #x60000000 p_type)
               (<= p_type #x6FFFFFFF))
          (mv nil :operating-system-specific)
        (if (and (<= #x70000000 p_type)
                 (<= p_type #x7FFFFFFF))
            (mv nil :processor-specific)
          (mv (cons :bad-program-header-type p_type) nil))))))

(defconst *elf-file-types* ; acl2::*file-types* is already defined
  `((#x0 . :none)
    (#x1 . :rel)
    (#x2 . :exec)
    (#x3 . :dyn)
    (#x4 . :core)))

(defund decode-file-type (e_type)
  (declare (xargs :guard (unsigned-byte-p 16 e_type)))
  (let ((res (lookup e_type *elf-file-types*)))
    (if res
        res
      (if (and (<= #xfe00 e_type)
               (<= e_type #xfeff))
          :operating-system-specific
        (if (and (<= #xff00 e_type)
                 (<= e_type #xffff))
            :processor-specific
          (er hard? 'decode-file-type "Unknown file type: ~x0." e_type))))))

(local
  (defthm symbolp-of-decode-file-type
    (symbolp (decode-file-type e_type))
    :hints (("Goal" :in-theory (enable decode-file-type)))))

;; TODO: Add/check these.  Where is the official list?
;; There are more of these here:
;; https://gist.github.com/x0nu11byt3/bcb35c3de461e5fb66173071a2379779
(defconst *elf-machine-types*
  '((0 . :EM_NONE)
    (1 . :EM_M32)  ;       AT&T WE 32100
    (2 . :EM_SPARC) ;       SPARC
    (3 . :EM_386)   ;       Intel 80386
    (4 . :EM_68K)   ;       Motorola 68000
    (5 . :EM_88K)   ;       Motorola 88000
    ;; reserved        6       Reserved for future use (was EM_486)
    (7 . :EM_860)       ;       Intel 80860
    (8 . :EM_MIPS)      ;       MIPS I Architecture
    (9 . :EM_S370)      ;       IBM System/370 Processor
    (10 . :EM_MIPS_RS3_LE) ;      MIPS RS3000 Little-endian
    ;; reserved        11-14   Reserved for future use
    (15 . :EM_PARISC)   ;      Hewlett-Packard PA-RISC
    ;; reserved        16      Reserved for future use
    (17 . :EM_VPP500)   ;      Fujitsu VPP500
    (18 . :EM_SPARC32PLUS) ;      Enhanced instruction set SPARC
    (19 . :EM_960)         ;      Intel 80960
    (20 . :EM_PPC)         ;      PowerPC
    (21 . :EM_PPC64)       ;      64-bit PowerPC
    (22 . :EM_S390)        ;      IBM System/390 Processor
    ;; reserved        23-35   Reserved for future use
    (36 . :EM_V800)  ;      NEC V800
    (37 . :EM_FR20)  ;      Fujitsu FR20
    (38 . :EM_RH32)  ;      TRW RH-32
    (39 . :EM_RCE)   ;      Motorola RCE
    (40 . :EM_ARM)   ;      Advanced RISC Machines ARM
    (41 . :EM_ALPHA) ;      Digital Alpha
    (42 . :EM_SH)    ;      Hitachi SH
    (43 . :EM_SPARCV9) ;      SPARC Version 9
    (44 . :EM_TRICORE) ;      Siemens TriCore embedded processor
    (45 . :EM_ARC)     ;      Argonaut RISC Core, Argonaut Technologies Inc.
    (46 . :EM_H8_300)  ;      Hitachi H8/300
    (47 . :EM_H8_300H) ;      Hitachi H8/300H
    (48 . :EM_H8S)     ;      Hitachi H8S
    (49 . :EM_H8_500)  ;      Hitachi H8/500
    (50 . :EM_IA_64)   ;      Intel IA-64 processor architecture
    (51 . :EM_MIPS_X)  ;      Stanford MIPS-X
    (52 . :EM_COLDFIRE) ;      Motorola ColdFire
    (53 . :EM_68HC12)   ;      Motorola M68HC12
    (54 . :EM_MMA)      ;      Fujitsu MMA Multimedia Accelerator
    (55 . :EM_PCP)      ;      Siemens PCP
    (56 . :EM_NCPU)     ;      Sony nCPU embedded RISC processor
    (57 . :EM_NDR1)     ;      Denso NDR1 microprocessor
    (58 . :EM_STARCORE) ;      Motorola Star*Core processor
    (59 . :EM_ME16)     ;      Toyota ME16 processor
    (60 . :EM_ST100)    ;      STMicroelectronics ST100 processor
    (61 . :EM_TINYJ) ;      Advanced Logic Corp. TinyJ embedded processor family
    (62 . :EM_X86_64) ;      AMD x86-64 architecture
    (63 . :EM_PDSP)   ;      Sony DSP Processor
    (64 . :EM_PDP10)  ;      Digital Equipment Corp. PDP-10
    (65 . :EM_PDP11)  ;      Digital Equipment Corp. PDP-11
    (66 . :EM_FX66)   ;      Siemens FX66 microcontroller
    (67 . :EM_ST9PLUS) ;      STMicroelectronics ST9+ 8/16 bit microcontroller
    (68 . :EM_ST7)     ;      STMicroelectronics ST7 8-bit microcontroller
    (69 . :EM_68HC16)  ;      Motorola MC68HC16 Microcontroller
    (70 . :EM_68HC11)  ;      Motorola MC68HC11 Microcontroller
    (71 . :EM_68HC08)  ;      Motorola MC68HC08 Microcontroller
    (72 . :EM_68HC05)  ;      Motorola MC68HC05 Microcontroller
    (73 . :EM_SVX)     ;      Silicon Graphics SVx
    (74 . :EM_ST19)    ;      STMicroelectronics ST19 8-bit microcontroller
    (75 . :EM_VAX)     ;      Digital VAX
    (76 . :EM_CRIS)    ;      Axis Communications 32-bit embedded processor
    (77 . :EM_JAVELIN) ;      Infineon Technologies 32-bit embedded processor
    (78 . :EM_FIREPATH) ;      Element 14 64-bit DSP Processor
    (79 . :EM_ZSP)      ;      LSI Logic 16-bit DSP Processor
    (80 . :EM_MMIX)     ;      Donald Knuth's educational 64-bit processor
    (81 . :EM_HUANY) ;      Harvard University machine-independent object files
    (82 . :EM_PRISM) ;      SiTera Prism
    (83 . :EM_AVR)   ;      Atmel AVR 8-bit microcontroller
    (84 . :EM_FR30)  ;      Fujitsu FR30
    (85 . :EM_D10V)  ;      Mitsubishi D10V
    (86 . :EM_D30V)  ;      Mitsubishi D30V
    (87 . :EM_V850)  ;      NEC v850
    (88 . :EM_M32R)  ;      Mitsubishi M32R
    (89 . :EM_MN10300) ;      Matsushita MN10300
    (90 . :EM_MN10200) ;      Matsushita MN10200
    (91 . :EM_PJ)      ;      picoJava
    (92 . :EM_OPENRISC) ;      OpenRISC 32-bit embedded processor
    (93 . :EM_ARC_A5)   ;      ARC Cores Tangent-A5
    (94 . :EM_XTENSA)   ;      Tensilica Xtensa Architecture
    (95 . :EM_VIDEOCORE) ;      Alphamosaic VideoCore processor
    (96 . :EM_TMM_GPP)   ;      Thompson Multimedia General Purpose Processor
    (97 . :EM_NS32K)     ;      National Semiconductor 32000 series
    (98 . :EM_TPC)       ;      Tenor Network TPC processor
    (99 . :EM_SNP1K)     ;      Trebia SNP 1000 processor
    (100 . :EM_ST200) ;     STMicroelectronics (www.st.com) ST200 microcontroller
    (243 . :EM_RISCV)
    ))

;; Returns (mv erp u16 bytes).  Little endian.
(defun parse-half (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u16 bytes))

;; Returns (mv erp u32 bytes).  Little endian.
(defun parse-word (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;; Returns (mv erp val bytes).  Little endian.
(defun parse-addr (64bitp bytes)
  (declare (xargs :guard (and (booleanp 64bitp)
                              (byte-listp bytes))))
  (if 64bitp (parse-u64 bytes) (parse-u32 bytes)))

;; Returns (mv erp val bytes).  Little endian.
(defun parse-offset (64bitp bytes)
  (declare (xargs :guard (and (booleanp 64bitp)
                              (byte-listp bytes))))
  (parse-addr 64bitp bytes))

;; Returns (mv erp u64 bytes).  Little endian.
(defun parse-xword (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u64 bytes))

;; Returns (mv erp chars).
(defun parse-string-chars (bytes acc)
  (declare (xargs :guard (and (byte-listp bytes)
                              (character-listp acc))
                  :guard-hints (("Goal" :expand (byte-listp bytes)
                                 :in-theory (enable byte-listp bytep)))))
  (if (endp bytes)
      (mv :ran-out-of-bytes-in-parse-string-chars nil)
    (let ((byte (first bytes)))
      (if (= 0 byte)
          (mv nil (reverse acc))
        (parse-string-chars (rest bytes) (cons (code-char byte) acc))))))

(local
  (defthm character-listp-of-mv-nth-1-of-parse-string-chars
    (implies (character-listp acc)
             (character-listp (mv-nth 1 (parse-string-chars bytes acc))))
    :hints (("Goal" :in-theory (enable parse-string-chars)))))

;; Returns (mv erp string)
(defun parse-string (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (mv-let (erp chars)
    (parse-string-chars bytes nil)
    (if erp
        (mv erp "")
      (mv nil (coerce chars 'string)))))

(defconst *sh-types*
  '((0 . :sht-null)
    (1 . :sht-progbits)
    (2 . :sht-symtab)
    (3 . :sht-strtab)
    (4 . :sht-rela)
    (5 . :sht-hash)
    (6 . :sht-dynamic)
    (7 . :sht-note)
    (8 . :sht-nobits)
    (9 . :sht-rel)
    (10 . :sht-shlib)
    (11 . :sht-dynsym)
    ;; todo: handle the ranges
    ))

(defconst *shn_undef* 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp section-header bytes).
(defund parse-elf-section-header (64-bitp bytes)
  (declare (xargs :guard (and (booleanp 64-bitp)
                              (byte-listp bytes))))
  (b* ((result nil)
       ((mv erp sh_name bytes) (parse-word bytes))
       ((when erp) (mv erp nil bytes))
       (result (acons :name-offset sh_name result))
       ((mv erp sh_type bytes) (parse-word bytes))
       ((when erp) (mv erp nil bytes))
       (type (let ((res (lookup sh_type *sh-types*)))
               (or res :unknown)))
       (result (acons :type type result))
       ((mv erp sh_flags bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       (result (acons :flags sh_flags result))
       ((mv erp sh_addr bytes) (parse-addr 64-bitp bytes))
       ((when erp) (mv erp nil bytes))
       (result (acons :addr sh_addr result))
       ((mv erp sh_offset bytes) (parse-offset 64-bitp bytes))
       ((when erp) (mv erp nil bytes))
       (result (acons :offset sh_offset result))
       ((mv erp sh_size bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       (result (acons :size sh_size result))
       ((mv erp sh_link bytes) (parse-word bytes))
       ((when erp) (mv erp nil bytes))
       (result (acons :link sh_link result))
       ((mv erp sh_info bytes) (parse-word bytes))
       ((when erp) (mv erp nil bytes))
       (result (acons :info sh_info result))
       ((mv erp sh_addralign bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       (result (acons :addralign sh_addralign result))
       ((mv erp sh_entsize bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       (result (acons :entsize sh_entsize result)))
    (mv nil (reverse result) bytes)))

(local
  (defthm alist-of-mv-nth-1-of-parse-elf-section-header
    (alistp (mv-nth 1 (parse-elf-section-header 64-bitp bytes)))
    :hints (("Goal" :in-theory (enable parse-elf-section-header)))))

(local
  (defthm byte-listp-of-mv-nth-2-of-parse-elf-section-header
    (implies (byte-listp bytes)
             (byte-listp (mv-nth 2 (parse-elf-section-header 64-bitp bytes))))
    :hints (("Goal" :in-theory (enable parse-elf-section-header)))))

;; Returns (mv erp section-header-table-without-names).
(defund parse-elf-section-headers (index count 64-bitp acc bytes)
  (declare (xargs :guard (and (natp index)
                              (natp count)
                              (alist-listp acc) ; todo: strenghten
                              (booleanp 64-bitp)
                              (byte-listp bytes))
                  :measure (nfix (- count index))))
  (if (or (<= count index)
          (not (natp index))
          (not (natp count)))
      (mv nil (reverse acc))
    (mv-let (erp section-header bytes)
      (parse-elf-section-header 64-bitp bytes)
      (if erp
          (mv erp nil)
        (parse-elf-section-headers (+ 1 index)
                                   count
                                   64-bitp
                                   (cons section-header acc)
                                   bytes)))))

(local
  (defthm alist-listp-of-mv-nth-1-of-parse-elf-section-headers
    (implies (alist-listp acc)
             (alist-listp (mv-nth 1 (parse-elf-section-headers index count 64-bitp acc bytes))))
    :hints (("Goal" :in-theory (enable parse-elf-section-headers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; strengthen?  disable?
;; currently, this applies to section-header-tables with and without the names filled in
(defun section-header-tablep (section-header-table)
  (declare (xargs :guard t))
  (alist-listp section-header-table))

;; Looks up a section header by name.  Returns the header, or :none.
(defund get-elf-section-header (name section-header-table)
  (declare (xargs :guard (and (stringp name)
                              (section-header-tablep section-header-table))))
  (if (endp section-header-table)
      :none
    (let* ((section-header (first section-header-table))
           (this-name (lookup-eq-safe :name section-header)))
      (if (equal this-name name)
          section-header
        (get-elf-section-header name (rest section-header-table))))))

(defthm alistp-of-get-elf-section-header
  (implies (and (not (equal :none (get-elf-section-header name section-header-table)))
                (section-header-tablep section-header-table))
           (alistp (get-elf-section-header name section-header-table)))
  :hints (("Goal" :in-theory (enable get-elf-section-header))))

(defopeners get-elf-section-header) ; move?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp result).
(defund assign-section-header-names (section-header-table string-table-bytes acc)
  (declare (xargs :guard (and (section-header-tablep section-header-table)
                              (byte-listp string-table-bytes)
                              (alistp acc))))
  (if (endp section-header-table)
      (mv nil (reverse acc))
    (b* ((section-header (first section-header-table))
         (name-offset (lookup-eq-safe :name-offset section-header))
         ((when (not (natp name-offset))) ; impossible?
          (mv :bad-name-offset nil)))
      (mv-let (erp name)
        (parse-string (nthcdr name-offset string-table-bytes))
        (if erp
            (mv erp nil)
          (assign-section-header-names (rest section-header-table)
                                       string-table-bytes
                                       (cons (acons :name name section-header) acc)))))))

(local
  (defthm alist-listp-of-mv-nth-1-of-assign-section-header-names
    (implies (and (alist-listp acc)
                  (section-header-tablep section-header-table))
             (alist-listp (mv-nth 1 (assign-section-header-names section-header-table string-table-bytes acc))))
    :hints (("Goal" :in-theory (enable assign-section-header-names)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund symtab-offset-and-size (section-header-table)
  (declare (xargs :guard (section-header-tablep section-header-table)))
  (if (endp section-header-table)
      (prog2$ (er hard? 'symtab-offset-and-size "No symbol table found.") ; todo: what about a stripped binary?
              (mv 0 0))
    (let* ((section-header (first section-header-table))
           (type (lookup-eq-safe :type section-header)))
      (if (eq type :sht-symtab)
          (mv (lookup-eq-safe :offset section-header)
              (lookup-eq-safe :size section-header))
        (symtab-offset-and-size (rest section-header-table))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund strtab-offset (section-header-table)
  (declare (xargs :guard (section-header-tablep section-header-table)))
  (let ((header (get-elf-section-header ".strtab" section-header-table)))
    (if (eq :none header)
        :none
      (lookup-eq-safe :offset header))))

;; Returns (mv erp result bytes) where RESULT is an alist representing the symbol-table-entry.
(defun parse-elf-symbol-table-entry (64-bitp string-table-bytes-etc bytes)
  (declare (xargs :guard (and (booleanp 64-bitp)
                              (byte-listp string-table-bytes-etc)
                              (byte-listp bytes))))
  (if 64-bitp
      (b* ((result nil)
           ((mv erp st_name bytes) (parse-word bytes)) ; actually an offset
           ((when erp) (mv erp nil bytes))
           (result (acons :name-offset st_name result))
           ((mv erp name) (if (= 0 st_name)
                              (mv nil :no-name)
                            (parse-string (nthcdr st_name string-table-bytes-etc))))
           ((when erp) (mv erp nil bytes))
           (result (acons :name name result))
           ((mv erp st_info bytes) (parse-u8 bytes))
           ((when erp) (mv erp nil bytes))
           (result (acons :info st_info result))
           ((mv erp st_other bytes) (parse-u8 bytes))
           ((when erp) (mv erp nil bytes))
           (result (acons :other st_other result))
           ((mv erp st_shndx bytes) (parse-half bytes))
           ((when erp) (mv erp nil bytes))
           (result (acons :shndx st_shndx result))
           ((mv erp st_value bytes) (parse-addr 64-bitp bytes))
           ((when erp) (mv erp nil bytes))
           (result (acons :value st_value result))
           ((mv erp st_size bytes) (parse-xword bytes))
           ((when erp) (mv erp nil bytes))
           (result (acons :size st_size result)))
        (mv nil (reverse result) bytes))
    ;; differnt layout for 32-bits:
    (b* ((result nil)
         ((mv erp st_name bytes) (parse-word bytes)) ; actually an offset
         ((when erp) (mv erp nil bytes))
         (result (acons :name-offset st_name result))
         ((mv erp name) (if (= 0 st_name)
                            (mv nil :no-name)
                          (parse-string (nthcdr st_name string-table-bytes-etc))))
         ((when erp) (mv erp nil bytes))
         (result (acons :name name result))

         ((mv erp st_value bytes) (parse-addr nil bytes))
         ((when erp) (mv erp nil bytes))
         (result (acons :value st_value result))

         ((mv erp st_size bytes) (parse-word bytes))
         ((when erp) (mv erp nil bytes))
         (result (acons :size st_size result))

         ((mv erp st_info bytes) (parse-u8 bytes))
         ((when erp) (mv erp nil bytes))
         (result (acons :info st_info result))

         ((mv erp st_other bytes) (parse-u8 bytes))
         ((when erp) (mv erp nil bytes))
         (result (acons :other st_other result))

         ((mv erp st_shndx bytes) (parse-half bytes))
         ((when erp) (mv erp nil bytes))
         (result (acons :shndx st_shndx result)))
      (mv nil (reverse result) bytes))))

;; Returns (mv erp result) where RESULT is a list of alists, each representing a symbol-table-entry.
(defund parse-elf-symbol-table (symbol-table-size 64-bitp string-table-bytes-etc acc bytes)
  (declare (xargs :guard (and (integerp symbol-table-size)
                              ;; (equal 0 (mod symbol-table-size 24))
                              (booleanp 64-bitp)
                              (byte-listp string-table-bytes-etc)
                              (true-listp acc)
                              (byte-listp bytes))
                  :measure (len bytes)))
  (if (not (posp symbol-table-size))
      (mv nil (reverse acc))
    (mv-let (erp symbol-table-entry bytes)
      (parse-elf-symbol-table-entry 64-bitp string-table-bytes-etc bytes)
      (if erp
          (mv erp nil)
        (parse-elf-symbol-table (- symbol-table-size (if 64-bitp 24 16)) ; size of a symbol-table-entry
                                64-bitp
                                string-table-bytes-etc
                                (cons symbol-table-entry acc)
                                bytes)))))

(defund elf-symbol-tablep (st)
  (declare (xargs :guard t ))
  (alist-listp st))

(local
  (defthm elf-symbol-tablep-of-mv-nth-1-of-parse-elf-symbol-table
    (implies (elf-symbol-tablep acc)
             (elf-symbol-tablep (mv-nth 1 (parse-elf-symbol-table symbol-table-size 64-bitp string-table-bytes-etc acc bytes))))
    :hints (("Goal" :in-theory (enable parse-elf-symbol-table elf-symbol-tablep)))))

;; Returns (mv erp result) where RESULT is an alist mapping section names to lists of bytes.
(defund extract-elf-sections (section-header-table all-bytes acc)
  (declare (xargs :guard (and (section-header-tablep section-header-table)
                              (byte-listp all-bytes)
                              (alistp acc))))
  (if (endp section-header-table)
      (mv nil (reverse acc))
    (b* ((section-header (first section-header-table))
         (name (lookup-eq-safe :name section-header))
         (offset (lookup-eq-safe :offset section-header))
         ((when (not (natp offset))) ; impossible?
          (mv :bad-size nil))
         (size (lookup-eq-safe :size section-header))
         ((when (not (natp size))) ; impossible?
          (mv :bad-size nil))
         ((mv erp bytes &) (parse-n-bytes size (nthcdr offset all-bytes)))
         ((when erp) (mv erp nil)))
      (extract-elf-sections (rest section-header-table) all-bytes
                            (acons name bytes acc)))))

(local
  (defthm alistp-of-mv-nth-1-of-extract-elf-sections
    (implies (alistp acc)
             (alistp (mv-nth 1 (extract-elf-sections section-header-table all-bytes acc))))
    :hints (("Goal" :in-theory (enable extract-elf-sections)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes an entry in the program-header-table
(defund elf-program-header-table-entryp (entry)
  (declare (xargs :guard t))
  (and (symbol-alistp entry)
       (natp (lookup-eq :vaddr entry))
       (natp (lookup-eq :memsz entry))
       ;; todo: more
       ))

;move up
;; Returns (mv erp program-header bytes).
(defund parse-elf-program-header (64-bitp bytes)
  (declare (xargs :guard (and (booleanp 64-bitp)
                              (byte-listp bytes)
                              ;; (len-at-least (if 64-bitp #x38 #x20) bytes)
                              )))
  (b* (((mv erp p_type bytes) (parse-word bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp p_type) (decode-program-header-type p_type))
       ((when erp) (mv erp nil bytes))
       ;; We wait to assemble the result, due to differences in where the flags
       ;; appear in 32-bit vs 64-bit headers.
       ((mv erp p_flags bytes)                    ; flags are read later if 32-bit
        (if 64-bitp
            (parse-word bytes)
          (mv nil :to-be-read-later bytes)))
       ((when erp) (mv erp nil bytes))
       ;; flags not stored until below
       ((mv erp p_offset bytes) (parse-offset 64-bitp bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp p_vaddr bytes) (parse-addr 64-bitp bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp p_paddr bytes) (parse-addr 64-bitp bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp p_filesz bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       ((mv erp p_memsz bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       ((mv erp p_flags bytes) ; flags already read above if 64-bit
        (if 64-bitp
            (mv nil p_flags bytes) ; already read above
          (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       ((mv erp p_align bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       ((when erp) (mv erp nil bytes))
       ;; Check for errors:
       ((when (not (unsigned-byte-p 47 p_vaddr)))
        (er hard? 'parse-elf-program-header "Segment address ~x0 too large." p_vaddr)
        (mv :vaddr-too-large nil bytes))
       ((when (not (or (and (= 0 p_vaddr) (= 0 p_memsz)) ; would give -1 in the computation below
                       (unsigned-byte-p 47 (+ p_vaddr p_memsz -1)))))
        (er hard? 'parse-elf-program-header "Segment with vaddr ~x0 and size ~x1 too large." p_vaddr p_memsz)
        (mv :segment-too-large nil bytes))
       ;; Assemble the result:
       (result nil) ; an alist, to be extended
       (result (acons :type p_type result))
       ;; we put the flags second, as they come second for 64-bit (the order shouldn't matter much):
       (result (acons :flags (decode-val-with-mask-flag-alist p_flags *segment-mask-flag-alist*) result))
       (result (acons :offset p_offset result))
       (result (acons :vaddr p_vaddr result))
       (result (acons :paddr p_paddr result)) ;; reserved for systems with physical addressing
       (result (acons :filesz p_filesz result))
       (result (acons :memsz p_memsz result))
       (result (acons :align p_align result)))
    (mv nil (reverse result) bytes)))

;drop?
(local
  (defthm alistp-of-mv-nth-1-of-parse-elf-program-header
    (alistp (mv-nth 1 (parse-elf-program-header 64-bitp bytes)))
    :hints (("Goal" :in-theory (enable parse-elf-program-header)))))

(local
  (defthm elf-program-header-table-entryp-of-mv-nth-1-of-parse-elf-program-header
    (implies (not (mv-nth 0 (parse-elf-program-header 64-bitp bytes)))
             (elf-program-header-table-entryp (mv-nth 1 (parse-elf-program-header 64-bitp bytes))))
    :hints (("Goal" :in-theory (enable parse-elf-program-header elf-program-header-table-entryp)))))

(local
  (defthm byte-listp-of-mv-nth-2-of-parse-elf-program-header
    (implies (byte-listp bytes)
             (byte-listp (mv-nth 2 (parse-elf-program-header 64-bitp bytes))))
    :hints (("Goal" :in-theory (enable parse-elf-program-header)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Recognizes a program-header-table.
(defund elf-program-header-tablep (program-header-table)
  (declare (xargs :guard t))
  (if (not (consp program-header-table))
      (null program-header-table)
    (and (elf-program-header-table-entryp (first program-header-table))
         (elf-program-header-tablep (rest program-header-table)))))

(local
  (defthm elf-program-header-tablep-of-revappend
    (implies (and (elf-program-header-tablep x)
                  (elf-program-header-tablep y))
             (elf-program-header-tablep (revappend x y)))
    :hints (("Goal" :in-theory (enable elf-program-header-tablep revappend)))))

;move up
;; Returns (mv erp program-headers) where PROGRAM-HEADERS is a list of alists
;; (header entries).
(defund parse-elf-program-header-table (index num-entries 64-bitp acc bytes)
  (declare (xargs :guard (and (natp index)
                              (natp num-entries)
                              (booleanp 64-bitp)
                              (true-list-listp acc)
                              (byte-listp bytes))
                  :measure (nfix (- num-entries index))
                  :hints (("Goal" :in-theory (enable natp)))))
  (if (or (<= num-entries index)
          (not (natp index))
          (not (natp num-entries)))
      (mv nil (reverse acc))
    (mv-let (erp program-header bytes)
      (parse-elf-program-header 64-bitp bytes)
      (if erp
          (mv erp nil)
        (parse-elf-program-header-table (+ 1 index)
                                   num-entries
                                   64-bitp
                                   (cons program-header acc)
                                   bytes)))))

(local
  (defthm elf-program-header-tablep-of-mv-nth-1-of-parse-elf-program-header-table
    (implies (and (elf-program-header-tablep acc)
                  (not (mv-nth 0 (parse-elf-program-header-table index num-entries 64-bitp acc bytes)))
                  )
             (elf-program-header-tablep (mv-nth 1 (parse-elf-program-header-table index num-entries 64-bitp acc bytes))))
    :hints (("Goal" :in-theory (enable parse-elf-program-header-table elf-program-header-tablep)))))

;; Returns (mv erp parsed-elf) where PARSED-ELF is meaningless if ERP in non-nil.
;; TODO: Some of this parsing need not be done for all callers (e.g., when loading an image)
;; TODO: Allow returning an error.
(defund parse-elf-file-bytes (bytes)
  (declare (xargs :guard (byte-listp bytes)
                  :guard-hints (("Goal" :in-theory (e/d (byte-listp-of-mv-nth-1-of-parse-n-bytes) (bytep))))))
  (b* ((all-bytes bytes) ; original bytes, for later looking up things at given offsets
       (result nil) ; empty alist, to be extended
       (result (acons :bytes all-bytes result))
       ;; Parse the file header:
       ((mv erp e_ident bytes) (parse-n-bytes 16 bytes))
       ((when erp) (mv erp nil))
       (ei_mag0 (nth 0 e_ident))
       (ei_mag1 (nth 1 e_ident))
       (ei_mag2 (nth 2 e_ident))
       (ei_mag3 (nth 3 e_ident))
       (ei_class (nth 4 e_ident))
       (ei_data (nth 5 e_ident))
       (ei_version (nth 6 e_ident))
       (ei_osabi (nth 7 e_ident))
       (ei_abiversion (nth 8 e_ident))
       ;; todo: parse more fields of e_ident?

       ;; Check that the magic number is right:
       ((when (not (and (= #x7F ei_mag0)
                        (= (char-code #\E) ei_mag1)
                        (= (char-code #\L) ei_mag2)
                        (= (char-code #\F) ei_mag3))))
        (er hard? 'parse-elf-file-bytes "Bad magic number: ~x0." (take 4 e_ident))
        (mv t nil))

       (class (lookup-safe ei_class *classes*))
       (64-bitp (eq :elfclass64 class))
       ;; Now we can set the magic number (todo: call this :executable-type?):
       (result (acons :magic (if 64-bitp :elf-64 :elf-32) result)) ; for use by parsed-executable-type
       (result (acons :class class result))
       (data (lookup-safe ei_data *data-encodings*))
       (result (acons :data data result))
       (result (acons :version ei_version result))
       (osabi (lookup-safe ei_osabi *osabis*))
       (result (acons :osabi osabi result))
       (result (acons :abiversion ei_abiversion result))
       ;; Done with e_ident.  Now parse the rest of the header:
       ((mv erp e_type bytes) (parse-half bytes)) ; todo: consider endianness for these values
       ((when erp) (mv erp nil))
       (result (acons :type (decode-file-type e_type) result))

       ((mv erp e_machine bytes) (parse-half bytes))
       ((when erp) (mv erp nil))
       (result (acons :machine (lookup-safe e_machine *elf-machine-types*) result))

       ((mv erp e_version bytes) (parse-word bytes))
       ((when erp) (mv erp nil))
       (result (acons :version e_version result))

       ((mv erp e_entry bytes) (parse-addr 64-bitp bytes))
       ((when erp) (mv erp nil))
       (result (acons :entry e_entry result))

       ((mv erp e_phoff bytes) (parse-offset 64-bitp bytes))
       ((when erp) (mv erp nil))
       (result (acons :phoff e_phoff result))

       ((mv erp e_shoff bytes) (parse-offset 64-bitp bytes))
       ((when erp) (mv erp nil))
       (result (acons :shoff e_shoff result))

       ((mv erp e_flags bytes) (parse-word bytes))
       ((when erp) (mv erp nil))
       (result (acons :flags e_flags result))

       ((mv erp e_ehsize bytes) (parse-half bytes))
       ((when erp) (mv erp nil))
       (result (acons :ehsize e_ehsize result))

       ((mv erp e_phentsize bytes) (parse-half bytes))
       ((when erp) (mv erp nil))
       (result (acons :phentsize e_phentsize result))

       ((mv erp e_phnum bytes) (parse-half bytes))
       ((when erp) (mv erp nil))
       (result (acons :phnum e_phnum result))

       ((mv erp e_shentsize bytes) (parse-half bytes))
       ((when erp) (mv erp nil))
       (result (acons :shentsize e_shentsize result))

       ((mv erp e_shnum bytes) (parse-half bytes))
       ((when erp) (mv erp nil))
       (result (acons :shnum e_shnum result))

       ((mv erp e_shstrndx &) (parse-half bytes)) ; ignore the remaining bytes, as below we jump ahead
       ((when erp) (mv erp nil))
       (result (acons :shstrndx e_shstrndx result))

       ;; Parse the program header table:
       ((mv erp program-header-table)
        (parse-elf-program-header-table 0 e_phnum 64-bitp nil (nthcdr e_phoff all-bytes)))
       ((when erp) (mv erp nil))
       (result (acons :program-header-table program-header-table result))

       ;; Parse the section header table:
       ((mv erp section-header-table-without-names) (parse-elf-section-headers 0 e_shnum 64-bitp nil (nthcdr e_shoff all-bytes)))
       ((when erp) (mv erp nil))

       ;; Resolve the names of the section headers:
       ((when (= e_shstrndx *shn_undef*))
        (mv :no-section-contains-a-section-name-string-table nil))
       (section-name-string-table-header (nth e_shstrndx section-header-table-without-names))
       (section-name-string-table-offset (lookup-eq-safe :offset section-name-string-table-header))
       ((when (not (natp section-name-string-table-offset))) ; impossible?
        (mv :bad-section-name-string-table-offset nil))
       ((mv erp section-header-table) (assign-section-header-names section-header-table-without-names
                                                                   (nthcdr section-name-string-table-offset all-bytes)
                                                                   nil))
       ((when erp) (mv erp nil))
       (result (acons :section-header-table section-header-table result))

       ((mv symbol-table-offset symbol-table-size) (symtab-offset-and-size section-header-table))
       ((when (not (natp symbol-table-offset))) ; impossible?
        (mv :bad-symbol-table-offset nil))
       ((when (not (natp symbol-table-size))) ; impossible?
        (mv :bad-symbol-table-size nil))
       (string-table-offset (strtab-offset section-header-table))
       ((when (not (natp string-table-offset))) ; impossible? but it may be :none
        (mv :bad-string-table-offset nil))
       ((mv erp symbol-table) (parse-elf-symbol-table symbol-table-size
                                                      64-bitp
                                                      (nthcdr string-table-offset all-bytes)
                                                      nil
                                                      (nthcdr symbol-table-offset all-bytes)))
       ((when erp) (mv erp nil))
       (result (acons :symbol-table symbol-table result))

       ((mv erp sections) (extract-elf-sections section-header-table all-bytes nil))
       ((when erp) (mv erp nil))
       (result (acons :sections sections result))
       )
    (mv nil (reverse result))))

;; TODO: Maybe move parse-elf here and rename it parse-elf-file.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Add more to this
(defund parsed-elfp (parsed-elf)
  (declare (xargs :guard t))
  (and (symbol-alistp parsed-elf)
       ;; Check the bytes:
       (assoc-eq :bytes parsed-elf)
       (byte-listp (lookup-eq :bytes parsed-elf))
       ;; Check the type (:rel, :dyn, etc):
       (assoc-eq :type parsed-elf)
       (symbolp (lookup-eq :type parsed-elf))
       ;; Check the CPU type:
       (assoc-eq :machine parsed-elf)
       (symbolp (lookup-eq :machine parsed-elf))
       ;; Check the entry point:
       (assoc-eq :entry parsed-elf)
       (natp (lookup-eq :entry parsed-elf))
       ;; Check the section header table:
       (assoc-eq :section-header-table parsed-elf)
       (let ((section-header-table (lookup-eq :section-header-table parsed-elf)))
         (section-header-tablep section-header-table))
       ;; Check the sections (todo: drop this?):
       (assoc-eq :sections parsed-elf)
       (alistp (lookup-eq :sections parsed-elf))
       ;; Check the program header table (segments):
       (assoc-eq :program-header-table parsed-elf)
       (elf-program-header-tablep (lookup-eq :program-header-table parsed-elf))
       ;; Check the symbol-table:
       (assoc-eq :symbol-table parsed-elf)
       (elf-symbol-tablep (lookup-eq :symbol-table parsed-elf))))

(defthmd alistp-when-parsed-elfp
  (implies (parsed-elfp parsed-elf)
           (alistp parsed-elf))
  :hints (("Goal" :in-theory (enable parsed-elfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm parsed-elfp-of-mv-nth-1-of-parse-elf-file-bytes
  (implies (and (not (mv-nth 0 (parse-elf-file-bytes bytes)))
                (byte-listp bytes))
           (parsed-elfp (mv-nth 1 (parse-elf-file-bytes bytes))))
  :hints (("Goal" :in-theory (enable parse-elf-file-bytes parsed-elfp))))
