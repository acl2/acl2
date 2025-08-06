; A parser for Mach-O executables
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parser-utils")
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/typed-lists-light/map-code-char" :dir :system)
(include-book "kestrel/bv/defs-bitwise" :dir :system) ;for bvor

;; See also
;; projects/x86isa/tools/execution/exec-loaders/mach-o/mach-o-reader.lisp
;; This file is similar to mach-o-reader.lisp, but has the following differences:
;;
;; - returns the parsed mach-o file as an alist, rather than populate
;; a stobj (then, build-book-for-mach-o-file creates an ACL2 book with
;; a defconst for this alist).
;;
;; - makes the parsed contents more readable by, e.g., putting in
;; symbolic values for numeric constants, decoding some flags, etc.
;;
;; - supports all kinds of sections and doesn't presume which ones will occur
;;
;; - for "zero fill" sections, this tool refrains from trying to look
;; up data at a meaningless file offset.
;;
;; - this tool has many fewer dependencies than mach-o-reader.lisp
;;
;; - Disadvantage: This tool does not yet support exotic load commands.

;; The constants in this file are from /usr/include/mach-o/loader.h on
;; my Mac.  I believe that most or all agree with the ones in:
;; books/projects/execloader/mach-o-constants.lisp
;; I also used:
;; https://github.com/apple/darwin-xnu/blob/main/EXTERNAL_HEADERS/mach-o/loader.h

(local (in-theory (disable mv-nth)))

(local
 (defthm symbolp-of-lookup-equal
   (implies (symbol-listp (strip-cdrs alist))
            (symbolp (lookup-equal key alist)))
   :hints (("Goal" :in-theory (enable lookup-equal assoc-equal strip-cdrs)))))

;;;
;;; magic numbers
;;;

(defconst *mach-o-magic-numbers*
  '((#xfeedface . :MH_MAGIC)
    (#xcefaedfe . :MH_CIGAM)
    (#xfeedfacf . :MH_MAGIC_64)
    (#xcffaedfe . :MH_CIGAM_64)))

(defconst *32-bit-magic-numbers* (list :MH_MAGIC :MH_CIGAM))
(defconst *64-bit-magic-numbers* (list :MH_MAGIC_64 :MH_CIGAM_64))

;;;
;;; CPU types (from /usr/include/mach/machine.h)
;;;

(defconst *CPU_ARCH_ABI64* #x01000000)
(defconst *CPU_TYPE_X86* 7)
(defconst *CPU_TYPE_ARM* 12)
(defconst *CPU_TYPE_POWERPC* 18)

(defconst *mach-o-CPU-types*
  (list (cons (bvchop 32 -1) :CPU_TYPE_ANY)
        (cons 1 :CPU_TYPE_VAX)
        (cons 6 :CPU_TYPE_MC680x0)
        (cons *CPU_TYPE_X86* :CPU_TYPE_X86)
        (cons (bvor 32 *CPU_TYPE_X86* *CPU_ARCH_ABI64*) :CPU_TYPE_X86_64)
        (cons 10 :CPU_TYPE_MC98000)
        (cons 11 :CPU_TYPE_HPPA)
        (cons *CPU_TYPE_ARM* :CPU_TYPE_ARM)
        (cons (bvor 32 *CPU_TYPE_ARM* *CPU_ARCH_ABI64*) :CPU_TYPE_ARM64)
        (cons 13 :CPU_TYPE_MC88000)
        (cons 14 :CPU_TYPE_SPARC)
        (cons 15 :CPU_TYPE_I860)
        (cons *CPU_TYPE_POWERPC* :CPU_TYPE_POWERPC)
        (cons (bvxor 32 *CPU_TYPE_POWERPC*  *CPU_ARCH_ABI64*) :CPU_TYPE_POWERPC64)))


;;;
;;; filetypes
;;;

(defconst *mach-o-filetypes*
  '((#x1 . :MH_OBJECT)
    (#x2 . :MH_EXECUTE)
    (#x3 . :MH_FVMLIB)
    (#x4 . :MH_CORE)
    (#x5 . :MH_PRELOAD)
    (#x6 . :MH_DYLIB)
    (#x7 . :MH_DYLINKER)
    (#x8 . :MH_BUNDLE)
    (#x9 . :MH_DYLIB_STUB)
    (#xa . :MH_DSYM)
    (#xb . :MH_KEXT_BUNDLE)))

(defconst *LC_REQ_DYLD* #x80000000)

(defconst *mach-o-load-commands*
  (list (cons #x1 :LC_SEGMENT)
        (cons #x2 :LC_SYMTAB)
        (cons #x3 :LC_SYMSEG)
        (cons #x4 :LC_THREAD)
        (cons #x5 :LC_UNIXTHREAD)
        (cons #x6 :LC_LOADFVMLIB)
        (cons #x7 :LC_IDFVMLIB)
        (cons #x8 :LC_IDENT)
        (cons #x9 :LC_FVMFILE)
        (cons #xa :LC_PREPAGE)
        (cons #xb :LC_DYSYMTAB)
        (cons #xc :LC_LOAD_DYLIB)
        (cons #xd :LC_ID_DYLIB)
        (cons #xe :LC_LOAD_DYLINKER)
        (cons #xf :LC_ID_DYLINKER)
        (cons #x10 :LC_PREBOUND_DYLIB)
        (cons #x11 :LC_ROUTINES)
        (cons #x12 :LC_SUB_FRAMEWORK)
        (cons #x13 :LC_SUB_UMBRELLA)
        (cons #x14 :LC_SUB_CLIENT)
        (cons #x15 :LC_SUB_LIBRARY)
        (cons #x16 :LC_TWOLEVEL_HINTS)
        (cons #x17 :LC_PREBIND_CKSUM)
        (cons (bvor 32 #x18 *LC_REQ_DYLD*) :LC_LOAD_WEAK_DYLIB)
        (cons #x19 :LC_SEGMENT_64)
        (cons #x1a :LC_ROUTINES_64)
        (cons #x1b :LC_UUID)
        (cons (bvor 32 #x1c *LC_REQ_DYLD*) :LC_RPATH)
        (cons #x1d :LC_CODE_SIGNATURE)
        (cons #x1e :LC_SEGMENT_SPLIT_INFO)
        (cons (bvor 32 #x1f *LC_REQ_DYLD*) :LC_REEXPORT_DYLIB)
        (cons #x20 :LC_LAZY_LOAD_DYLIB)
        (cons #x21 :LC_ENCRYPTION_INFO)
        (cons #x22 :LC_DYLD_INFO)
        (cons (bvor 32 #x22 *LC_REQ_DYLD*) :LC_DYLD_INFO_ONLY)
        (cons (bvor 32 #x23  *LC_REQ_DYLD*) :LC_LOAD_UPWARD_DYLIB)
        (cons #x24 :LC_VERSION_MIN_MACOSX)
        (cons #x25 :LC_VERSION_MIN_IPHONEOS)
        (cons #x26 :LC_FUNCTION_STARTS)
        (cons #x27 :LC_DYLD_ENVIRONMENT)
        (cons (bvor 32 #x28 *LC_REQ_DYLD*) :LC_MAIN)
        (cons #x29 :LC_DATA_IN_CODE)
        (cons #x2A :LC_SOURCE_VERSION)
        (cons #x2B :LC_DYLIB_CODE_SIGN_DRS)
        (cons #x2C :LC_ENCRYPTION_INFO_64)
        (cons #x2D :LC_LINKER_OPTION)
        (cons #x2E :LC_LINKER_OPTIMIZATION_HINT)
        (cons #x2F :LC_VERSION_MIN_TVOS)
        (cons #x30 :LC_VERSION_MIN_WATCHOS)
        ;; These next 2 are copied from https://github.com/llvm-mirror/llvm/blob/master/include/llvm/BinaryFormat/MachO.def
        ;; Is that an authoritative source?
        (cons #x31 :LC_NOTE)
        (cons #x32 :LC_BUILD_VERSION)))

(defun keep-non-zeros (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (endp bytes)
      nil
    (let ((byte (first bytes)))
      (if (eql 0 byte)
          nil
        (cons byte (keep-non-zeros (rest bytes)))))))

(local
 (defthm byte-listp-of-keep-non-zeros
   (implies (byte-listp bytes)
            (byte-listp (keep-non-zeros bytes)))
   :hints (("Goal" :in-theory (enable keep-non-zeros)))))

;; Return (mv erp string bytes)
(defund parse-n-bytes-into-string (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (b* (((mv erp string-bytes bytes) (parse-n-bytes n bytes))
       ((when erp) (mv erp "" bytes))
       (string (coerce (map-code-char (keep-non-zeros string-bytes)) 'string)) ;TODO: strip trailing 0 bytes
       )
    (mv nil string bytes)))

(defthm stringp-of-mv-nth-1-of-parse-n-bytes-into-string
  (stringp (mv-nth 1 (parse-n-bytes-into-string n bytes)))
  :hints (("Goal" :in-theory (enable parse-n-bytes-into-string))))

(defthm byte-listp-of-mv-nth-2-of-parse-n-bytes-into-string
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-n-bytes-into-string n bytes))))
  :hints (("Goal" :in-theory (enable parse-n-bytes-into-string))))

(defconst *mach-o-header-flags-alist*
  '((#x1 . :MH_NOUNDEFS)
    (#x2 . :MH_INCRLINK)
    (#x4 . :MH_DYLDLINK)
    (#x8 . :MH_BINDATLOAD)
    (#x10 . :MH_PREBOUND)
    (#x20 . :MH_SPLIT_SEGS)
    (#x40 . :MH_LAZY_INIT)
    (#x80 . :MH_TWOLEVEL)
    (#x100 . :MH_FORCE_FLAT)
    (#x200 . :MH_NOMULTIDEFS)
    (#x400 . :MH_NOFIXPREBINDING)
    (#x800 . :MH_PREBINDABLE)
    (#x1000 . :MH_ALLMODSBOUND)
    (#x2000 . :MH_SUBSECTIONS_VIA_SYMBOLS)
    (#x4000 . :MH_CANONICAL)
    (#x8000 . :MH_WEAK_DEFINES)
    (#x10000 . :MH_BINDS_TO_WEAK)
    (#x20000 . :MH_ALLOW_STACK_EXECUTION)
    (#x40000 . :MH_ROOT_SAFE                                         )
    (#x80000 . :MH_SETUID_SAFE)
    (#x100000 . :MH_NO_REEXPORTED_DYLIBS)
    (#x200000 . :MH_PIE)
    (#x400000 . :MH_DEAD_STRIPPABLE_DYLIB)
    (#x800000 . :MH_HAS_TLV_DESCRIPTORS)
    (#x1000000 . :MH_NO_HEAP_EXECUTION)
    (#x2000000 . :MH_APP_EXTENSION_SAFE)))

;; The magic number is already parsed
;; Returns (mv erp header bytes).
(defun parse-mach-o-header-32 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp cputype bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       (cputype (lookup-safe cputype *mach-o-CPU-types*))
       ((mv erp cpusubtype bytes) (parse-u32 bytes)) ; TODO: decode
       ((when erp) (mv erp nil bytes))
       ((mv erp filetype bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       (filetype (lookup-safe filetype *mach-o-filetypes*))
       ((when (not (eq :MH_EXECUTE filetype)))
        (mv :unsupported-filetype
            (er hard? 'parse-mach-o-header-32 "Unsupported filetype: ~x0." filetype)
            bytes))
       ((mv erp ncmds bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp sizeofcmds bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp flags bytes) (parse-u32 bytes)) ;TODO: decode
       ((when erp) (mv erp nil bytes)))
    (mv nil
        (list (cons :cputype cputype)
                (cons :cpusubtype cpusubtype)
                (cons :filetype filetype)
                (cons :ncmds ncmds)
                (cons :sizeofcmds sizeofcmds)
                (cons :flags (decode-flags flags *mach-o-header-flags-alist*)))
          bytes)))

;; The magic number is already parsed
;; Returns (mv erp header bytes).
(defun parse-mach-o-header-64 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp cputype bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       (cputype (lookup-safe cputype *mach-o-CPU-types*))
       ((mv erp cpusubtype bytes) (parse-u32 bytes)) ; TODO: decode
       ((when erp) (mv erp nil bytes))
       ((mv erp filetype bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       (filetype (lookup-safe filetype *mach-o-filetypes*))
       ((when (not (eq :MH_EXECUTE filetype)))
        (mv :unsupported-filetype
            (er hard? 'parse-mach-o-header-64 "Unsupported filetype: ~x0." filetype)
            bytes))
       ((mv erp ncmds bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp sizeofcmds bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp flags bytes) (parse-u32 bytes))    ;TODO: decode
       ((when erp) (mv erp nil bytes))
       ((mv erp reserved bytes) (parse-u32 bytes)) ;drop from the result?
       ((when erp) (mv erp nil bytes))
       )
      (mv nil
          (list (cons :cputype cputype)
                (cons :cpusubtype cpusubtype)
                (cons :filetype filetype)
                (cons :ncmds ncmds)
                (cons :sizeofcmds sizeofcmds)
                (cons :flags (decode-flags flags *mach-o-header-flags-alist*))
                (cons :reserved reserved))
          bytes)))

(defconst *mach-o-section-types*
  '((#x0 . :S_REGULAR)
    (#x1 . :S_ZEROFILL)
    (#x2 . :S_CSTRING_LITERALS)
    (#x3 . :S_4BYTE_LITERALS)
    (#x4 . :S_8BYTE_LITERALS)
    (#x5 . :S_LITERAL_POINTERS)
    (#x6 . :S_NON_LAZY_SYMBOL_POINTERS)
    (#x7 . :S_LAZY_SYMBOL_POINTERS)
    (#x8 . :S_SYMBOL_STUBS)
    (#x9 . :S_MOD_INIT_FUNC_POINTERS)
    (#xa . :S_MOD_TERM_FUNC_POINTERS)
    (#xb . :S_COALESCED)
    (#xc . :S_GB_ZEROFILL)
    (#xd . :S_INTERPOSING)
    (#xe . :S_16BYTE_LITERALS)
    (#xf . :S_DTRACE_DOF)
    (#x10 . :S_LAZY_DYLIB_SYMBOL_POINTERS)
    (#x11 . :S_THREAD_LOCAL_REGULAR)
    (#x12 . :S_THREAD_LOCAL_ZEROFILL)
    (#x13 . :S_THREAD_LOCAL_VARIABLES)
    (#x14 . :S_THREAD_LOCAL_VARIABLE_POINTERS)
    (#x15 . :S_THREAD_LOCAL_INIT_FUNCTION_POINTERS)))

(defconst *mach-o-section-attributes*
  '((#x80000000 . :S_ATTR_PURE_INSTRUCTIONS)
    (#x40000000 . :S_ATTR_NO_TOC)
    (#x20000000 . :S_ATTR_STRIP_STATIC_SYMS)
    (#x10000000 . :S_ATTR_NO_DEAD_STRIP)
    (#x08000000 . :S_ATTR_LIVE_SUPPORT)
    (#x04000000 . :S_ATTR_SELF_MODIFYING_CODE)
    (#x02000000 . :S_ATTR_DEBUG)
    (#x00000400 . :S_ATTR_SOME_INSTRUCTIONS)
    (#x00000200 . :S_ATTR_EXT_RELOC)
    (#x00000100 . :S_ATTR_LOC_RELOC)))

;; Returns (mv erp section bytes).
(defun parse-mach-o-section (expected-segname all-bytes bytes)
  (declare (xargs :guard (and (stringp expected-segname)
                              (byte-listp all-bytes)
                              (byte-listp bytes))))
  (b* (((mv erp sectname bytes) (parse-n-bytes-into-string 16 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp segname bytes) (parse-n-bytes-into-string 16 bytes))
       ((when erp) (mv erp nil bytes))
       ;;it's not clear why the segment name is stored here as well as
       ;;in the overarching load command for the segment
       ((when (not (equal segname expected-segname)))
        (mv :segname-mismatch
            (er hard? 'parse-mach-o-section "Segname mismatch (expected ~x0, got ~x1)." expected-segname segname)
            bytes))
       ((mv erp addr bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp size bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp offset bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp align bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp reloff bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp nreloc bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp flags bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       (section-type (logand #xff flags))
       (section-type (lookup-safe section-type *mach-o-section-types*))
       (section-attributes (decode-flags flags *mach-o-section-attributes*))
       ((mv erp reserved1 bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp reserved2 bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ;; look up the contents of the section:
       ((mv erp contents &) (if (member-eq section-type '(:S_ZEROFILL :S_GB_ZEROFILL :S_THREAD_LOCAL_ZEROFILL))
                                (mv nil `(:zero-fill ,size) nil) ;special handling for zerofill sections (don't try to read data from a meaningless offset)
                              (parse-n-bytes size (nthcdr offset all-bytes))))
       ((when erp) (mv erp nil bytes)))
      (mv nil
          (list (cons :sectname sectname)
                (cons :type section-type)
                (cons :segname segname)
                (cons :addr addr)
                (cons :size size)
                (cons :offset offset)
                (cons :align align)
                (cons :reloff reloff)
                (cons :nreloc nreloc)
                (cons :attributes section-attributes)
                (cons :reserved1 reserved1)
                (cons :reserved2 reserved2)
                (cons :contents contents)
                )
          bytes)))

;; Returns (mv erp section bytes).
(defun parse-mach-o-section-64 (expected-segname all-bytes bytes)
  (declare (xargs :guard (and (stringp expected-segname)
                              (byte-listp all-bytes)
                              (byte-listp bytes))))
  (b* (((mv erp sectname bytes) (parse-n-bytes-into-string 16 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp segname bytes) (parse-n-bytes-into-string 16 bytes))
       ((when erp) (mv erp nil bytes))
       ;;it's not clear why the segment name is stored here as well as
       ;;in the overarching load command for the segment
       ((when (not (equal segname expected-segname)))
        (mv :segname-mismatch
            (er hard? 'parse-mach-o-section-64 "Segname mismatch (expected ~x0, got ~x1)." expected-segname segname)
            bytes))
       ((mv erp addr bytes) (parse-u64 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp size bytes) (parse-u64 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp offset bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp align bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp reloff bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp nreloc bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp flags bytes) (parse-u32 bytes)) ;TODO: decode the section attributes
       ((when erp) (mv erp nil bytes))
       (section-type (logand #xff flags))
       (section-type (lookup-safe section-type *mach-o-section-types*))
       (section-attributes (decode-flags flags *mach-o-section-attributes*))
       ((mv erp reserved1 bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp reserved2 bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp reserved3 bytes) (parse-u32 bytes))  ;NOTE: This field is not in Mach-O_File_Format.pdf, but it is in loader.h
       ((when erp) (mv erp nil bytes))
       ;; look up the contents of the section:
       ((mv erp contents &) (if (member-eq section-type '(:S_ZEROFILL :S_GB_ZEROFILL :S_THREAD_LOCAL_ZEROFILL))
                                (mv nil `(:zero-fill ,size) nil) ;special handling for zerofill sections (don't try to read data from a meaningless offset)
                              (parse-n-bytes size (nthcdr offset all-bytes))))
       ((when erp) (mv erp nil bytes)))
    (mv nil
        (list (cons :sectname sectname)
              (cons :type section-type)
              (cons :segname segname)
              (cons :addr addr)
              (cons :size size)
              (cons :offset offset)
              (cons :align align)
              (cons :reloff reloff)
              (cons :nreloc nreloc)
              (cons :attributes section-attributes)
              (cons :reserved1 reserved1)
              (cons :reserved2 reserved2)
              (cons :reserved3 reserved3)
              (cons :contents contents))
        bytes)))

;; Returns (mv erp sections bytes).
(defun parse-mach-o-sections (nsects expected-segname acc all-bytes bytes)
  (declare (xargs :guard (and (natp nsects)
                              (stringp expected-segname)
                              (true-listp acc)
                              (byte-listp all-bytes)
                              (byte-listp bytes))))
  (if (zp nsects)
      (mv nil (reverse acc) bytes)
    (b* (((mv erp section bytes) (parse-mach-o-section expected-segname all-bytes bytes))
         ((when erp) (mv erp nil bytes)))
      (parse-mach-o-sections (+ -1 nsects) expected-segname (cons section acc) all-bytes bytes))))

;; Returns (mv erp sections bytes).
(defun parse-mach-o-sections-64 (nsects expected-segname acc all-bytes bytes)
  (declare (xargs :guard (and (natp nsects)
                              (stringp expected-segname)
                              (true-listp acc)
                              (byte-listp all-bytes)
                              (byte-listp bytes))))
  (if (zp nsects)
      (mv nil (reverse acc) bytes)
    (b* (((mv erp section bytes) (parse-mach-o-section-64 expected-segname all-bytes bytes))
         ((when erp) (mv erp nil bytes)))
        (parse-mach-o-sections-64 (+ -1 nsects) expected-segname (cons section acc) all-bytes bytes))))

(defconst *mach-o-stab-symbol-types*
  '((#x20 . :N_GSYM)
    (#x22 . :N_FNAME)
    (#x24 . :N_FUN)
    (#x26 . :N_STSYM)
    (#x28 . :N_LCSYM)
    (#x2e . :N_BNSYM)
    (#x32 . :N_AST)
    (#x3c . :N_OPT)
    (#x40 . :N_RSYM)
    (#x44  . :N_SLINE)
    (#x4e . :N_ENSYM)
    (#x60 . :N_SSYM)
    (#x64 . :N_SO)
    (#x66 . :N_OSO)
    (#x80 . :N_LSYM)
    (#x82 . :N_BINCL)
    (#x84 . :N_SOL)
    (#x86 . :N_PARAMS)
    (#x88 . :N_VERSION)
    (#x8A . :N_OLEVEL)
    (#xa0  . :N_PSYM)
    (#xa2 . :N_EINCL)
    (#xa4 . :N_ENTRY)
    (#xc0 . :N_LBRAC)
    (#xc2 . :N_EXCL)
    (#xe0 . :N_RBRAC)
    (#xe2 . :N_BCOMM)
    (#xe4 . :N_ECOMM)
    (#xe8 . :N_ECOML)
    (#xfe . :N_LENG)
    (#x30 . :N_PC)))

;TODO: Theis comes from merging the constants in nlist.h with those described in the PDF
(defconst *mach-o-symbol-n-types*
  '((#x00 . :N_UNDF)
    (#x02 . :N_ABS)
    (#x04 . :N_TEXT)
    (#x06 . :N_DATA)
    (#x08 . :N_BSS)
    (#x12 . :N_COMM)
    (#x1e . :N_FN)
    (#x0e . :N_SECT)
    (#x0c . :N_PBUD)
    (#x0a . :N_INDR)))

;; Returns (mv erp result bytes).
(defun parse-mach-o-nlist (string-table bytes)
  (declare (xargs :guard (and (byte-listp string-table)
                              (byte-listp bytes))))
  (b* (((mv erp n-strx bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-type bytes) (parse-u8 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-sect bytes) (parse-u8 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-desc bytes) (parse-u16 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-value bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       (stabp (not (eql 0 (logand #xe0 n-type))))
       (n-type (if stabp
                   (lookup-safe n-type *mach-o-stab-symbol-types*)
                 (b* ((n-pext (not (eql 0 (logand #x10 n-type))))
                      (n-type (logand #x0e n-type))
                      (n-ext (not (eql 0 (logand #x01 n-type)))))
                     (list (cons :n-pext n-pext)
                           (cons :n-type (lookup-safe n-type *mach-o-symbol-n-types*))
                           (cons :n-ext n-ext)))))
       (string (if (eql 0 n-strx) ;todo: check that this special case is appropriate (it's suggested by the PDF)
                   ""
                 (coerce (map-code-char (keep-non-zeros (nthcdr n-strx string-table))) 'string))))
      (mv nil
          (list (cons :string string)
                ;;(cons :n-strx n-strx)
                (cons :n-type n-type)
                (cons :n-sect n-sect)
                (cons :n-desc n-desc)
                (cons :n-value n-value))
          bytes)))

;; Returns (mv erp result).
(defun parse-mach-o-nlists (nsyms acc string-table bytes)
  (declare (xargs :guard (and (natp nsyms)
                              (true-listp acc)
                              (byte-listp string-table)
                              (byte-listp bytes))))
  (if (zp nsyms)
      (mv nil (reverse acc))
    (b* (((mv erp sym bytes) (parse-mach-o-nlist string-table bytes))
         ((when erp) (mv erp nil)))
      (parse-mach-o-nlists (+ -1 nsyms) (cons sym acc) string-table bytes))))

;; Returns (mv erp result bytes).
(defun parse-mach-o-nlist-64 (string-table bytes)
  (declare (xargs :guard (and (byte-listp string-table)
                              (byte-listp bytes))))
  (b* (((mv erp n-strx bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-type bytes) (parse-u8 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-sect bytes) (parse-u8 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-desc bytes) (parse-u16 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp n-value bytes) (parse-u64 bytes))
       ((when erp) (mv erp nil bytes))
       (string (if (eql 0 n-strx) ;todo: check that this special case is appropriate (it's suggested by the PDF)
                   ""
                 (coerce (map-code-char (keep-non-zeros (nthcdr n-strx string-table))) 'string)))
       (stabp (not (= 0 (logand #xe0 n-type))))
       (n-type (if stabp
                   (lookup-safe n-type *mach-o-stab-symbol-types*)
                 (b* ((n-pext (not (= 0 (logand #x10 n-type))))
                      (n-type (logand #x0e n-type))
                      (n-ext (not (= 0 (logand #x01 n-type)))))
                     (list (cons :n-pext n-pext)
                           (cons :n-type (lookup-safe n-type *mach-o-symbol-n-types*))
                           (cons :n-ext n-ext))))))
      (mv nil
          (list (cons :string string)
                ;; (cons :n-strx n-strx)
                (cons :n-type n-type)
                (cons :n-sect n-sect)
                (cons :n-desc n-desc)
                (cons :n-value n-value))
          bytes)))

;; Returns (mv erp result).
(defun parse-mach-o-nlist-64s (nsyms acc string-table bytes)
  (declare (xargs :guard (and (natp nsyms)
                              (true-listp acc)
                              (byte-listp string-table)
                              (byte-listp bytes))))
  (if (zp nsyms)
      (mv nil (reverse acc))
    (b* (((mv erp sym bytes) (parse-mach-o-nlist-64 string-table bytes))
         ((when erp) (mv erp nil)))
        (parse-mach-o-nlist-64s (+ -1 nsyms) (cons sym acc) string-table bytes))))

(defconst *mach-o-segment-flags*
  '((#x1 . :SG_HIGHVM)
    (#x2 . :SG_FVMLIB)
    (#x4 . :SG_NORELOC)
    (#x8 . :SG_PROTECTED_VERSION_1)))

; Returns (mv erp cmd-data).
;; Note that the caller adds the cmd itself to the alist returned.
(defun parse-mach-o-load-command (cmd ; the type of the command
                                  architecture
                                  all-bytes
                                  bytes)
  (declare (xargs :guard (and (symbolp cmd)
                              (member architecture '(32 64))
                              (byte-listp all-bytes)
                              (byte-listp bytes))))
  (let ((cmd-data nil)) ;empty accumulator (TODO: remove)
    ;; for all of the options below, the cmd and cmdsize are already parsed:
    (cond ((eq cmd :LC_UUID)
           (b* (((mv erp uuid &) (parse-n-bytes 16 bytes)) ;todo: assemble the value
                ((when erp) (mv erp nil))
                (cmd-data (acons :uuid uuid cmd-data)))
               (mv nil cmd-data)))
          ((eq cmd :LC_SEGMENT)
           (b* (((mv erp segname bytes) (parse-n-bytes-into-string 16 bytes))
                ((when erp) (mv erp nil))
                ((mv erp vmaddr bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp vmsize bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp fileoff bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp filesize bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp maxprot bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp initprot bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp nsects bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp flags bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ;; now come the sections commands:
                ((mv erp sections &) (parse-mach-o-sections nsects segname nil all-bytes bytes))
                ((when erp) (mv erp nil)))
               (mv nil
                   (list (cons :segname segname)
                         (cons :vmaddr vmaddr)
                         (cons :vmsize vmsize)
                         (cons :fileoff fileoff)
                         (cons :filesize filesize)
                         (cons :maxprot maxprot)
                         (cons :initprot initprot)
                         (cons :nsects nsects)
                         (cons :flags (decode-flags flags *mach-o-segment-flags*))
                         (cons :sections sections)))))
          ((eq cmd :LC_SEGMENT_64)
           (b* (((mv erp segname bytes) (parse-n-bytes-into-string 16 bytes))
                ((when erp) (mv erp nil))
                ((mv erp vmaddr bytes) (parse-u64 bytes))
                ((when erp) (mv erp nil))
                ((mv erp vmsize bytes) (parse-u64 bytes))
                ((when erp) (mv erp nil))
                ((mv erp fileoff bytes) (parse-u64 bytes))
                ((when erp) (mv erp nil))
                ((mv erp filesize bytes) (parse-u64 bytes))
                ((when erp) (mv erp nil))
                ((mv erp maxprot bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp initprot bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp nsects bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ((mv erp flags bytes) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                ;; now come the sections commands:
                ((mv erp sections &) (parse-mach-o-sections-64 nsects segname nil all-bytes bytes))
                ((when erp) (mv erp nil)))
               (mv nil
                   (list (cons :segname segname)
                          (cons :vmaddr vmaddr)
                          (cons :vmsize vmsize)
                          (cons :fileoff fileoff)
                          (cons :filesize filesize)
                          (cons :maxprot maxprot)
                          (cons :initprot initprot)
                          (cons :nsects nsects)
                          (cons :flags (decode-flags flags *mach-o-segment-flags*))
                          (cons :sections sections)))))
          ((eq cmd :LC_TWOLEVEL_HINTS)
           (b* (((mv erp offset bytes) (parse-u32 bytes)) ;todo: dereference
                ((when erp) (mv erp nil))
                (cmd-data (acons :offset offset cmd-data))
                ((mv erp nhints &) (parse-u32 bytes))
                ((when erp) (mv erp nil))
                (cmd-data (acons :nhints nhints cmd-data)))
               (mv nil cmd-data)))
          ((eq cmd :LC_DYLD_INFO_ONLY)
           (prog2$ (cw "NOTE: Ignoring unsupported command type: ~x0.~%" cmd)
                   (mv nil (acons :unsupported t nil))))
          ((eq cmd :LC_SYMTAB) ;TODO: look this up?
             (b* (((mv erp symoff bytes) (parse-u32 bytes))
                  ((when erp) (mv erp nil))
                  ((mv erp nsyms bytes) (parse-u32 bytes))
                  ((when erp) (mv erp nil))
                  ((mv erp stroff bytes) (parse-u32 bytes))
                  ((when erp) (mv erp nil))
                  ((mv erp strsize &) (parse-u32 bytes))
                  ((when erp) (mv erp nil))
                  ((mv erp string-table &) (parse-n-bytes strsize (nthcdr stroff all-bytes)))  ;todo: make an nthcdr-safe and use it here
                  ((when erp) (mv erp nil))
                  ((mv erp syms) (if (eql architecture 32)
                                     (parse-mach-o-nlists nsyms nil string-table (nthcdr symoff all-bytes))
                                   (parse-mach-o-nlist-64s nsyms nil string-table (nthcdr symoff all-bytes))))
                  ((when erp) (mv erp nil)))
                 (mv nil
                     (list ;(cons :symoff symoff)
                           ;(cons :nsyms nsyms)
                           ;(cons :stroff stroff)
                           ;(cons :strsize strsize)
                           (cons :syms syms)
                           ;; Make it into one big string, for readability:
                           (cons :string-table (coerce (map-code-char string-table) 'string))))))
          ((eq cmd :LC_MAIN)
           (b* (((mv erp entryoff bytes) (parse-u64 bytes))
                ((when erp) (mv erp nil))
                ((mv erp stacksize &) (parse-u64 bytes))
                ((when erp) (mv erp nil)))
             (mv nil
                 (list (cons :entryoff entryoff)
                       (cons :stacksize stacksize)))))
          ;;TODO: Add more!
          (t (prog2$ (cw "NOTE: Ignoring unsupported command type: ~x0.~%" cmd)
                     (mv nil ; :unsupported-comment-type
                         (acons :unsupported t nil)))
             ;; (mv (er hard 'parse-mach-o-load-command "Unsupported command type: ~x0." cmd)
             ;;     bytes)
             ))))

; Returns (mv erp cmds).
(defun parse-mach-o-load-commands (ncmds acc architecture all-bytes bytes)
  (declare (xargs :guard (and (natp ncmds)
                              (true-listp acc)
                              (member architecture '(32 64))
                              (byte-listp all-bytes)
                              (byte-listp bytes))))
  (if (zp ncmds)
      (mv nil (reverse acc))
    (b* ((orig-bytes bytes)
         ((mv erp cmd-u32 bytes) (parse-u32 bytes))
         ((when erp) (mv erp nil))
         ((mv erp cmdsize bytes) (parse-u32 bytes))
         ((when erp) (mv erp nil))
         (cmd (lookup cmd-u32 *mach-o-load-commands*)))
      (if (not cmd)
          (b* ((- (cw "NOTE: Ignoring unsupported load command: ~x0.~%" cmd-u32))
               (bytes (nthcdr cmdsize orig-bytes)))
            (parse-mach-o-load-commands (+ -1 ncmds) acc architecture all-bytes bytes))
        (b* (((mv erp cmd-data)
              (parse-mach-o-load-command cmd architecture all-bytes bytes))
             ((when erp) (mv erp nil))
             (acc (cons (acons :cmd cmd ; (acons :cmdsize cmdsize
                               cmd-data ;)
                               )
                        acc))
             ;; For robustness, we discard exactly cmdsize bytes here,
             ;; regardless of how many were actually consumed (TODO: add a
             ;; check):
             (bytes (nthcdr cmdsize orig-bytes)))
          (parse-mach-o-load-commands (+ -1 ncmds) acc architecture all-bytes bytes))))))

;; Returns (mv erp result).
(defun parse-mach-o-file-bytes (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* ((all-bytes bytes) ;capture for later looking up things at given offsets
       ;; Parse the magic number:
       ((mv erp magic bytes) (parse-u32 bytes))
       ((when erp) (mv erp nil))
       (magic (lookup magic *mach-o-magic-numbers*))
       ((when (not magic))
        (er hard? 'parse-mach-o-file-bytes "Bad magic number: ~x0." magic)
        (mv :bad-magic-number nil))
       (architecture (if (member-eq magic *32-bit-magic-numbers*) 32 64)) ; todo: change to pass a 64-bitp value
       ;; Parse the header:
       ((mv erp header bytes)
        (if (eql architecture 32)
            (parse-mach-o-header-32 bytes)
          (parse-mach-o-header-64 bytes)))
       ((when erp) (mv erp nil))
       ;; Parse the load-commands:
       (ncmds (lookup-eq-safe :ncmds header))
       ((mv erp cmds) (parse-mach-o-load-commands ncmds nil architecture all-bytes bytes))
       ((when erp) (mv erp nil)))
    (mv nil
        (list (cons :magic magic)
              (cons :header header)
              (cons :cmds cmds)
              (cons :bytes all-bytes) ; todo: some bytes are replicated in the :contents fields of sections!  avoid that.
              ))))

;; ;; Parse a file that is known to be a Mach-O executable.  Returns (mv
;; ;; erp contents state) where contents in an alist representing the
;; ;; contents of the Mach-O executable.
;; (defun parse-mach-o-file (filename state)
;;   (declare (xargs :guard (stringp filename)
;;                   :stobjs state
;; ;                  :mode :program
;;                   ))
;;   (b* (((mv existsp state) (file-existsp filename state))
;;        ((when (not existsp))
;;         (progn$ (cw "ERROR in parse-for-mach-o-file: File does not exist: ~x0." filename)
;;                 (exit 1) ;return non-zero exit status ;todo: do we really want this?
;;                 (mv :file-does-not-exist nil state)))
;;        ((mv erp bytes state) (read-file-into-byte-list filename state))
;;        ((when erp)
;;         (er hard 'parse-mach-o-file "Failed to read any bytes from file: ~x0." filename) ; todo: should we exit here, like we do above?
;;         (mv erp nil state))
;;        ;; Parse the bytes read:
;;        (parsed-mach-o-file (parse-mach-o-file-bytes bytes)))
;;     (mv nil parsed-mach-o-file state)))
