; A parser for PE executables
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also build-book-for-pe-file.lisp.

;; TODO: Collect any warnings / errors and include them in the parsed output somehow?

(include-book "parser-utils")
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "std/io/read-file-bytes" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv/getbit-def" :dir :system)
(include-book "kestrel/typed-lists-light/bytes-to-printable-string" :dir :system)
(include-book "kestrel/typed-lists-light/map-code-char" :dir :system)
(local (include-book "std/typed-lists/integer-listp" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;todo: use len-at-least
(defun at-least-n-bytes-left (n bytes)
  (declare (xargs :guard (and (posp n)
                              (true-listp bytes))))
  (consp (nthcdr (- n 1) bytes))) ;we take all but the last and assert there is at least one more

(defconst *expected-sig*
  (list (char-code #\P)
        (char-code #\E)
        0
        0))

;in BV form (note the byte order):
(defconst *pe-signature* #x00004550) ;todo: get this by packing *expected-sig*

;; Returns the PE signature offset, or nil if there are not enough bytes.  The
;; offset to the PE signature is a u32 at location #x3c.
(defun pe-sig-offset (all-bytes)
  (declare (xargs :guard (integer-listp all-bytes)))
  (b* (((when (not (at-least-n-bytes-left (+ 4 #x3c) all-bytes)))
        (prog2$ (cw "NOTE: Not enough bytes to get the PE signature offset.~%")
                nil))
       (bytes (nthcdr #x3c all-bytes))
       ((mv pe-sig-offset &)
        (parse-u32 bytes)))
    pe-sig-offset))

;; Skips ahead to the PE signature (so this skips over any extra stuff between the true MS-DOS stub and the PE signature)
(defun parse-ms-dos-stub (bytes)
  (declare (xargs :guard (integer-listp bytes)))
  (b* ((pe-sig-offset (pe-sig-offset bytes))
       ((when (not pe-sig-offset))
        (mv (er hard? 'parse-ms-dos-stub "Failed to get the offset to the PE signature.")
            nil))
       ;; consume all bytes up to the given offset (there may be extra stuff after the MS-DOS stub)
       (ms-dos-stub (take-safe-ctx pe-sig-offset bytes 'parse-ms-dos-stub))
       (bytes (nthcdr pe-sig-offset bytes)))
    (mv ms-dos-stub bytes)))

;; Returns the PE signature, or NIL if there are not enough bytes in the file.
;; This may often be called on a non-PE file, so it needs to be safe.
(defun pe-file-signature (bytes)
  (declare (xargs :guard (integer-listp bytes)))
  (b* ((pe-sig-offset (pe-sig-offset bytes))
       ((when (not pe-sig-offset))
        nil) ;maybe this is not even a PE file.
       ;; (- (cw "NOTE: Offset to pe-sig would be ~x0.~%" pe-sig-offset))
       ((when (not (at-least-n-bytes-left (+ 4 pe-sig-offset) bytes)))
        (prog2$ (cw "NOTE: Not enough bytes to read a PE signature at offset ~x0.~%" pe-sig-offset)
                nil))
       (bytes (nthcdr pe-sig-offset bytes))
       ((mv sig &) (parse-u32 bytes)))
    sig))

(defconst *machine-types*
  '((#x0 . :IMAGE_FILE_MACHINE_UNKNOWN)
    (#x1d3 . :IMAGE_FILE_MACHINE_AM33)
    (#x8664 . :IMAGE_FILE_MACHINE_AMD64)
    (#x1c0 . :IMAGE_FILE_MACHINE_ARM)
    (#xaa64 . :IMAGE_FILE_MACHINE_ARM64)
    (#x1c4 . :IMAGE_FILE_MACHINE_ARMNT)
    (#xebc . :IMAGE_FILE_MACHINE_EBC)
    (#x14c . :IMAGE_FILE_MACHINE_I386)
    (#x200 . :IMAGE_FILE_MACHINE_IA64)
    (#x9041 . :IMAGE_FILE_MACHINE_M32R)
    (#x266 . :IMAGE_FILE_MACHINE_MIPS16)
    (#x366 . :IMAGE_FILE_MACHINE_MIPSFPU)
    (#x466 . :IMAGE_FILE_MACHINE_MIPSFPU16)
    (#x1f0 . :IMAGE_FILE_MACHINE_POWERPC)
    (#x1f1 . :IMAGE_FILE_MACHINE_POWERPCFP)
    (#x166 . :IMAGE_FILE_MACHINE_R4000)
    (#x5032 . :IMAGE_FILE_MACHINE_RISCV32)
    (#x5064 . :IMAGE_FILE_MACHINE_RISCV64)
    (#x5128 . :IMAGE_FILE_MACHINE_RISCV128)
    (#x1a2 . :IMAGE_FILE_MACHINE_SH3)
    (#x1a3 . :IMAGE_FILE_MACHINE_SH3DSP)
    (#x1a6 . :IMAGE_FILE_MACHINE_SH4)
    (#x1a8 . :IMAGE_FILE_MACHINE_SH5)
    (#x1c2 . :IMAGE_FILE_MACHINE_THUMB)
    (#x169 . :IMAGE_FILE_MACHINE_WCEMIPSV2)))

(defconst *magic-numbers*
  '((#x10b . :PE32)
    (#x20b . :PE32+)))

(defconst *pe-characteristic-flags-alist*
  '((#x0001 . :IMAGE_FILE_RELOCS_STRIPPED)
    (#x0002 . :IMAGE_FILE_EXECUTABLE_IMAGE)
    (#x0004 . :IMAGE_FILE_LINE_NUMS_STRIPPED)
    (#x0008 . :IMAGE_FILE_LOCAL_SYMS_STRIPPED)
    (#x0010 . :IMAGE_FILE_AGGRESSIVE_WS_TRIM)
    (#x0020 . :IMAGE_FILE_LARGE_ADDRESS_AWARE)
    (#x0040 . :IMAGE_FILE_16BIT_MACHINE)
    (#x0080 . :IMAGE_FILE_BYTES_REVERSED_LO)
    (#x0100 . :IMAGE_FILE_32BIT_MACHINE)
    (#x0200 . :IMAGE_FILE_DEBUG_STRIPPED)
    (#x0400 . :IMAGE_FILE_REMOVABLE_RUN_FROM_SWAP)
    (#x1000 . :IMAGE_FILE_SYSTEM)
    (#x2000 . :IMAGE_FILE_DLL)
    (#x4000 . :IMAGE_FILE_UP_SYSTEM_ONLY)
    (#x8000 . :IMAGE_FILE_BYTES_REVERSED_HI)))

(defun parse-coff-file-header (bytes)
;  (declare (xargs :guard (integer-listp bytes)))   ;todo: check for not enough bytes (using len-at-least)
  (b* ((header nil)
       ;; machine:
       ((mv machine bytes) (parse-u16 bytes))
       (header (acons :machine (lookup-safe machine *machine-types*) header))
       ;; number-of-sections:
       ((mv number-of-sections bytes) (parse-u16 bytes))
       (header (acons :number-of-sections number-of-sections header))
       ;; time-date-stamp:
       ((mv time-date-stamp bytes) (parse-u32 bytes))
       (header (acons :time-date-stamp time-date-stamp header))
       ;; pointer-to-symbol-table:
       ((mv pointer-to-symbol-table bytes) (parse-u32 bytes))
       ;; pecoff.pdf says: "This value should be zero for an image because COFF debugging information is deprecated."
       ;; However, non-zero values seem to happen a lot.
       (- (and (not (eql 0 pointer-to-symbol-table))
               (cw "NOTE: Non-zero pointer to symbol table (deprecated): ~x0.~%" pointer-to-symbol-table)))
       (header (acons :pointer-to-symbol-table pointer-to-symbol-table header))
       ;; number-of-symbols:
       ((mv number-of-symbols bytes) (parse-u32 bytes))
       ;; pecoff.pdf says: This value should be zero for an image because COFF debugging information is deprecated.
       ;; However, non-zero values seem to happen a lot.
       (- (and (not (eql 0 number-of-symbols))
               (cw "NOTE: Non-zero number of symbols (deprecated): ~x0.~%" number-of-symbols)))
       (header (acons :number-of-symbols number-of-symbols header))
       ;; size-of-optional-header:
       ((mv size-of-optional-header bytes) (parse-u16 bytes))
       (header (acons :size-of-optional-header size-of-optional-header header)) ;TODO: Use this to decide whether to parse an optional-header
       ;; characteristics:
       ((mv characteristics bytes) (parse-u16 bytes))
       (header (acons :characteristics (decode-flags characteristics
                                                     *pe-characteristic-flags-alist*)
                      header)))
      (mv (reverse header) bytes)))

(defun parse-optional-header-standard-fields (bytes)
  (b* ((header nil)
       ((mv magic-number bytes) (parse-u16 bytes))
       (magic (lookup-safe magic-number *magic-numbers*))
       (header (acons :magic magic header))
       ((mv major-linker-version bytes) (parse-u8 bytes))
       (header (acons :major-linker-version major-linker-version header))
       ((mv minor-linker-version bytes) (parse-u8 bytes))
       (header (acons :minor-linker-version minor-linker-version header))
       ((mv size-of-code bytes) (parse-u32 bytes))
       (header (acons :size-of-code size-of-code header))
       ((mv size-of-initialized-data bytes) (parse-u32 bytes))
       (header (acons :size-of-initialized-data size-of-initialized-data header))
       ((mv size-of-uninitialized-data bytes) (parse-u32 bytes))
       (header (acons :size-of-uninitialized-data size-of-uninitialized-data header))
       ((mv address-of-entry-point bytes) (parse-u32 bytes))
       (header (acons :address-of-entry-point address-of-entry-point header))
       ((mv base-of-code bytes) (parse-u32 bytes))
       (header (acons :base-of-code base-of-code header))
       ((mv header bytes)
        (if (eq magic :pe32)
            ;; this field is only for PE32:
            (b* (((mv base-of-data bytes) (parse-u32 bytes))
                 (header (acons :base-of-data base-of-data header)))
                (mv header bytes))
          (mv header bytes))))
    (mv (reverse header) bytes)))

(defconst *windows-subsystems*
  '((0 . :IMAGE_SUBSYSTEM_UNKNOWN)
    (1 . :IMAGE_SUBSYSTEM_NATIVE)
    (2 . :IMAGE_SUBSYSTEM_WINDOWS_GUI)
    (3 . :IMAGE_SUBSYSTEM_WINDOWS_CUI)
    (7 . :IMAGE_SUBSYSTEM_POSIX_CUI)
    (9 . :IMAGE_SUBSYSTEM_WINDOWS_CE_GUI)
    (10 . :IMAGE_SUBSYSTEM_EFI_APPLICATION)
    (11 . :IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER)
    (12 . :IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER)
    (13 . :IMAGE_SUBSYSTEM_EFI_ROM)
    (14 . :IMAGE_SUBSYSTEM_XBOX)))

(defconst *dll-characteristics-flags-alist*
  '((#x0001 . :RESERVED)
    (#x0002 . :RESERVED)
    (#x0004 . :RESERVED)
    (#x0008 . :RESERVED)
    (#x0020 . :IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA)
    (#x0040 . :IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE)
    (#x0080 . :IMAGE_DLLCHARACTERISTICS_FORCE_INTEGRITY)
    (#x0100 . :IMAGE_DLLCHARACTERISTICS_NX_COMPAT)
    (#x0200 . :IMAGE_DLLCHARACTERISTICS_NO_ISOLATION)
    (#x0400 . :IMAGE_DLLCHARACTERISTICS_NO_SEH)
    (#x0800 . :IMAGE_DLLCHARACTERISTICS_NO_BIND)
    (#x1000 . :IMAGE_DLLCHARACTERISTICS_APPCONTAINER)
    (#x2000 . :IMAGE_DLLCHARACTERISTICS_WDM_DRIVER)
    (#x4000 . :IMAGE_DLLCHARACTERISTICS_GUARD_CF)
    (#x8000 . :IMAGE_DLLCHARACTERISTICS_TERMINAL_SERVER_AWARE)))

(defun parse-optional-header-windows-specific-fields (magic bytes)
  (b* ((header nil)
       ((mv image-base bytes) (if (eq :pe32 magic) (parse-u32 bytes) (parse-u64 bytes)))
       (header (acons :image-base image-base header))
       ((mv section-alignment bytes) (parse-u32 bytes))
       (header (acons :section-alignment section-alignment header))
       ((mv file-alignment bytes) (parse-u32 bytes))
       (header (acons :file-alignment file-alignment header))
       ((mv major-operating-system-version bytes) (parse-u16 bytes))
       (header (acons :major-operating-system-version major-operating-system-version header))
       ((mv minor-operating-system-version bytes) (parse-u16 bytes))
       (header (acons :minor-operating-system-version minor-operating-system-version header))
       ((mv major-image-version bytes) (parse-u16 bytes))
       (header (acons :major-image-version major-image-version header))
       ((mv minor-image-version bytes) (parse-u16 bytes))
       (header (acons :minor-image-version minor-image-version header))
       ((mv major-subsystem-version bytes) (parse-u16 bytes))
       (header (acons :major-subsystem-version major-subsystem-version header))
       ((mv minor-subsystem-version bytes) (parse-u16 bytes))
       (header (acons :minor-subsystem-version minor-subsystem-version header))
       ((mv win-32-version-value bytes) (parse-u32 bytes))
       ((when (not (eql 0 win-32-version-value)))
        (mv (er hard 'parse-optional-header-windows-specific-fields "Win32VersionValue should be 0.")
              bytes))
       ((mv size-of-image bytes) (parse-u32 bytes))
       (header (acons :size-of-image size-of-image header))
       ((mv size-of-headers bytes) (parse-u32 bytes))
       (header (acons :size-of-headers size-of-headers header))
       ((mv check-sum bytes) (parse-u32 bytes))
       (header (acons :check-sum check-sum header))
       ((mv subsystem bytes) (parse-u16 bytes))
       (header (acons :subsystem (lookup-safe subsystem *windows-subsystems*) header)) ;todo: better error message if no match
       ((mv dll-characteristics bytes) (parse-u16 bytes))
       (header (acons :dll-characteristics (decode-flags dll-characteristics *dll-characteristics-flags-alist*) header))
       ((mv size-of-stack-reserve bytes) (if (eq :pe32 magic) (parse-u32 bytes) (parse-u64 bytes)))
       (header (acons :size-of-stack-reserve size-of-stack-reserve header))
       ((mv size-of-stack-commit bytes) (if (eq :pe32 magic) (parse-u32 bytes) (parse-u64 bytes)))
       (header (acons :size-of-stack-commit size-of-stack-commit header))
       ((mv size-of-heap-reserve bytes) (if (eq :pe32 magic) (parse-u32 bytes) (parse-u64 bytes)))
       (header (acons :size-of-heap-reserve size-of-heap-reserve header))
       ((mv size-of-heap-commit bytes) (if (eq :pe32 magic) (parse-u32 bytes) (parse-u64 bytes)))
       (header (acons :size-of-heap-commit size-of-heap-commit header))
       ((mv loader-flags bytes) (parse-u32 bytes))
       (- (if (not (eql 0 loader-flags))
              (cw "ERROR: LoaderFlags should be 0, but they are ~x0." loader-flags) ;todo: store them?
            nil))
       ((mv number-of-rva-and-sizes bytes) (parse-u32 bytes))
       (header (acons :number-of-rva-and-sizes number-of-rva-and-sizes header)))
      (mv (reverse header) bytes)))

(defun parse-optional-data-directories-aux (num bytes acc)
  (if (zp num)
      (mv (reverse acc) bytes)
    (b* (((mv rva bytes) (parse-u32 bytes))
         ((mv size bytes) (parse-u32 bytes))
         (data-directory (acons :rva rva (acons :size size nil))))
        (parse-optional-data-directories-aux (+ -1 num) bytes (cons data-directory acc)))))

(defun pair-data-directories-with-names (data-directories names)
  (if (endp data-directories)
      nil ;The data-directories may run out before the names
    (acons (first names)
           (first data-directories)
           (pair-data-directories-with-names (rest data-directories) (rest names)))))

(defconst *data-directory-names*
  '(:export-table
    :import-table
    :resource-table
    :exception-table
    :certificate-table
    :base-relocation-table
    :debug
    :architecture
    :global-ptr
    :tls-table
    :load-config-table
    :bound-import
    :iat
    :delay-import-descriptor
    :clr-runtime-header
    :reserved ;;TODO: Check that this one is 0 if it is used
    ))

;TODO: check that we don't run out of names before we run out of directories
(defun parse-optional-data-directories (number-of-rva-and-sizes bytes)
  (b* (((mv data-directories bytes)
        (parse-optional-data-directories-aux number-of-rva-and-sizes bytes nil)))
      (mv (pair-data-directories-with-names data-directories *data-directory-names*)
          bytes)))

(defun keep-bytes-until-0 (bytes)
  (if (endp bytes)
      nil
    (if (eql 0 (first bytes))
        nil
      (cons (first bytes) (keep-bytes-until-0 (rest bytes))))))

;; the string will be null-terminated if shorter than name-bytes, and we drop the null
(defun name-to-string (name-bytes)
  (let* ((name-bytes (keep-bytes-until-0 name-bytes))
         (name-chars (map-code-char name-bytes)) ;TODO; Handle UTF-8 !
         (name-string (coerce name-chars 'string)))
    name-string))

;; See also http://lxr.free-electrons.com/source/include/linux/pe.h
(defconst *pe-section-characteristic-flags-alist*
  '(;(#x00000000 . :RESERVED) ;0 doesn't even make sense... (the author of pe.h in Linux seems to agree)
    (#x00000001 . :RESERVED)
    (#x00000002 . :RESERVED)
    (#x00000004 . :RESERVED)
    (#x00000008 . :IMAGE_SCN_TYPE_NO_PAD)
    (#x00000010 . :RESERVED)
    (#x00000020 . :IMAGE_SCN_CNT_CODE)
    (#x00000040 . :IMAGE_SCN_CNT_INITIALIZED_DATA)
    (#x00000080 . :IMAGE_SCN_CNT_UNINITIALIZED_DATA)
    (#x00000100 . :IMAGE_SCN_LNK_OTHER)
    (#x00000200 . :IMAGE_SCN_LNK_INFO)
    (#x00000400 . :RESERVED)
    (#x00000800 . :IMAGE_SCN_LNK_REMOVE)
    (#x00001000 . :IMAGE_SCN_LNK_COMDAT)
    (#x00002000 . :RESERVED)
    (#x00004000 . :RESERVED)
    (#x00008000 . :IMAGE_SCN_GPREL)
    (#x00010000 . :IMAGE_SCN_MEM_PURGEABLE) ;this is given as hex 00020000 in pecoff.pdf, but that seems to be a mistake (the author of pe.h agrees)
    (#x00020000 . :IMAGE_SCN_MEM_16BIT)
    (#x00040000 . :IMAGE_SCN_MEM_LOCKED)
    (#x00080000 . :IMAGE_SCN_MEM_PRELOAD)
    ;; the next nibble does not represent a proper bit field (meaning is
    ;; assigned to values such as 3 that have more than 1 bit set -- and this
    ;; meaning is not the conjunction of the meanings of values 1 and 2). So we
    ;; will handle this nibble separately.
    ;; ...values omitted here...
    (#x01000000 . :IMAGE_SCN_LNK_NRELOC_OVFL) ;TODO: Handle this overflow case
    (#x02000000 . :IMAGE_SCN_MEM_DISCARDABLE)
    (#x04000000 . :IMAGE_SCN_MEM_NOT_CACHED)
    (#x08000000 . :IMAGE_SCN_MEM_NOT_PAGED)
    (#x10000000 . :IMAGE_SCN_MEM_SHARED)
    (#x20000000 . :IMAGE_SCN_MEM_EXECUTE)
    (#x40000000 . :IMAGE_SCN_MEM_READ)
    (#x80000000 . :IMAGE_SCN_MEM_WRITE)))

; what about #x0 and #xF ?
(defconst *pe-section-characteristic-alignment-flags-values*
  '((#x1 . :IMAGE_SCN_ALIGN_1BYTES)
    (#x2 . :IMAGE_SCN_ALIGN_2BYTES)
    (#x3 . :IMAGE_SCN_ALIGN_4BYTES)
    (#x4 . :IMAGE_SCN_ALIGN_8BYTES)
    (#x5 . :IMAGE_SCN_ALIGN_16BYTES)
    (#x6 . :IMAGE_SCN_ALIGN_32BYTES)
    (#x7 . :IMAGE_SCN_ALIGN_64BYTES)
    (#x8 . :IMAGE_SCN_ALIGN_128BYTES)
    (#x9 . :IMAGE_SCN_ALIGN_256BYTES)
    (#xA . :IMAGE_SCN_ALIGN_512BYTES)
    (#xB . :IMAGE_SCN_ALIGN_1024BYTES)
    (#xC . :IMAGE_SCN_ALIGN_2048BYTES)
    (#xD . :IMAGE_SCN_ALIGN_4096BYTES)
    (#xE . :IMAGE_SCN_ALIGN_8192BYTES)))

(defconst *char-to-digit-alist*
  (list (cons (char-code #\0) 0)
        (cons (char-code #\1) 1)
        (cons (char-code #\2) 2)
        (cons (char-code #\3) 3)
        (cons (char-code #\4) 4)
        (cons (char-code #\5) 5)
        (cons (char-code #\6) 6)
        (cons (char-code #\7) 7)
        (cons (char-code #\8) 8)
        (cons (char-code #\9) 9)))

(defun decode-ascii-number (bytes curr)
  (if (endp bytes)
      curr
    (let* ((byte (first bytes))
           (curr (* 10 curr))
           (curr (+ curr (lookup-safe byte *char-to-digit-alist*))))
      (decode-ascii-number (rest bytes) curr))))

(defun drop-leading-zeros (bytes)
  (if (endp bytes)
      nil
    (if (eql 0 (first bytes))
        (drop-leading-zeros (rest bytes))
      bytes)))

(defun drop-trailing-zeros (bytes)
  (reverse (drop-leading-zeros (reverse bytes))))

(defun decode-section-name (name-bytes string-table-bytes)
  (if (and (consp name-bytes)
           (equal (first name-bytes) (char-code #\/)))
      (if (not string-table-bytes)
          :unknown ;todo: print a message
        (b* ((name-bytes (drop-trailing-zeros name-bytes))
             ;;(- (cw "trimmed bytes: ~x0. string-table-bytes: ~x1." name-bytes string-table-bytes))
             (string-table-index (decode-ascii-number (rest name-bytes) 0))
             (string-table-offset (- string-table-index 4)) ; 4 for the string table size
             ;; (- (cw "string-table-offset: ~x0" string-table-offset))
             )
          ;; todo: check that there are enough bytes:
          (name-to-string (nthcdr string-table-offset string-table-bytes))))
    (name-to-string name-bytes)))

;; TODO: Add the special handling for $ in section names in object files.
(defun parse-section-header (file-type bytes string-table-bytes)
  ;;(declare (xargs :guard (member-eq file-type '(:image :object))))
  (b* ((header nil) ;to accumulate results
       ((mv name-bytes bytes) (parse-n-bytes 8 bytes))
       ;; (- (cw "section name-bytes: ~x0~%" name-bytes))
       (name (decode-section-name name-bytes string-table-bytes))
       (header (acons :name name header))
       ((mv virtual-size bytes) (parse-u32 bytes))
       (header (acons :virtual-size virtual-size header))
       ((mv virtual-address bytes) (parse-u32 bytes))
       (header (acons :virtual-address virtual-address header))
       ((mv size-of-raw-data bytes) (parse-u32 bytes))
       (header (acons :size-of-raw-data size-of-raw-data header))
       ((mv pointer-to-raw-data bytes) (parse-u32 bytes))
       (header (acons :pointer-to-raw-data pointer-to-raw-data header))
       ((mv pointer-to-relocations bytes) (parse-u32 bytes))
       (header (acons :pointer-to-relocations pointer-to-relocations header))
       ((mv pointer-to-line-numbers bytes) (parse-u32 bytes))
       (header (acons :pointer-to-line-numbers pointer-to-line-numbers header))
       ((mv number-of-relocations bytes) (parse-u16 bytes))
       (header (acons :number-of-relocations number-of-relocations header))
       ((mv number-of-line-numbers bytes) (parse-u16 bytes))
       (header (acons :number-of-line-numbers number-of-line-numbers header))
       ((mv characteristics-val bytes) (parse-u32 bytes))
       ;;(characteristics (bvxor 32 #xFF0FFFFF characteristics-val)) not really needed
       (characteristics (decode-flags characteristics-val *pe-section-characteristic-flags-alist*))
       (characteristics (if (eq file-type :object) ;the alignment stuff is only valid for object files
                            (b* ((special-nibble (slice 23 20 characteristics-val)) ;this nibble is not a proper bitfield
                                 (alignment (lookup special-nibble *pe-section-characteristic-alignment-flags-values*))
                                 (alignment (or alignment :unknown-alignment)))
                              (cons alignment characteristics))
                          characteristics))
       (header (acons :characteristics characteristics header)))
      (mv (reverse header) bytes)))

(defun parse-section-headers (number-of-sections file-type acc bytes string-table-bytes)
  ;(declare (xargs :guard (member-eq file-type '(:image :object))))
  (if (zp number-of-sections)
      (mv (reverse acc) bytes)
    (b* (((mv section-header bytes) (parse-section-header file-type bytes string-table-bytes)))
        (parse-section-headers (+ -1 number-of-sections) file-type (cons section-header acc) bytes string-table-bytes))))

(defun parse-section (section-header all-bytes len-all-bytes acc)
  (let* ((name (lookup-eq-safe :name section-header))
         (size-of-raw-data (lookup-eq-safe :size-of-raw-data section-header))
         (pointer-to-raw-data (lookup-eq-safe :pointer-to-raw-data section-header))
         (raw-data (if (> (+ size-of-raw-data pointer-to-raw-data) len-all-bytes)
                       (prog2$ (cw "ERROR: Not enough bytes for the section ~x0 (start: ~x1, length: ~x2, total bytes: ~x3).~%"
                                   name pointer-to-raw-data size-of-raw-data len-all-bytes)
                               nil ;:not-enough-bytes
                               )
                     (take size-of-raw-data (nthcdr pointer-to-raw-data all-bytes))))
         (section-info (acons :header section-header ;TODO: inline the fields here?
                              (acons :raw-data raw-data
                                     (acons :raw-data-as-string (bytes-to-printable-string raw-data)
                                            nil)))))
    (acons name section-info acc)))

(defun parse-sections (section-headers acc all-bytes len-all-bytes)
  (if (endp section-headers)
      (reverse acc)
    (let ((acc (parse-section (first section-headers) all-bytes len-all-bytes acc)))
      (parse-sections (rest section-headers) acc all-bytes len-all-bytes))))

;bytes has length 8
(defun interpret-symbol-name (bytes string-table-bytes)
  (if (equal '(0 0 0 0) (take 4 bytes))
      (b* (((mv offset &) (parse-u32 (nthcdr 4 bytes))))
        (name-to-string (nthcdr offset string-table-bytes))) ;todo: slow?  use an array?)
    (name-to-string bytes)))

(defconst *section-number-values-alist*
  '((0 . :IMAGE_SYM_UNDEFINED)
    (-1 . :IMAGE_SYM_ABSOLUTE)
    (-2 . :IMAGE_SYM_DEBUG)))

(defun interpret-section-number (val)
  (if (assoc val *section-number-values-alist*)
      (lookup val *section-number-values-alist*)
    val))

;; Returns (mv entry bytes)
(defund parse-symbol-table-entry (bytes string-table-bytes)
  (b* ((entry nil) ;empty alist
       ((mv name-bytes bytes) (parse-n-bytes 8 bytes))
       (name (interpret-symbol-name name-bytes string-table-bytes))
       (entry (acons :name name entry))
       ((mv value bytes) (parse-u32 bytes))
       (entry (acons :value value entry))  ;todo parse value better?
       ((mv section-number bytes) (parse-u16 bytes)) ;todo parse better!
       (section-number (logext 16 section-number)) ;it's a signed integer, 1-based
       (section-number (interpret-section-number section-number))
       (entry (acons :section-number section-number entry))
       ((mv type bytes) (parse-u16 bytes)) ;todo parse better!
       (entry (acons :type type entry))
       ((mv storage-class bytes) (parse-u8 bytes)) ;todo parse better!
       (entry (acons :storage-class storage-class entry))
       ((mv number-of-aux-symbols bytes) (parse-u8 bytes)) ;todo parse better!
       (entry (acons :number-of-aux-symbols number-of-aux-symbols entry))
       ;; todo: call something like "parse n bytes" here:
       (aux-symbol-data (take (* 18 number-of-aux-symbols) bytes))
       (bytes (nthcdr (* 18 number-of-aux-symbols) bytes))
       (entry (acons :aux-symbol-data aux-symbol-data entry))
       (entry (reverse entry))
       )
    (mv entry bytes)))

(defthm len-of-mv-nth-1-of-parse-symbol-table-entry
  (implies (consp bytes)
           (< (len (mv-nth 1 (parse-symbol-table-entry bytes string-table-bytes)))
              (len bytes)))
  :hints (("Goal" :in-theory (e/d (parse-symbol-table-entry) (len)))))

;the len of bytes should be a multiple of 18
;; Returns the list of entries
(defun parse-symbol-table (bytes string-table-bytes)
  (declare (xargs :measure (len bytes)))
  (if (endp bytes)
      nil
    (mv-let (entry bytes)
      (parse-symbol-table-entry bytes string-table-bytes) ;consumes 1 or more symbols
      (cons entry
            (parse-symbol-table bytes string-table-bytes)))))

(defun map-code-char-tail (bytes acc)
  (if (endp bytes)
      (reverse acc)
    (map-code-char-tail (rest bytes)
                        (cons (code-char (first bytes))
                              acc))))

;; Returns the string table as a list of bytes
(defun parse-string-table (bytes)
  (b* (((when (not (at-least-n-bytes-left 4 bytes)))
        (er hard 'parse-string-table "Can't read string table size."))
       ((mv size bytes) (parse-u32 bytes)) ;the size includes these 4 bytes
       (size-of-string-part (- size 4))
       ((when (< size-of-string-part 0))
        (er hard 'parse-string-table "Negative size for string data in string table."))
       ((when (not (at-least-n-bytes-left size-of-string-part bytes)))
        (er hard 'parse-string-table "Can't read string table (not enough data)."))
       (bytes (take size-of-string-part bytes)) ;; these bytes include a bunch of null-terminated strings
       )
    bytes))

(defun bytes-to-string (bytes)
  (let* ((chars (map-code-char-tail bytes nil)) ;TODO; Handle UTF-8 ??
         (string (coerce chars 'string)))
    string))

;; Returns an alist representing the contents of the PE file
(defun parse-pe-file-bytes (bytes)
  (b* ((all-bytes bytes)
       (pe nil) ;initially empty alist to accumulate results
       ;; Parse the ms-dos-stub:
       ((mv ms-dos-stub bytes)
        (parse-ms-dos-stub bytes))
       (pe (acons :ms-dos-stub ms-dos-stub pe)) ;checked by PARSED-EXECUTABLE-TYPE
       (pe (acons :ms-dos-stub-as-string (bytes-to-printable-string ms-dos-stub) pe))
       ;; Parse the PE signature
       ((mv sig bytes) (parse-n-bytes 4 bytes))
       ((when (not (equal sig *expected-sig*)))
        (er hard 'parse-pe "Bad signature (~x0)" sig))
       ;;(pe (acons :sig sig pe))
       (pe (acons :sig-as-string (bytes-to-printable-string sig) pe))
       ;; Parse the coff-file-header:
       ((mv coff-file-header bytes) (parse-coff-file-header bytes))
       (pe (acons :coff-file-header coff-file-header pe))
       ;; Parse the symbol table:
       (pointer-to-symbol-table (lookup-eq-safe :pointer-to-symbol-table coff-file-header))
       (number-of-symbols (lookup-eq-safe :number-of-symbols coff-file-header))
       (symbol-table-size (* 18 ;number of bytes per symbol
                             number-of-symbols))
       ;; Parse the string table:
       (string-table-start (+ pointer-to-symbol-table symbol-table-size))
       (symbol-table-existsp (not (eql 0 pointer-to-symbol-table))) ;assuming 0 means there is no string table either
       (string-table-existsp symbol-table-existsp)
       (string-table-bytes (if string-table-existsp
                               (parse-string-table (nthcdr string-table-start all-bytes))
                             nil))
       (string-table (if string-table-existsp
                         (bytes-to-string string-table-bytes)
                       :none))
       (pe (acons :string-table string-table pe))
       (symbol-table-bytes (take symbol-table-size (nthcdr pointer-to-symbol-table all-bytes)))
       (symbol-table (if symbol-table-existsp (parse-symbol-table symbol-table-bytes string-table-bytes) :none))
       (pe (acons :symbol-table symbol-table pe))
       ;; Parse the optional-header:
       ((mv optional-header-standard-fields bytes) (parse-optional-header-standard-fields bytes))
       (pe (acons :optional-header-standard-fields optional-header-standard-fields pe))
       (magic (lookup-eq-safe :magic optional-header-standard-fields))
       ((mv optional-header-windows-specific-fields bytes) (parse-optional-header-windows-specific-fields magic bytes))
       (pe (acons :optional-header-windows-specific-fields optional-header-windows-specific-fields pe))
       (number-of-rva-and-sizes (lookup-eq-safe :number-of-rva-and-sizes optional-header-windows-specific-fields))
       ((mv optional-data-directories bytes) (parse-optional-data-directories number-of-rva-and-sizes bytes))
       (pe (acons :optional-data-directories optional-data-directories pe))
       ;; TODO: Cross-check with the size of the optional-header (stored in the file header)
       (number-of-sections (lookup-eq-safe :number-of-sections coff-file-header))
       (- (cw "~x0 section(s).~%" number-of-sections))
       ;; The final bytes are essentially ignored here:
       ((mv section-headers bytes) (parse-section-headers number-of-sections :image nil bytes string-table-bytes))
       (- (cw "~x0 bytes after section headers.~%" (len bytes)))
       ;; (pe (acons :section-headers section-headers pe)) ;; the header is now included in the parsed data for its section
       ;; Here we stop processing the bytes in order, instead looking up each section's start in all-bytes:
       (sections (parse-sections section-headers nil all-bytes (len all-bytes)))
       (pe (acons :sections sections pe))
       ;;TODO: What other data do we need to parse?
       ) ;todo: Can we somehow check that all bytes are used?
    (reverse pe)))

;; Parse a file that is known to be a PE executable.  Returns (mv
;; contents state) where contents in an alist representing the
;; contents of the PE executable.
(defun parse-pe-file (filename state)
  (declare (xargs :stobjs state
                  :verify-guards nil
                  :guard (stringp filename)))
  (b* (((mv existsp state)
        (file-existsp filename state))
       ((when (not existsp))
        (progn$ (cw "ERROR in parse-for-pe-file: File does not exist: ~x0." filename)
                (exit 1) ;return non-zero exit status
                (mv t state)))
       ((mv bytes state)
        (read-file-bytes filename state))
       ((when (not (consp bytes))) ;I've seen this be a string error message
        (prog2$ (er hard 'parse-pe-file "Failed to read any bytes from file: ~x0.  Result: ~x1" filename bytes)
                (mv t state)))
       ;; Parse the bytes read:
       (parsed-pe-file (parse-pe-file-bytes bytes)))
    (mv parsed-pe-file state)))

;dup
(defund my-all-equal (x lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) t)
        (t (and (equal x (car lst))
                (my-all-equal x (cdr lst))))))

;move?
;; Returns a list of entries.
(defun parse-import-directory-table (bytes)
  (declare (xargs ;; :guard (and (acl2::all-unsigned-byte-p 8 bytes)
            ;;              (true-listp bytes))
            :measure (len bytes)
                  ))
  (if (< (len bytes) 20)
      (er hard? 'parse-import-directory-table "Not enough bytes.")
    (if (my-all-equal 0 (take 20 bytes))
        nil ;null entry means end of table
      (b* (((mv import-lookup-table-rva bytes) (parse-u32 bytes))
           ((mv time/date-stamp bytes) (parse-u32 bytes))
           ((mv forwarder-chain bytes) (parse-u32 bytes))
           ((mv name-rva bytes) (parse-u32 bytes))
           ((mv import-address-table-rva bytes) (parse-u32 bytes)))
        (cons (acons :import-lookup-table-rva import-lookup-table-rva
                     (acons :time/date-stamp time/date-stamp
                            (acons :forwarder-chain forwarder-chain
                                   (acons :name-rva name-rva
                                          (acons :import-address-table-rva import-address-table-rva nil)))))
              (parse-import-directory-table bytes))))))

;; Get data at the given RVA from the sections, chopping it down to size bytes
;; (and checking that there are that many) if size is not :unknown.
(defun get-data-from-sections (sections rva size)
  ;; (declare (xargs :guard (or (posp size)
  ;;                            (eq :unknown size))))
  (if (endp sections)
      (er hard? 'get-data-from-sections "No more sections.  Did not find RVA ~x0." rva)
    (let* ((section (first sections))
           (section-name (car section))
           (section-info (cdr section))
           (header (lookup-eq-safe :header section-info))
           (section-rva (lookup-eq-safe :VIRTUAL-ADDRESS header))
           (section-size (lookup-eq-safe :VIRTUAL-SIZE header)))
      (if (and (<= section-rva rva)
               (< rva (+ section-rva section-size)))
          (let ((bytes-before-target (- rva section-rva)))
            ;; The RVA is in this section:
            (if (and (not (eq :unknown size))
                     (< (- section-size bytes-before-target)
                        size))
                (er hard? 'get-data-from-sections "RVA ~x0 found in section ~x1 (start: ~x2, size: ~x3) but not enough bytes (need ~x4)."
                    rva
                    section-name
                    section-rva
                    section-size
                    size)
              (let ((bytes (nthcdr bytes-before-target (lookup-eq-safe :raw-data section-info))))
                (if (eq :unknown size)
                    bytes
                  (take size bytes)))))
        ;; RVA is not in this section, so keep looking
        (get-data-from-sections (rest sections) rva size)))))

;; Returns a byte list
(defun read-bytes-of-null-terminated-string (bytes)
  (if (endp bytes)
      (er hard? 'read-bytes-of-null-terminated-string "No null-terminator found for string.")
    (let ((byte (first bytes)))
      (if (= 0 byte) ;found the null
          nil
        (cons byte (read-bytes-of-null-terminated-string (rest bytes)))))))

(defun get-string-from-sections (sections rva)
  (if (endp sections)
      (er hard? 'get-string-from-sections "No more sections.  Did not find RVA ~x0." rva)
    (let* ((section (first sections))
           ;(section-name (car section))
           (section-info (cdr section))
           (header (lookup-eq-safe :header section-info))
           (section-rva (lookup-eq-safe :VIRTUAL-ADDRESS header))
           (section-size (lookup-eq-safe :VIRTUAL-SIZE header)))
      (if (and (<= section-rva rva)
               (< rva (+ section-rva section-size)))
          (let* ((bytes-before-target (- rva section-rva))
                 (bytes (nthcdr bytes-before-target (lookup-eq-safe :raw-data section-info)))
                 (string-bytes (read-bytes-of-null-terminated-string bytes))
                 (string (coerce (map-code-char string-bytes) 'string))
                 )
            string)
        ;; RVA is not in this section, so keep looking
        (get-string-from-sections (rest sections) rva)))))

(defun parse-hint/name-table-entry-bytes (bytes)
  (b* (((mv hint bytes) (parse-u16 bytes))
       (string-bytes (read-bytes-of-null-terminated-string bytes))
       (string (coerce (map-code-char string-bytes) 'string)))
    (acons :hint hint
           (acons :name string
                  nil))))

(defun parse-import-lookup-table-bytes (bytes magic sections)
;  (declare (xargs :guard (member-eq magic '(strip-cdrs *magic-numbers*))))
  (declare (xargs :measure (len bytes)))
  (if (< (len bytes) (if (eq magic :pe32) 4 8))
      (er hard? 'parse-import-lookup-table-bytes "Not enough bytes")
    (b* (((mv item bytes) (if (eq magic :pe32)
                              (parse-u32 bytes)
                            (parse-u64 bytes))))
      (if (= 0 item)
          ;; no more items
          nil
        (let* ((most-significant-bit (if (eq magic :pe32)
                                         (getbit 31 item)
                                       (getbit 63 item)))
               (import-info
                (if (= 1 most-significant-bit)
                    ;; import by ordinal:
                    (acons :ordinal-number (bvchop 16 item)
                           nil)
                  ;;import by name:
                  (let* ((hint/name-table-rva (bvchop 31 item))
                         (hint/name-table-entry-bytes (get-data-from-sections sections hint/name-table-rva :unknown))
                         (hint/name-info (parse-hint/name-table-entry-bytes hint/name-table-entry-bytes))
                         )
                    hint/name-info))))
          (cons import-info
                (parse-import-lookup-table-bytes bytes magic sections)))))))

(defun lookup-import-directory-table-entries (import-directory-table sections magic)
  (if (endp import-directory-table)
      nil
    (let* ((entry (first import-directory-table))
           (name-rva (lookup-eq-safe :name-rva entry))
           (dll-name (get-string-from-sections sections name-rva))
           (import-address-table-rva (lookup-eq-safe :import-address-table-rva entry))
           (import-address-table-bytes (get-data-from-sections sections import-address-table-rva :unknown))
           )
      (cons (cons dll-name
                  (parse-import-lookup-table-bytes import-address-table-bytes magic sections))
            (lookup-import-directory-table-entries (rest import-directory-table) sections magic)))))

;; TODO: Make the result of this more compact
;; TODO: Can this get overwritten in memory at runtime?
(defun get-import-info (parsed-pe-file)
  (b* ((optional-header-standard-fields (lookup-eq-safe :optional-header-standard-fields parsed-pe-file))
       (magic (lookup-eq-safe :magic optional-header-standard-fields))
       (sections (lookup-eq-safe :sections parsed-pe-file))
       (import-table-info
        (lookup-eq-safe :import-table
                        (lookup-eq-safe :optional-data-directories
                                        parsed-pe-file)))
       (import-table-rva (lookup-eq-safe :rva import-table-info))
       (import-table-size (lookup-eq-safe :size import-table-info))

       (import-table-bytes (get-data-from-sections sections import-table-rva import-table-size))
       (import-directory-table (parse-import-directory-table import-table-bytes))
       (import-dll-info (lookup-import-directory-table-entries import-directory-table sections magic)))
    (list import-directory-table
          import-dll-info)))
