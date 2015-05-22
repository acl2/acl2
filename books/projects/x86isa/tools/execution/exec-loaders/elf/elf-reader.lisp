;; ORIGINAL AUTHORS:
;; Soumava Ghosh <soumava@cs.utexas.edu>
;; Shilpi Goel   <shigoel@cs.utexas.edu>

;; ===================================================================

(in-package "X86ISA")

(include-book "elf-stobj"
              :ttags
              (:syscall-exec :include-raw :other-non-det :undef-flg))

(set-ignore-ok t)

;; -------------------------------------------------------------------
;; Function to recursively read a location at an offset of a given
;; byte-list and return the list of bytes until a null is encountered
;; -------------------------------------------------------------------

(defun elf-read-mem-null-term (byte-list offset)
  (declare (xargs :measure (nfix (- (len byte-list) offset))
                  :guard-debug t
                  :guard (and (natp offset)
                              (<= offset (len byte-list)))
                  :verify-guards nil))
  (if (natp offset)
      (if (< offset (len byte-list))
          (let* ((val (car (nthcdr offset byte-list))))
            (if (equal 0 val)
                (cons 0 nil)
              (cons val
                    (elf-read-mem-null-term byte-list
                                            (1+ offset)))))
        (cons 0 nil))
    nil))

;; -------------------------------------------------------------------
;; Function to read a null terminated string from a given offset
;; of a byte-list
;; -------------------------------------------------------------------

(defun elf-read-string-null-term (byte-list offset)
  (declare (xargs :guard (and (natp offset)
                              (<= offset (len byte-list)))
                  :verify-guards nil))
  (let* ((bytes (elf-read-mem-null-term byte-list offset))
         (charlist (bytes-to-charlist bytes)))
    (coerce charlist 'string)))

;; -------------------------------------------------------------------
;; Function to read segment headers from the binary
;; -------------------------------------------------------------------

(defun read-segment-headers (nsegments rest-of-the-file acc)
  (declare (xargs :guard (and (natp nsegments)
                              (byte-listp rest-of-the-file)
                              (true-listp acc))))
  (if (zp nsegments)
      (reverse acc)

    (b* (((mv p_type   rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv p_flags  rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv p_offset rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv p_vaddr  rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv p_paddr  rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv p_filesz rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv p_memsz  rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv p_align  rest-of-the-file) (rnbni 8 rest-of-the-file))
         (segment
          (list (cons 'type   p_type)
                (cons 'flags  p_flags)
                (cons 'offset p_offset)
                (cons 'vaddr  p_vaddr)
                (cons 'paddr  p_paddr)
                (cons 'filesz p_filesz)
                (cons 'memsz  p_memsz)
                (cons 'align  p_align))))
        (read-segment-headers (1- nsegments) rest-of-the-file
                              (cons segment acc)))))

;; -------------------------------------------------------------------
;; Function to read section headers from the binary
;; -------------------------------------------------------------------

(defun read-section-headers (nsections rest-of-the-file acc)
  (declare (xargs :guard (and (natp nsections)
                              (byte-listp rest-of-the-file)
                              (true-listp acc))))
  (if (zp nsections)
      (reverse acc)

    (b* (((mv sh_name      rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv sh_type      rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv sh_flags     rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv sh_addr      rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv sh_offset    rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv sh_size      rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv sh_link      rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv sh_info      rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv sh_addralign rest-of-the-file) (rnbni 8 rest-of-the-file))
         ((mv sh_entsize   rest-of-the-file) (rnbni 8 rest-of-the-file))
         (section
          (list (cons 'name      sh_name)
                (cons 'type      sh_type)
                (cons 'flags     sh_flags)
                (cons 'addr      sh_addr)
                (cons 'offset    sh_offset)
                (cons 'size      sh_size)
                (cons 'link      sh_link)
                (cons 'info      sh_info)
                (cons 'addralign sh_addralign)
                (cons 'entsize   sh_entsize))))
        (read-section-headers (1- nsections) rest-of-the-file
                              (cons section acc)))))

;; -------------------------------------------------------------------
;; Function to read the ELF header from the first 64 bytes
;; -------------------------------------------------------------------

(defun read-elf-header (file-header)
  (declare (xargs :guard (and (byte-listp file-header)
                              (= (len file-header) 64))))
  (b* (((mv e_magic     file-header) (rnbbi 4 file-header))
       ((mv e_class     file-header) (rnbni 1 file-header))
       ((mv e_dataenc   file-header) (rnbni 1 file-header))
       ((mv e_identver  file-header) (rnbni 1 file-header))
       ((mv e_osabi     file-header) (rnbni 1 file-header))
       ((mv e_abiver    file-header) (rnbni 1 file-header))
       ((mv e_padding   file-header) (rnbbi 7 file-header))
       ((mv e_type      file-header) (rnbni 2 file-header))
       ((mv e_machine   file-header) (rnbni 2 file-header))
       ((mv e_version   file-header) (rnbni 4 file-header))
       ((mv e_entry     file-header) (rnbni 8 file-header))
       ((mv e_phoff     file-header) (rnbni 8 file-header))
       ((mv e_shoff     file-header) (rnbni 8 file-header))
       ((mv e_flags     file-header) (rnbni 4 file-header))
       ((mv e_ehsize    file-header) (rnbni 2 file-header))
       ((mv e_phentsize file-header) (rnbni 2 file-header))
       ((mv e_phnum     file-header) (rnbni 2 file-header))
       ((mv e_shentsize file-header) (rnbni 2 file-header))
       ((mv e_shnum     file-header) (rnbni 2 file-header))
       ((mv e_shstrndx  file-header) (rnbni 2 file-header)))
      (list (cons 'magic     e_magic)
            (cons 'class     e_class)
            (cons 'dataenc   e_dataenc)
            (cons 'identver  e_identver)
            (cons 'osabi     e_osabi)
            (cons 'abiver    e_abiver)
            (cons 'padding   e_padding)
            (cons 'type      e_type)
            (cons 'machine   e_machine)
            (cons 'version   e_version)
            (cons 'entry     e_entry)
            (cons 'phoff     e_phoff)
            (cons 'shoff     e_shoff)
            (cons 'flags     e_flags)
            (cons 'ehsize    e_ehsize)
            (cons 'phentsize e_phentsize)
            (cons 'phnum     e_phnum)
            (cons 'shentsize e_shentsize)
            (cons 'shnum     e_shnum)
            (cons 'shstrndx  e_shstrndx))))

;; -------------------------------------------------------------------
;; Function to read the names of the section headers from the string
;; section table, located at the offset indicated by the sh_offset
;; value of the e_shstrndx th section in the list of sections
;; -------------------------------------------------------------------

(defun read-section-names (remaining-sections string-section-data acc)
  (declare (xargs :guard (and (true-listp acc)
                              (byte-listp string-section-data))
                  :verify-guards nil))
  (if (not (consp remaining-sections))
      acc

    (b* ((section-header (car remaining-sections))
         (name-str-offset (cdr (assoc 'name section-header)))
         (name-str (elf-read-string-null-term string-section-data
                                              name-str-offset))
         (new-section-header (append (cons (cons 'name-str name-str) nil)
                                     section-header)))
        (read-section-names (cdr remaining-sections)
                            string-section-data
                            (cons new-section-header acc)))))

;; -------------------------------------------------------------------
;; Function to fill the data segment bytes into the stobj
;; -------------------------------------------------------------------

(defun set-stobj-fields (sections file-bytes elf)
  (declare (xargs :stobjs (elf)
                  :guard (byte-listp file-bytes)
                  :verify-guards nil))
  (if (not (consp sections))
      elf
    (b* ((section (car sections))
         (section-name (cdr (assoc 'name-str section)))
         (name-bytes (combine-bytes (string-to-bytes section-name)))
         (addr (cdr (assoc 'addr section)))
         (offset (cdr (assoc 'offset section)))
         (size (cdr (assoc 'size section)))
         (elf
          (case name-bytes
            (#.*note_abi_tag*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!note-ABI-tag-addr addr elf))
                  (elf (!note-ABI-tag-offset offset elf))
                  (elf (!note-ABI-tag-size size elf))
                  (elf (!note-ABI-tag-bytes bytes elf)))
                 elf))

            (#.*note_gnu_build_id*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!note-gnu-buildid-addr addr elf))
                  (elf (!note-gnu-buildid-offset offset elf))
                  (elf (!note-gnu-buildid-size size elf))
                  (elf (!note-gnu-buildid-bytes bytes elf)))
                 elf))

            (#.*rela_plt*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!rela-plt-addr addr elf))
                  (elf (!rela-plt-offset offset elf))
                  (elf (!rela-plt-size size elf))
                  (elf (!rela-plt-bytes bytes elf)))
                 elf))

            (#.*init*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!init-addr addr elf))
                  (elf (!init-offset offset elf))
                  (elf (!init-size size elf))
                  (elf (!init-bytes bytes elf)))
                 elf))

            (#.*plt*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!plt-addr addr elf))
                  (elf (!plt-offset offset elf))
                  (elf (!plt-size size elf))
                  (elf (!plt-bytes bytes elf)))
                 elf))

            (#.*elf-text*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!text-addr addr elf))
                  (elf (!text-offset offset elf))
                  (elf (!text-size size elf))
                  (elf (!text-bytes bytes elf)))
                 elf))

            (#.*fini*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!fini-addr addr elf))
                  (elf (!fini-offset offset elf))
                  (elf (!fini-size size elf))
                  (elf (!fini-bytes bytes elf)))
                 elf))

            (#.*rodata*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!rodata-addr addr elf))
                  (elf (!rodata-offset offset elf))
                  (elf (!rodata-size size elf))
                  (elf (!rodata-bytes bytes elf)))
                 elf))

            (#.*eh_frame*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!eh-frame-addr addr elf))
                  (elf (!eh-frame-offset offset elf))
                  (elf (!eh-frame-size size elf))
                  (elf (!eh-frame-bytes bytes elf)))
                 elf))

            (#.*gcc_except_table*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!gcc-except-table-addr addr elf))
                  (elf (!gcc-except-table-offset offset elf))
                  (elf (!gcc-except-table-size size elf))
                  (elf (!gcc-except-table-bytes bytes elf)))
                 elf))

            (#.*init_array*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!init-array-addr addr elf))
                  (elf (!init-array-offset offset elf))
                  (elf (!init-array-size size elf))
                  (elf (!init-array-bytes bytes elf)))
                 elf))

            (#.*fini_array*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!fini-array-addr addr elf))
                  (elf (!fini-array-offset offset elf))
                  (elf (!fini-array-size size elf))
                  (elf (!fini-array-bytes bytes elf)))
                 elf))

            (#.*ctors*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!ctors-addr addr elf))
                  (elf (!ctors-offset offset elf))
                  (elf (!ctors-size size elf))
                  (elf (!ctors-bytes bytes elf)))
                 elf))

            (#.*dtors*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!dtors-addr addr elf))
                  (elf (!dtors-offset offset elf))
                  (elf (!dtors-size size elf))
                  (elf (!dtors-bytes bytes elf)))
                 elf))

            (#.*jcr*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!jcr-addr addr elf))
                  (elf (!jcr-offset offset elf))
                  (elf (!jcr-size size elf))
                  (elf (!jcr-bytes bytes elf)))
                 elf))

            (#.*data_rel_ro*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!data-rel-ro-addr addr elf))
                  (elf (!data-rel-ro-offset offset elf))
                  (elf (!data-rel-ro-size size elf))
                  (elf (!data-rel-ro-bytes bytes elf)))
                 elf))

            (#.*got*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!got-addr addr elf))
                  (elf (!got-offset offset elf))
                  (elf (!got-size size elf))
                  (elf (!got-bytes bytes elf)))
                 elf))

            (#.*got_plt*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!got-plt-addr addr elf))
                  (elf (!got-plt-offset offset elf))
                  (elf (!got-plt-size size elf))
                  (elf (!got-plt-bytes bytes elf)))
                 elf))

            (#.*elf-data*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!data-addr addr elf))
                  (elf (!data-offset offset elf))
                  (elf (!data-size size elf))
                  (elf (!data-bytes bytes elf)))
                 elf))

            (#.*tdata*
             (b* ((bytes (take size (nthcdr offset file-bytes)))
                  (elf (!tdata-addr addr elf))
                  (elf (!tdata-offset offset elf))
                  (elf (!tdata-size size elf))
                  (elf (!tdata-bytes bytes elf)))
                 elf))

            (#.*tbss*
             (b* ((bytes (make-list size :initial-element 0))
                  (elf (!tbss-addr addr elf))
                  (elf (!tbss-offset offset elf))
                  (elf (!tbss-size size elf))
                  (elf (!tbss-bytes bytes elf)))
                 elf))

            (#.*bss*
             (b* ((bytes (make-list size :initial-element 0))
                  (elf (!bss-addr addr elf))
                  (elf (!bss-offset offset elf))
                  (elf (!bss-size size elf))
                  (elf (!bss-bytes bytes elf)))
                 elf))

            (t elf))))
        (set-stobj-fields (cdr sections) file-bytes elf))))

;; -------------------------------------------------------------------
;; Function to read an ELF binary and initialize the stobj with the bytes
;; -------------------------------------------------------------------

(defun elf-file-read (file-byte-list elf state)
  (declare (xargs :stobjs (elf state)
                  :guard (byte-listp file-byte-list)
                  :verify-guards nil))
  (b* ((elf-file-size (len file-byte-list))
       (elf (!elf-file-size elf-file-size elf))
       ;; Assuming 64-bit architecture --- ELF header size is 64
       ;; bytes.
       (elf-header-size 64)
       (elf (!elf-header-size elf-header-size elf))
       ;; The following checks are also done in the top-level function
       ;; binary-file-read (in tools/execution/top.lisp).  They're
       ;; done here again in case someone wants to use this function
       ;; at the top level.
       (file-header (take elf-header-size file-byte-list))
       (header (read-elf-header file-header))
       (magic (combine-bytes (cdr (assoc 'magic header))))
       (class (cdr (assoc 'class header)))
       ((when (or (not (equal magic #.*ELFMAG*))
                  (not (equal class 2))))
        (mv
         (cw "Error: Not a 64-bit ELF object file (as suggested by the ELF header). ~%")
         elf state))

       ;; Retrieve the data for the segment headers
       (segment-header-offset (nfix (cdr (assoc 'phoff header))))
       (segment-headers (nthcdr segment-header-offset file-byte-list))
       (nsegments (nfix (cdr (assoc 'phnum header))))
       (segments (read-segment-headers nsegments segment-headers nil))

       ;; Retrieve the data for the section header
       (section-header-offset (nfix (cdr (assoc 'shoff header))))
       (section-headers (nthcdr section-header-offset file-byte-list))
       (nsections (nfix (cdr (assoc 'shnum header))))
       (elf (!sections-num nsections elf))
       (sections (read-section-headers nsections section-headers nil))
       (string-section-index (nfix (cdr (assoc 'shstrndx header))))
       ((when (not (or (equal nsections string-section-index)
                       (> nsections string-section-index))))
        (mv
         (cw "ELF Binary: Mismatch between number of sections and string-section-index. Strings could not be read. ~%")
         elf state))
       (string-section-header (car (nthcdr string-section-index sections)))
       (string-section-data (take (nfix (cdr (assoc 'size
                                                    string-section-header)))
                                  (nthcdr (nfix (cdr
                                                 (assoc 'offset
                                                        string-section-header)))
                                          file-byte-list)))
       (new-sections (read-section-names sections string-section-data nil))

       ;; Fill all section bytes
       (elf (set-stobj-fields new-sections file-byte-list elf)))
      (mv (acons 'HEADER header
                 (acons 'SECTIONS (list new-sections) nil))
          elf state)))

;;======================================================================

;;----------------------------------------------------------------------
;; Functions to load the x86 stobj based on the information in the
;; elf stobj:
;; ----------------------------------------------------------------------

;; (elf-file-read <file-byte-list> elf state)

;; (load-qwords-into-physical-memory-list *1-gig-page-tables* x86)

(defun elf-load-text-section (elf x86)
  (declare (xargs :stobjs (elf x86)))
  (b* ((text-section-addr (text-addr elf))
       (text-section-bytes (text-bytes elf))
       (- (if (equal text-section-bytes nil)
              (cw "~%Text section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p text-section-addr))
                  (not (canonical-address-p (+ text-section-addr
                                               (len text-section-bytes))))))
        (mv (cons 'text-section-addr text-section-addr) x86)))
      (write-bytes-to-memory text-section-addr text-section-bytes x86)))

(defun elf-load-data-section (elf x86)
  (declare (xargs :stobjs (elf x86)))
  (b* ((data-section-addr (data-addr elf))
       (data-section-bytes (data-bytes elf))
       (- (if (equal data-section-bytes nil)
              (cw "~%Data section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p data-section-addr))
                  (not (canonical-address-p (+ (len
                                                data-section-bytes)
                                               data-section-addr)))))
        (mv (cons 'data-section-addr data-section-addr) x86)))
      (write-bytes-to-memory data-section-addr data-section-bytes x86)))

(defun elf-load-bss-section (elf x86)
  (declare (xargs :stobjs (elf x86)))
  (b* ((bss-section-addr (bss-addr elf))
       (bss-section-bytes (bss-bytes elf))
       (- (if (equal bss-section-bytes nil)
              (cw "~%Bss section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p bss-section-addr))
                  (not (canonical-address-p (+ (len
                                                bss-section-bytes)
                                               bss-section-addr)))))
        (mv (cons 'bss-section-addr bss-section-addr) x86)))
      (write-bytes-to-memory bss-section-addr bss-section-bytes x86)))

(defun elf-load-rodata-section (elf x86)
  (declare (xargs :stobjs (elf x86)))
  (b* ((rodata-section-addr (rodata-addr elf))
       (rodata-section-bytes (rodata-bytes elf))
       (- (if (equal rodata-section-bytes nil)
              (cw "~%Rodata section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p rodata-section-addr))
                  (not (canonical-address-p (+ (len
                                                rodata-section-bytes)
                                               rodata-section-addr)))))
        (mv (cons 'rodata-section-addr rodata-section-addr) x86)))
      (write-bytes-to-memory rodata-section-addr rodata-section-bytes x86)))

;; ======================================================================
