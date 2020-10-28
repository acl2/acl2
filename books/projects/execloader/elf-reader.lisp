; EL Library

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
; Soumava Ghosh       <soumava@cs.utexas.edu>

; [Shilpi Goel] This book used to live in
; [books]/projects/x86isa/tools/execution/exec-loaders, but now it's
; in a stand-alone library of its own.

;; ----------------------------------------------------------------------

(in-package "EL")

(include-book "elf-stobj")
(include-book "elf-structs")
(include-book "std/io/read-file-bytes" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;; ----------------------------------------------------------------------

(defxdoc elf-reader
  :parents (execloader)
  :short "Read in parts of ELF format files into fields of the @('elf') stobj"
  )

(local (xdoc::set-default-parents elf-reader))

;; -------------------------------------------------------------------

(define elf-read-mem-null-term ((byte-list byte-listp)
                                (offset natp))
  :short "Read a location at an @('offset') of a given @('byte-list')
  and return the list of bytes until a null is encountered (null not included)"
  :measure (nfix (- (len byte-list) offset))
  :guard (<= offset (len byte-list))
  :returns (bl byte-listp :hyp (and (natp offset) (byte-listp byte-list)))
  (if (natp offset)
      (if (< offset (len byte-list))
          (let* ((val (car (nthcdr offset byte-list))))
            (if (equal 0 val)
                ;; (cons 0 nil)
                nil
              (cons val
                    (elf-read-mem-null-term byte-list (1+ offset)))))
        ;; (cons 0 nil)
        nil)
    nil))

(define elf-read-string-null-term ((byte-list byte-listp)
                                   (offset natp))
  :short "Read a null terminated string from a given @('offset') of @('byte-list')"
  :guard (<= offset (len byte-list))
  :returns (str stringp :rule-classes :type-prescription)
  (let* ((bytes (elf-read-mem-null-term byte-list offset))
         (charlist (bytes->charlist bytes)))
    (coerce charlist 'string)))

(define read-segment-headers-64 ((nsegments natp)
                                 (rest-of-the-file byte-listp)
                                 (acc elf64-segment-headers-p))
  :short "Read 64-bit ELF segment headers"
  :returns (64-bit-segments elf64-segment-headers-p :hyp (elf64-segment-headers-p acc))
  (if (zp nsegments)
      (reverse acc)

    (b* (((mv p_type   rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_flags  rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_offset rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
         ((mv p_vaddr  rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
         ((mv p_paddr  rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
         ((mv p_filesz rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
         ((mv p_memsz  rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
         ((mv p_align  rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
         (segment
          (make-elf64-segment-header
           :type   p_type
           :flags  p_flags
           :offset p_offset
           :vaddr  p_vaddr
           :paddr  p_paddr
           :filesz p_filesz
           :memsz  p_memsz
           :align  p_align)))
      (read-segment-headers-64 (1- nsegments) rest-of-the-file
                               (cons segment acc)))))

(define read-segment-headers-32 ((nsegments natp)
                                 (rest-of-the-file byte-listp)
                                 (acc elf32-segment-headers-p))
  :short "Read 64-bit ELF segment headers"
  :returns (32-bit-segments elf32-segment-headers-p :hyp (elf32-segment-headers-p acc))
  (if (zp nsegments)
      (reverse acc)

    (b* (((mv p_type   rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_offset rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_vaddr  rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_paddr  rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_filesz rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_memsz  rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_flags  rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv p_align  rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         (segment
          (make-elf32-segment-header
           :type   p_type
           :flags  p_flags
           :offset p_offset
           :vaddr  p_vaddr
           :paddr  p_paddr
           :filesz p_filesz
           :memsz  p_memsz
           :align  p_align)))
      (read-segment-headers-32 (1- nsegments) rest-of-the-file
                               (cons segment acc)))))

(define read-section-headers ((nsections natp)
                              (w natp)
                              (rest-of-the-file byte-listp)
                              (acc elf-section-headers-p))
  :short "Read ELF section headers"
  :prepwork
  ((local (in-theory (e/d () (unsigned-byte-p)))))
  :returns (section-headers elf-section-headers-p :hyp (elf-section-headers-p acc))
  (if (zp nsections)
      (reverse acc)

    (b* (((unless (or (equal w 4) (equal w 8)))
          (prog2$
           (raise "Width of fields expected to be either 4 or 8, but it is ~x0 instead!" w)
           (reverse acc)))
         ((mv sh_name      rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv sh_type      rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv sh_flags     rest-of-the-file) (merge-first-split-bytes w rest-of-the-file))
         ((mv sh_addr      rest-of-the-file) (merge-first-split-bytes w rest-of-the-file))
         ((mv sh_offset    rest-of-the-file) (merge-first-split-bytes w rest-of-the-file))
         ((mv sh_size      rest-of-the-file) (merge-first-split-bytes w rest-of-the-file))
         ((mv sh_link      rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv sh_info      rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv sh_addralign rest-of-the-file) (merge-first-split-bytes w rest-of-the-file))
         ((mv sh_entsize   rest-of-the-file) (merge-first-split-bytes w rest-of-the-file))
         (section
          (make-elf-section-header
           ;; name-str to be filled in later --- see
           ;; read-section-names.
           :name      sh_name
           :type      sh_type
           :flags     sh_flags
           :addr      sh_addr
           :offset    sh_offset
           :size      sh_size
           :link      sh_link
           :info      sh_info
           :addralign sh_addralign
           :entsize   sh_entsize)))
      (read-section-headers (1- nsections) w rest-of-the-file
                            (cons section acc)))))

(define read-elf-header ((file-header byte-listp))
  :short "Read the ELF header from the first 64 bytes"
  :returns (header elf-header-p)
  (b* (((mv e_magic     file-header) (split-bytes 4 file-header))
       ((mv e_class     file-header) (merge-first-split-bytes 1 file-header))
       (w (if (equal e_class 1) 4 8))
       ((mv e_dataenc   file-header) (merge-first-split-bytes 1 file-header))
       ((mv e_identver  file-header) (merge-first-split-bytes 1 file-header))
       ((mv e_osabi     file-header) (merge-first-split-bytes 1 file-header))
       ((mv e_abiver    file-header) (merge-first-split-bytes 1 file-header))
       ((mv e_padding   file-header) (split-bytes 7 file-header))
       ((mv e_type      file-header) (merge-first-split-bytes 2 file-header))
       ((mv e_machine   file-header) (merge-first-split-bytes 2 file-header))
       ((mv e_version   file-header) (merge-first-split-bytes 4 file-header))
       ((mv e_entry     file-header) (merge-first-split-bytes w file-header))
       ((mv e_phoff     file-header) (merge-first-split-bytes w file-header))
       ((mv e_shoff     file-header) (merge-first-split-bytes w file-header))
       ((mv e_flags     file-header) (merge-first-split-bytes 4 file-header))
       ((mv e_ehsize    file-header) (merge-first-split-bytes 2 file-header))
       ((mv e_phentsize file-header) (merge-first-split-bytes 2 file-header))
       ((mv e_phnum     file-header) (merge-first-split-bytes 2 file-header))
       ((mv e_shentsize file-header) (merge-first-split-bytes 2 file-header))
       ((mv e_shnum     file-header) (merge-first-split-bytes 2 file-header))
       ((mv e_shstrndx  &)           (merge-first-split-bytes 2 file-header)))
    (make-elf-header
     :magic     e_magic
     :class     e_class
     :dataenc   e_dataenc
     :identver  e_identver
     :osabi     e_osabi
     :abiver    e_abiver
     :padding   e_padding
     :type      e_type
     :machine   e_machine
     :version   e_version
     :entry     e_entry
     :phoff     e_phoff
     :shoff     e_shoff
     :flags     e_flags
     :ehsize    e_ehsize
     :phentsize e_phentsize
     :phnum     e_phnum
     :shentsize e_shentsize
     :shnum     e_shnum
     :shstrndx  e_shstrndx)))

(define read-section-names ((sections elf-section-headers-p)
                            (string-section-data byte-listp)
                            (acc elf-section-headers-p))
  :short "Get the names of the section headers from the string section
 table, located at the offset indicated by the @('sh_offset') value of
 the @('shstrndx')th section"
  :returns (new-sections elf-section-headers-p
                         :hyp (elf-section-headers-p acc))
  (if (atom sections)
      acc
    (b* ((section-header (car sections))
         ((elf-section-header section-header))
         (name-str-offset section-header.name)
         ((unless (<= name-str-offset (len string-section-data)))
          (prog2$
           (raise "String-section-data's length should be at least ~x0, but it is ~x1 instead!"
                  name-str-offset (len string-section-data))
           acc))
         (name-str (elf-read-string-null-term string-section-data name-str-offset))
         (new-section-header (change-elf-section-header section-header :name-str name-str)))
      (read-section-names (cdr sections)
                          string-section-data
                          (cons new-section-header acc)))))

(local
 (defthm byte-listp-of-make-list-ac-0
   (implies (natp n)
            (byte-listp (make-list-ac n 0 nil)))))

(define get-string-section-data ((string-section-index natp)
                                 (sections elf-section-headers-p)
                                 (file-byte-list byte-listp))
  :returns (bl byte-listp :hyp (byte-listp file-byte-list))
  (b* ((sections-from-string-section-index (nthcdr string-section-index sections))
       ((unless (and (consp sections-from-string-section-index)
                     (elf-section-headers-p sections-from-string-section-index)))
        (prog2$
         (er hard? 'elf-file-read "String-section-index header not found!~%")
         nil))
       (header (car sections-from-string-section-index))
       ((elf-section-header header))
       (string-section-header-bytes (take header.size (nthcdr header.offset file-byte-list)))
       ((unless (byte-listp string-section-header-bytes))
        (prog2$
         (er hard? 'elf-file-read "Not enough bytes to read string-section-header data!")
         nil)))
    string-section-header-bytes))

(define get-named-section-headers ((elf-header elf-header-p)
                                   (file-byte-list byte-listp))
  :returns (new-sections elf-section-headers-p)
  (b* (((elf-header elf-header))
       (section-header-offset elf-header.shoff)
       (section-header-bytes (nthcdr section-header-offset file-byte-list))
       ((unless (byte-listp section-header-bytes))
        (prog2$
         (raise "Not enough bytes to read ELF section headers!")
         nil))
       (nsections elf-header.shnum)
       (w (if (equal elf-header.class 1) 4 8))
       (string-section-index elf-header.shstrndx)
       ((when (not (or (equal nsections string-section-index)
                       (> nsections string-section-index))))
        (prog2$
         (raise "ELF Binary: Mismatch between number of sections and string-section-index. ~
 Strings could not be read. ~%")
         nil))
       (headers (read-section-headers nsections w section-header-bytes nil))
       (string-section-data (get-string-section-data string-section-index headers file-byte-list))
       (updated-headers (read-section-names headers string-section-data nil)))
    updated-headers))

(define is-elf-content-p ((contents byte-listp)
                          state)
  :short "Check if @('contents') represent a valid ELF binary (in bytes,
  LSB-first); if so, return the ELF header"
  :returns (mv (is-elf-file booleanp :rule-classes :type-prescription)
               (header elf-header-p)
               state)
  (b* (((unless (<= 64 (len contents)))
        (prog2$
         (raise "Error reading ELF contents!")
         (mv nil (make-elf-header) state)))
       (bytes contents)
       (file-header (take 64 bytes))
       ((elf-header header) (read-elf-header file-header))
       (magic (merge-bytes header.magic))
       (class header.class)
       ;; ELF32 when class=1
       ;; ELF64 when class=2
       ((when (or (not (equal magic *ELFMAG*))
                  (not (member class '(1 2)))))
        (prog2$
         (raise "Error:  Invalid ELF header! ~% Header: ~x0 ~%" header)
         (mv nil (make-elf-header) state))))
    (mv t header state)))

(define set-elf-stobj-fields ((sections elf-section-headers-p)
                              (file-bytes byte-listp)
                              elf)
  :short "Populate ELF stobj with bytes corresponding to each section"
  :returns (new-elf good-elf-p :hyp (good-elf-p elf))
  :prepwork ((local (in-theory (e/d ()
                                    (acl2::make-list-ac-removal
                                     make-list-ac
                                     nth not length unsigned-byte-p)))))
  (if (atom sections)
      elf
    (b* ((section (car sections))
         ((elf-section-header section))
         (section-name section.name-str)
         (name-bytes (merge-bytes (string->bytes section-name)))
         (addr section.addr)
         (offset section.offset)
         (size section.size)
         (bytes (take size (nthcdr offset file-bytes)))
         ((unless (byte-listp bytes))
          (prog2$
           (raise "Insufficient number of bytes!")
           elf))
         (elf
          (cond
           ((equal name-bytes *note_abi_tag*)
            (b* ((elf (!note-ABI-tag-addr addr elf))
                 (elf (!note-ABI-tag-offset offset elf))
                 (elf (!note-ABI-tag-size size elf))
                 (elf (!note-ABI-tag-bytes bytes elf)))
              elf))

           ((equal name-bytes *note_gnu_build_id*)
            (b* ((elf (!note-gnu-buildid-addr addr elf))
                 (elf (!note-gnu-buildid-offset offset elf))
                 (elf (!note-gnu-buildid-size size elf))
                 (elf (!note-gnu-buildid-bytes bytes elf)))
              elf))

           ((equal name-bytes *rela_plt*)
            (b* ((elf (!rela-plt-addr addr elf))
                 (elf (!rela-plt-offset offset elf))
                 (elf (!rela-plt-size size elf))
                 (elf (!rela-plt-bytes bytes elf)))
              elf))

           ((equal name-bytes *init*)
            (b* ((elf (!init-addr addr elf))
                 (elf (!init-offset offset elf))
                 (elf (!init-size size elf))
                 (elf (!init-bytes bytes elf)))
              elf))

           ((equal name-bytes *plt*)
            (b* ((elf (!plt-addr addr elf))
                 (elf (!plt-offset offset elf))
                 (elf (!plt-size size elf))
                 (elf (!plt-bytes bytes elf)))
              elf))

           ((equal name-bytes *elf-text*)
            (b* ((elf (!text-addr addr elf))
                 (elf (!text-offset offset elf))
                 (elf (!text-size size elf))
                 (elf (!text-bytes bytes elf)))
              elf))

           ((or (equal name-bytes *elf-text-init*)
                (equal name-bytes *elf-init-text*))
            (b* (((when (@text-init-bytes elf))
                  (prog2$
                   (raise "Non-empty text-init-bytes section!")
                   elf))
                 (elf (!text-init-addr addr elf))
                 (elf (!text-init-offset offset elf))
                 (elf (!text-init-size size elf))
                 (elf (!text-init-bytes bytes elf)))
              elf))

           ((equal name-bytes *fini*)
            (b* ((elf (!fini-addr addr elf))
                 (elf (!fini-offset offset elf))
                 (elf (!fini-size size elf))
                 (elf (!fini-bytes bytes elf)))
              elf))

           ((equal name-bytes *rodata*)
            (b* ((elf (!rodata-addr addr elf))
                 (elf (!rodata-offset offset elf))
                 (elf (!rodata-size size elf))
                 (elf (!rodata-bytes bytes elf)))
              elf))

           ((equal name-bytes *eh_frame*)
            (b* ((elf (!eh-frame-addr addr elf))
                 (elf (!eh-frame-offset offset elf))
                 (elf (!eh-frame-size size elf))
                 (elf (!eh-frame-bytes bytes elf)))
              elf))

           ((equal name-bytes *gcc_except_table*)
            (b* ((elf (!gcc-except-table-addr addr elf))
                 (elf (!gcc-except-table-offset offset elf))
                 (elf (!gcc-except-table-size size elf))
                 (elf (!gcc-except-table-bytes bytes elf)))
              elf))

           ((equal name-bytes *init_array*)
            (b* ((elf (!init-array-addr addr elf))
                 (elf (!init-array-offset offset elf))
                 (elf (!init-array-size size elf))
                 (elf (!init-array-bytes bytes elf)))
              elf))

           ((equal name-bytes *fini_array*)
            (b* ((elf (!fini-array-addr addr elf))
                 (elf (!fini-array-offset offset elf))
                 (elf (!fini-array-size size elf))
                 (elf (!fini-array-bytes bytes elf)))
              elf))

           ((equal name-bytes *ctors*)
            (b* ((elf (!ctors-addr addr elf))
                 (elf (!ctors-offset offset elf))
                 (elf (!ctors-size size elf))
                 (elf (!ctors-bytes bytes elf)))
              elf))

           ((equal name-bytes *dtors*)
            (b* ((elf (!dtors-addr addr elf))
                 (elf (!dtors-offset offset elf))
                 (elf (!dtors-size size elf))
                 (elf (!dtors-bytes bytes elf)))
              elf))

           ((equal name-bytes *jcr*)
            (b* ((elf (!jcr-addr addr elf))
                 (elf (!jcr-offset offset elf))
                 (elf (!jcr-size size elf))
                 (elf (!jcr-bytes bytes elf)))
              elf))

           ((equal name-bytes *data_rel_ro*)
            (b* ((elf (!data-rel-ro-addr addr elf))
                 (elf (!data-rel-ro-offset offset elf))
                 (elf (!data-rel-ro-size size elf))
                 (elf (!data-rel-ro-bytes bytes elf)))
              elf))

           ((equal name-bytes *got*)
            (b* ((elf (!got-addr addr elf))
                 (elf (!got-offset offset elf))
                 (elf (!got-size size elf))
                 (elf (!got-bytes bytes elf)))
              elf))

           ((equal name-bytes *got_plt*)
            (b* ((elf (!got-plt-addr addr elf))
                 (elf (!got-plt-offset offset elf))
                 (elf (!got-plt-size size elf))
                 (elf (!got-plt-bytes bytes elf)))
              elf))

           ((equal name-bytes *elf-data*)
            (b* ((elf (!data-addr addr elf))
                 (elf (!data-offset offset elf))
                 (elf (!data-size size elf))
                 (elf (!data-bytes bytes elf)))
              elf))

           ((equal name-bytes *tdata*)
            (b* ((elf (!tdata-addr addr elf))
                 (elf (!tdata-offset offset elf))
                 (elf (!tdata-size size elf))
                 (elf (!tdata-bytes bytes elf)))
              elf))

           ((equal name-bytes *symtab*)
            (b* ((elf (!symtab-addr addr elf))
                 (elf (!symtab-offset offset elf))
                 (elf (!symtab-size size elf))
                 (elf (!symtab-bytes bytes elf)))
              elf))

           ((equal name-bytes *strtab*)
            (b* ((elf (!strtab-addr addr elf))
                 (elf (!strtab-offset offset elf))
                 (elf (!strtab-size size elf))
                 (elf (!strtab-bytes bytes elf)))
              elf))

           ;; ((equal name-bytes *tbss*)
           ;;  (b* ((bytes (make-list size :initial-element 0))
           ;;       (elf (!tbss-addr addr elf))
           ;;       (elf (!tbss-offset offset elf))
           ;;       (elf (!tbss-size size elf))
           ;;       (elf (!tbss-bytes bytes elf)))
           ;;    elf))

           ;; ((equal name-bytes *bss*)
           ;;  (b* ((bytes (make-list size :initial-element 0))
           ;;       (elf (!bss-addr addr elf))
           ;;       (elf (!bss-offset offset elf))
           ;;       (elf (!bss-size size elf))
           ;;       (elf (!bss-bytes bytes elf)))
           ;;    elf))

           (t (prog2$
               (cw "~% Unimplemented section! ~s0 ~%" section-name)
               elf)))))

      (set-elf-stobj-fields (cdr sections) file-bytes elf))))

(define populate-elf-contents ((contents byte-listp)
                               elf state)
  :short "Initialize the ELF stobj with @('contents') parsed as an ELF binary"
  :returns
  (mv (elf-header elf-header-p)
      (elf-section-headers elf-section-headers-p)
      (new-elf good-elf-p :hyp (good-elf-p elf))
      state)
  :guard-hints (("Goal" :in-theory (e/d ()
                                        (acl2::make-list-ac-removal
                                         make-list-ac
                                         nth len unsigned-byte-p
                                         good-elf-p state-p))))  
  (b* (((mv okp header state)
        (is-elf-content-p contents state))
       ((unless okp)
        (prog2$ (raise "Bad ELF contents!")
                (mv (make-elf-header) nil elf state)))
       (file-byte-list contents)
       (elf-file-size (len file-byte-list))
       (elf (!elf-file-size elf-file-size elf))
       ((elf-header header))
       (class header.class)
       ;; ELF32 when class=1
       ;; ELF64 when class=2
       (elf-header-size (if (equal class 1) 52 64))
       (elf (!elf-header-size elf-header-size elf))

       ;; Retrieve the data for the segment headers
       (segment-header-offset header.phoff)
       (segment-headers (nthcdr segment-header-offset file-byte-list))
       ((unless (byte-listp segment-headers))
        (prog2$
         (er hard? 'elf-file-read "Not enough bytes to read ELF segment headers!")
         (mv (make-elf-header) nil elf state)))
       (nsegments header.phnum)
       ;; TODO: What do we do with these segments?
       (?segments (if (equal class 1)
                      (read-segment-headers-32 nsegments segment-headers nil)
                    (read-segment-headers-64 nsegments segment-headers nil)))

       ;; Retrieve the data for the section header
       (section-headers (get-named-section-headers header file-byte-list))
       (elf (!sections-num header.shnum elf))
       (elf (set-elf-stobj-fields section-headers file-byte-list elf)))
    (mv header section-headers elf state)))

(define populate-elf ((filename stringp)
                      elf
                      state)
  :short "Initialize the ELF stobj with @('contents') of ELF binary @('filename')"  
  :returns (mv (elf-header elf-header-p)
               (elf-section-headers elf-section-headers-p)
               (new-elf good-elf-p :hyp (good-elf-p elf))
               state)
  (b* (((mv contents state)
        (acl2::read-file-bytes filename state))
       ((unless (byte-listp contents))
        (prog2$
         (raise "Error reading file ~s0!" filename)
         (mv (make-elf-header) nil elf state))))
    (populate-elf-contents contents elf state)))

;; ----------------------------------------------------------------------

(define get-section-header
  ((name stringp "Name of a section header; e.g., \".symtab\"")
   (section-headers elf-section-headers-p))
  :short "Get the section header from @('section-headers') that corresponds to section @('name'), if it
  exists"
  :returns (header elf-section-header-p :hyp (elf-section-headers-p section-headers))
  (b* (((when (atom section-headers))
        (prog2$
         (raise "Section ~s0 data not present!" name)
         (make-elf-section-header)))
       (header (car section-headers))
       ((elf-section-header header))
       ((unless (equal header.name-str name))
        (get-section-header name (cdr section-headers))))
    header))

(define parse-symtab-entries ((elf64 booleanp)
                              (entrysize natp)
                              (symbytes byte-listp)
                              (strbytes byte-listp))
  :measure (len symbytes)
  :returns (elf-entries)
  (b* (((unless (and (< 0 (len symbytes)) (< 0 (nfix entrysize))))
        nil)
       ((mv entry rest-symbytes) (merge-first-split-bytes entrysize symbytes))
       ((unless (if elf64 (elf64_sym-p entry) (elf32_sym-p entry)))
        (prog2$
         (raise "Inconsistency with entrysize and symbytes?")
         nil))
       (entry-name (if elf64 (elf64_sym->name entry) (elf32_sym->name entry)))
       ;; (- (cw "~% ~x0 ~%" (if elf64 (elf64_sym-debug entry) (elf32_sym-debug entry))))
       ;; entry-name is the offset in strbytes where the symbol name is stored.
       (name-str (bytes->string (take-till-zero (nthcdr entry-name strbytes)))))
    (cons (if elf64
              (make-elf64_sym-info
               :name-str name-str
               :entry entry)
            (make-elf32_sym-info
             :name-str name-str
             :entry entry))
          (parse-symtab-entries elf64 entrysize rest-symbytes strbytes)))
  ///

  (defret elf64_sym-info-list-p-of-<fn>
    (implies elf64
             (elf64_sym-info-list-p elf-entries)))

  (defret elf32_sym-info-list-p-of-<fn>
    (implies (not elf64)
             (elf32_sym-info-list-p elf-entries))))

(define get-symtab-entries ((elf-header elf-header-p)
                            (section-headers elf-section-headers-p)
                            elf)
  :short "Get all symbol table entries, with names mapped to entries in the string table"
  :returns (elf-entries)
  (b* ((symtab-header (get-section-header ".symtab" section-headers))
       ((elf-section-header symtab-header))
       (symtab-bytes (@symtab-bytes elf))
       (strtab-bytes (@strtab-bytes elf))
       (elf64?
        ;; ELF32 when class=1
        ;; ELF64 when class=2
        (equal (elf-header->class elf-header) 2))
       (symtab-entries
        (parse-symtab-entries elf64? symtab-header.entsize symtab-bytes strtab-bytes)))
    symtab-entries)
  ///

  (defret elf32_sym-info-list-p-of-<fn>
    (implies (not (equal (elf-header->class elf-header) 2))
             (elf32_sym-info-list-p elf-entries)))

  (defret elf64_sym-info-list-p-of-<fn>
    (implies (equal (elf-header->class elf-header) 2)
             (elf64_sym-info-list-p elf-entries))))

(define find-label-address-from-elf-symtab-info ((elf64 booleanp)
                                                 (label stringp)
                                                 info)
  :guard (if elf64 (elf64_sym-info-list-p info) (elf32_sym-info-list-p info))
  :returns (addr acl2::maybe-natp :hyp :guard)               
  (b* (((when (atom info)) nil)
       (i (car info))
       (name (if elf64 (elf64_sym-info->name-str i) (elf32_sym-info->name-str i)))
       ((if (equal name label))
        (if elf64
            (elf64_sym->value (elf64_sym-info->entry i))
          (elf32_sym->value (elf32_sym-info->entry i)))))
    (find-label-address-from-elf-symtab-info elf64 label (cdr info))))

(define get-label-address ((label stringp)
                           (elf-header elf-header-p)
                           (section-headers elf-section-headers-p)
                           elf)
  :short "Return the address of @('label'), if present, by searching in the sym/str table information"
  :returns (addr acl2::maybe-natp :hyp :guard)
  (b* ((entries (get-symtab-entries elf-header section-headers elf))
       (elf64 (equal (elf-header->class elf-header) 2))
       (addr (find-label-address-from-elf-symtab-info elf64 label entries)))
    addr))

(define get-label-addresses ((labels string-listp)
                             (elf-header elf-header-p)
                             (section-headers elf-section-headers-p)
                             elf)
  :short "Return the addresses of each valid label in @('labels') by searching in the sym/str table information"
  :returns (addrs true-listp :hyp :guard)
  (if (atom labels)
      nil
    (cons (get-label-address (car labels) elf-header section-headers elf)
          (get-label-addresses (cdr labels) elf-header section-headers elf))))

;; ----------------------------------------------------------------------
