; EXLD Library

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

(in-package "EXLD")
(include-book "base")
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
                nil
              (cons val
                    (elf-read-mem-null-term byte-list (1+ offset)))))
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

;; ----------------------------------------------------------------------

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

;; ----------------------------------------------------------------------

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

(define read-section-names ((sec-headers elf-section-headers-p)
                            (string-section-data byte-listp)
                            (acc elf-section-headers-p))
  :short "Get the names of the section headers from the string section
 table, located at the offset indicated by the @('sh_offset') value of
 the @('shstrndx')th section"
  :returns (new-sec-headers elf-section-headers-p
                            :hyp (elf-section-headers-p acc))
  (if (atom sec-headers)
      acc
    (b* ((section-header (car sec-headers))
         ((elf-section-header section-header))
         (name-str-offset section-header.name)
         ((unless (<= name-str-offset (len string-section-data)))
          (prog2$
           (raise "String-section-data's length should be at least ~x0, but it is ~x1 instead!"
                  name-str-offset (len string-section-data))
           acc))
         (name-str (elf-read-string-null-term string-section-data name-str-offset))
         (new-section-header (change-elf-section-header section-header :name-str name-str)))
      (read-section-names (cdr sec-headers)
                          string-section-data
                          (cons new-section-header acc)))))

(local
 (defthm byte-listp-of-make-list-ac-0
   (implies (natp n)
            (byte-listp (make-list-ac n 0 nil)))))

(define get-string-section-data ((string-section-index natp)
                                 (sec-headers elf-section-headers-p)
                                 (file-byte-list byte-listp))
  :returns (bl byte-listp :hyp (byte-listp file-byte-list))
  (b* ((sec-headers-from-string-section-index (nthcdr string-section-index sec-headers))
       ((unless (and (consp sec-headers-from-string-section-index)
                     (elf-section-headers-p sec-headers-from-string-section-index)))
        (prog2$
         (er hard? 'elf-file-read "String-section-index header not found!~%")
         nil))
       (header (car sec-headers-from-string-section-index))
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

;; /* the ELF magic number */
(defconst *ELFMAG*             (merge-bytes (append '(127) (string->bytes "ELF"))))

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

(define set-elf-stobj-fields ((sec-headers elf-section-headers-p)
                              (file-bytes byte-listp)
                              elf)
  :short "Populate ELF stobj with bytes corresponding to each section"
  :returns (new-elf good-elf-p :hyp (good-elf-p elf))
  :prepwork ((local (in-theory (e/d ()
                                    (acl2::make-list-ac-removal
                                     make-list-ac
                                     nth not length unsigned-byte-p)))))
  (if (atom sec-headers)
      elf
    (b* ((sec-header (car sec-headers))
         ((elf-section-header sec-header))
         (bytes (take sec-header.size (nthcdr sec-header.offset file-bytes)))
         (elf
          (if (byte-listp bytes)
              (b* ((section (make-section-info :header sec-header
                                               :bytes bytes)))
                (!sections (cons section (@sections elf)) elf))

            (prog2$
             (cw "~% Insufficient number of bytes in the file to grab section ~s0!~% ~
  This could be a problem later, but we're moving on anyway..."
                 sec-header.name-str)
             elf))))
      (set-elf-stobj-fields (cdr sec-headers) file-bytes elf))))

;; ----------------------------------------------------------------------

(define populate-elf-contents ((contents byte-listp)
                               elf state)
  :short "Initialize the ELF stobj with @('contents') parsed as an ELF binary"
  :returns
  (mv (new-elf good-elf-p :hyp (good-elf-p elf))
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
                (mv elf state)))
       (elf (!elf-header header elf))
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
         (mv elf state)))
       (nsegments header.phnum)
       ;; TODO: What do we do with these segments?
       (?segments (if (equal class 1)
                      (read-segment-headers-32 nsegments segment-headers nil)
                    (read-segment-headers-64 nsegments segment-headers nil)))

       ;; Retrieve the data for the section header
       (section-headers (get-named-section-headers header file-byte-list))
       (elf (!sections-num header.shnum elf))
       (elf (set-elf-stobj-fields section-headers file-byte-list elf)))
    (mv elf state)))

(define populate-elf ((filename stringp)
                      elf
                      state)
  :short "Initialize the ELF stobj with @('contents') of ELF binary @('filename')"
  :returns (mv (new-elf good-elf-p :hyp (good-elf-p elf))
               state)
  (b* (((mv contents state)
        (acl2::read-file-bytes filename state))
       ((unless (byte-listp contents))
        (prog2$
         (raise "Error reading file ~s0!" filename)
         (mv elf state))))
    (populate-elf-contents contents elf state)))

;; ----------------------------------------------------------------------

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

(define get-symtab-entries (elf)
  :short "Get all symbol table entries, with names mapped to entries in the string table"
  :returns (elf-entries)
  (b* ((elf-header (@elf-header elf))
       (sections (@sections elf))
       ((section-info symtab-section) (get-section-info ".symtab" sections))
       ((section-info strtab-section) (get-section-info ".strtab" sections))
       ((elf-section-header symtab-header) symtab-section.header)
       (elf64?
        ;; ELF32 when class=1
        ;; ELF64 when class=2
        (equal (elf-header->class elf-header) 2))
       (symtab-entries
        (parse-symtab-entries elf64? symtab-header.entsize symtab-section.bytes strtab-section.bytes)))
    symtab-entries)
  ///

  (defret elf32_sym-info-list-p-of-<fn>
    (implies (not (equal (elf-header->class (@elf-header elf)) 2))
             (elf32_sym-info-list-p elf-entries)))

  (defret elf64_sym-info-list-p-of-<fn>
    (implies (equal (elf-header->class (@elf-header elf)) 2)
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
                           elf)
  :short "Return the address of @('label'), if present, by searching in the sym/str table information"
  :returns (addr acl2::maybe-natp :hyp :guard)
  (b* ((entries (get-symtab-entries elf))
       (elf64 (equal (elf-header->class (@elf-header elf)) 2))
       (addr (find-label-address-from-elf-symtab-info elf64 label entries)))
    addr))

(define get-label-addresses ((labels string-listp)
                             elf)
  :short "Return the addresses of each valid label in @('labels') by searching in the sym/str table information"
  :returns (addrs true-listp :hyp :guard)
  (if (atom labels)
      nil
    (cons (get-label-address (car labels) elf)
          (get-label-addresses (cdr labels) elf))))

;; ----------------------------------------------------------------------
