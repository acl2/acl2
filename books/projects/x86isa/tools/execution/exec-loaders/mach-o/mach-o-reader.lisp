; X86ISA Library

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
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>

;; A very simple Mach-O File Reader and Loader

;; ======================================================================

(in-package "X86ISA")

(include-book "std/io/read-file-bytes" :dir :system)
(include-book "mach-o-stobj"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "std/lists/take" :dir :system))

;; ======================================================================

;; Parse the Mach-O file:

;; ----------------------------------------------------------------------
;; Read the header:
;; ----------------------------------------------------------------------

(defun read-mach_header (file-header)
  (declare (xargs :guard (and (byte-listp file-header)
                              (or (= (len file-header) 28)
                                  (= (len file-header) 32)))))
  (b* (((mv magic       file-header) (rnbni 4 file-header))
       ((mv cputype     file-header) (rnbni 4 file-header))
       ((mv cpusubtype  file-header) (rnbni 4 file-header))
       ((mv filetype    file-header) (rnbni 4 file-header))
       ((mv ncmds       file-header) (rnbni 4 file-header))
       ((mv sizeofcmds  file-header) (rnbni 4 file-header))
       ((mv flags       file-header) (rnbni 4 file-header))
       ((mv reserved   ?file-header)
        (if (or (equal magic #.*MH_MAGIC_64*)
                (equal magic #.*MH_CIGAM_64*))
            (rnbni 4 file-header)
          ;; No reserved field for 32-bit object files.
          (mv nil file-header))))
      (list (cons 'magic      magic)
            (cons 'cputype    cputype)
            (cons 'cpusubtype cpusubtype)
            (cons 'filetype   filetype)
            (cons 'ncmds      ncmds)
            (cons 'sizeofcmds sizeofcmds)
            (cons 'flags      flags)
            (cons 'reserved   reserved))))

(defthm alistp-mv-nth-0-read-mach_header
  (implies (byte-listp file-header)
           (alistp (read-mach_header file-header))))

(in-theory (disable read-mach_header))

;; ----------------------------------------------------------------------
;; Read the section data structures:
;; ----------------------------------------------------------------------

(defun read-section_data_sz_structures
  (nsects sz rest-of-the-file acc mach-o)
  (declare (xargs :stobjs (mach-o)
                  :guard (and (natp nsects)
                              (or (and (equal sz 4)
                                       (<= (* nsects 68) (len rest-of-the-file)))
                                  (and (equal sz 8)
                                       (<= (* nsects 80) (len rest-of-the-file))))
                              (byte-listp rest-of-the-file)
                              (true-listp acc))))

  (if (zp nsects)
      (mv (reverse acc) rest-of-the-file mach-o)

    (b* (((mv sectbytes rest-of-the-file)  (rnbbi  16 rest-of-the-file))
         ((mv segbytes  rest-of-the-file)  (rnbbi  16 rest-of-the-file))
         ((mv addr      rest-of-the-file)  (rnbni  sz rest-of-the-file))
         ((mv size      rest-of-the-file)  (rnbni  sz rest-of-the-file))
         ((mv offset    rest-of-the-file)  (rnbni   4 rest-of-the-file))
         ((mv align     rest-of-the-file)  (rnbni   4 rest-of-the-file))
         ((mv reloff    rest-of-the-file)  (rnbni   4 rest-of-the-file))
         ((mv nreloc    rest-of-the-file)  (rnbni   4 rest-of-the-file))
         ((mv flags     rest-of-the-file)  (rnbni   4 rest-of-the-file))
         ((mv reserved1 rest-of-the-file)  (rnbni   4 rest-of-the-file))
         ((mv reserved2 rest-of-the-file)  (rnbni   4 rest-of-the-file))
         (sectname                         (bytes-to-string sectbytes))
         (segname                          (bytes-to-string segbytes))
         (sect                             (combine-bytes (take-till-zero sectbytes)))
         (seg                              (combine-bytes (take-till-zero segbytes)))
         ((mv reserved3 rest-of-the-file)
          (if (equal sz 8)
              (rnbni 4 rest-of-the-file)
            (mv nil rest-of-the-file)))

         (mach-o
          (case seg
            (#.*MACH-O-TEXT*

             (case sect

               (#.*TEXT-text*
                (b* ((mach-o (!TEXT-text-section-addr addr mach-o))
                     (mach-o (!TEXT-text-section-size size mach-o))
                     (mach-o (!TEXT-text-section-offset offset mach-o)))
                    mach-o))

               (#.*TEXT-cstring*
                (b* ((mach-o (!TEXT-cstring-section-addr addr mach-o))
                     (mach-o (!TEXT-cstring-section-size size mach-o))
                     (mach-o (!TEXT-cstring-section-offset offset mach-o)))
                    mach-o))

               (#.*TEXT-const*
                (b* ((mach-o (!TEXT-const-section-addr addr mach-o))
                     (mach-o (!TEXT-const-section-size size mach-o))
                     (mach-o (!TEXT-const-section-offset offset mach-o)))
                    mach-o))

               (t mach-o)

               ) ;; End of sect
             )   ;; End of TEXT segment

            (#.*MACH-O-DATA*

             (case sect

               (#.*DATA-data*
                (b* ((mach-o (!DATA-data-section-addr addr mach-o))
                     (mach-o (!DATA-data-section-size size mach-o))
                     (mach-o (!DATA-data-section-offset offset mach-o)))
                    mach-o))

               (#.*DATA-dyld*
                (b* ((mach-o (!DATA-dyld-section-addr addr mach-o))
                     (mach-o (!DATA-dyld-section-size size mach-o))
                     (mach-o (!DATA-dyld-section-offset offset mach-o)))
                    mach-o))

               (#.*DATA-const*
                (b* ((mach-o (!DATA-const-section-addr addr mach-o))
                     (mach-o (!DATA-const-section-size size mach-o))
                     (mach-o (!DATA-const-section-offset offset mach-o)))
                    mach-o))

               (#.*DATA-bss*
                (b* ((mach-o (!DATA-bss-section-addr addr mach-o))
                     (mach-o (!DATA-bss-section-size size mach-o))
                     (mach-o (!DATA-bss-section-offset offset mach-o)))
                    mach-o))

               (#.*DATA-common*
                (b* ((mach-o (!DATA-common-section-addr addr mach-o))
                     (mach-o (!DATA-common-section-size size mach-o))
                     (mach-o (!DATA-common-section-offset offset mach-o)))
                    mach-o))

               (t mach-o)

               ) ;; End of sect
             )   ;; End of DATA segment

            (t mach-o))))
        (read-section_data_sz_structures
         (1- nsects) sz
         rest-of-the-file
         (cons (list (cons 'sectname  sectname)
                     (cons 'segname   segname)
                     (cons 'addr      addr)
                     (cons 'size      size)
                     (cons 'offset    offset)
                     (cons 'align     align)
                     (cons 'reloff    reloff)
                     (cons 'nreloc    nreloc)
                     (cons 'flags     flags)
                     (cons 'reserved1 reserved1)
                     (cons 'reserved2 reserved2)
                     (cons 'reserved3 reserved3))
               acc) mach-o))))

(defthm byte-listp-mv-nth-1-read-section_data_sz_structures
  (implies (byte-listp rest-of-the-file)
           (byte-listp (mv-nth 1 (read-section_data_sz_structures
                                  nsects sz rest-of-the-file acc mach-o)))))

(defthm len-mv-nth-1-read-section_data_sz_structures-sz=4
  (implies (and (natp nsects)
                (and (equal sz 4)
                     (<= (* nsects 68) (len (double-rewrite rest-of-the-file))))
                (byte-listp (double-rewrite rest-of-the-file))
                (true-listp acc))
           (<= (- (len (double-rewrite rest-of-the-file)) (* nsects 68))
               (len (mv-nth 1 (read-section_data_sz_structures
                               nsects sz rest-of-the-file acc mach-o)))))
  :rule-classes :linear)

(defthm len-mv-nth-1-read-section_data_sz_structures-sz=8
  (implies (and (natp nsects)
                (and (equal sz 8)
                     (<= (* nsects 80) (len (double-rewrite rest-of-the-file))))
                (byte-listp (double-rewrite rest-of-the-file))
                (true-listp acc))
           (<= (- (len (double-rewrite rest-of-the-file)) (* nsects 80))
               (len (mv-nth 1 (read-section_data_sz_structures
                               nsects sz rest-of-the-file acc mach-o)))))
  :rule-classes :linear)

(defthm mach-op-mv-nth-2-read-section_data_sz_structures-sz=4
  (implies (and (mach-op mach-o)
                (equal sz 4)
                (<= (* nsects 68) (len rest-of-the-file))
                (byte-listp rest-of-the-file))
           (mach-op (mv-nth 2 (read-section_data_sz_structures
                             nsects sz rest-of-the-file acc mach-o)))))

(defthm mach-op-mv-nth-2-read-section_data_sz_structures-sz=8
  (implies (and (mach-op mach-o)
                (equal sz 8)
                (<= (* nsects 80) (len rest-of-the-file))
                (byte-listp rest-of-the-file))
           (mach-op (mv-nth 2 (read-section_data_sz_structures
                             nsects sz rest-of-the-file acc mach-o)))))

(in-theory (disable read-section_data_sz_structures))

;; ----------------------------------------------------------------------
;; Read the load commands (which in turn read the section data
;; structures):
;; ----------------------------------------------------------------------

(defun read-load_commands (ncmds rest-of-the-file acc mach-o)
  (declare (xargs :stobjs (mach-o)
                  :guard (and (natp ncmds)
                              (byte-listp rest-of-the-file)
                              (true-listp acc))))

  (if (zp ncmds)
      (mv (reverse acc) rest-of-the-file mach-o)

    (b* (((mv cmd rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv cmdsize rest-of-the-file) (rnbni 4 rest-of-the-file))
         ((mv cmd_list remaining-file mach-o)
          (case cmd

            (#.*LC_UUID*
             (b* (((mv uuid rest-of-the-file) (rnbni 16 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'uuid uuid))
                     rest-of-the-file mach-o)))

            (#.*LC_SEGMENT*
             (b* (((mv segbytes rest-of-the-file) (rnbbi  16 rest-of-the-file))
                  ((mv vmaddr   rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv vmsize   rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv fileoff  rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv filesize rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv maxprot  rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv initprot rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv nsects   rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv flags    rest-of-the-file) (rnbni  4 rest-of-the-file))
                  (segname                        (bytes-to-string segbytes))
                  ((when (not (<= (* nsects 68) (len rest-of-the-file))))
                   (b* ((- (cw "Error: End of file reached unexpectedly.~%")))
                       (mv (reverse acc) rest-of-the-file mach-o)))
                  ((mv section_ds rest-of-the-file mach-o)
                   (read-section_data_sz_structures
                    nsects 4 rest-of-the-file nil mach-o)))
                 (if (atom section_ds)
                     (mv (list (cons 'cmd cmd)
                               (cons 'cmdsize cmdsize)
                               (cons 'segname segname)
                               (cons 'vmaddr vmaddr)
                               (cons 'vmsize vmsize)
                               (cons 'fileoff fileoff)
                               (cons 'filesize filesize)
                               (cons 'maxprot maxprot)
                               (cons 'initprot initprot)
                               (cons 'nsects nsects)
                               (cons 'flags flags))
                         rest-of-the-file mach-o)
                   (mv (append (list (list (cons 'cmd cmd)
                                           (cons 'cmdsize cmdsize)
                                           (cons 'segname segname)
                                           (cons 'vmaddr vmaddr)
                                           (cons 'vmsize vmsize)
                                           (cons 'fileoff fileoff)
                                           (cons 'filesize filesize)
                                           (cons 'maxprot maxprot)
                                           (cons 'initprot initprot)
                                           (cons 'nsects nsects)
                                           (cons 'flags flags)))
                               section_ds)
                       rest-of-the-file mach-o))))

            (#.*LC_SEGMENT_64*
             (b* (((mv segbytes      rest-of-the-file) (rnbbi  16 rest-of-the-file))
                  ((mv vmaddr        rest-of-the-file) (rnbni  8 rest-of-the-file))
                  ((mv vmsize        rest-of-the-file) (rnbni  8 rest-of-the-file))
                  ((mv fileoff       rest-of-the-file) (rnbni  8 rest-of-the-file))
                  ((mv filesize      rest-of-the-file) (rnbni  8 rest-of-the-file))
                  ((mv maxprot       rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv initprot      rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv nsects        rest-of-the-file) (rnbni  4 rest-of-the-file))
                  ((mv flags         rest-of-the-file) (rnbni  4 rest-of-the-file))
                  (segname                             (bytes-to-string segbytes))
                  ((when (not (<= (* nsects 80) (len rest-of-the-file))))
                   (b* ((- (cw "Error: End of file reached unexpectedly.~%")))
                       (mv (reverse acc) rest-of-the-file mach-o)))
                  ((mv section_64_ds rest-of-the-file mach-o)
                   (read-section_data_sz_structures
                    nsects 8 rest-of-the-file nil mach-o)))
                 (if (atom section_64_ds)
                     (mv (list (cons 'cmd cmd)
                               (cons 'cmdsize cmdsize)
                               (cons 'segname segname)
                               (cons 'vmaddr vmaddr)
                               (cons 'vmsize vmsize)
                               (cons 'fileoff fileoff)
                               (cons 'filesize filesize)
                               (cons 'maxprot maxprot)
                               (cons 'initprot initprot)
                               (cons 'nsects nsects)
                               (cons 'flags flags))
                         rest-of-the-file mach-o)
                   (mv (append (list (list (cons 'cmd cmd)
                                           (cons 'cmdsize cmdsize)
                                           (cons 'segname segname)
                                           (cons 'vmaddr vmaddr)
                                           (cons 'vmsize vmsize)
                                           (cons 'fileoff fileoff)
                                           (cons 'filesize filesize)
                                           (cons 'maxprot maxprot)
                                           (cons 'initprot initprot)
                                           (cons 'nsects nsects)
                                           (cons 'flags flags)))
                               section_64_ds)
                       rest-of-the-file mach-o))))

            (#.*LC_TWOLEVEL_HINTS*
             ;; TO-DO: Fetch the two-level namespace hint table
             ;; located at offset. nhints specifies the number of
             ;; twolevel_hint data structures.
             (b* (((mv offset   rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv  nhints   rest-of-the-file) (rnbni 4 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'offset offset)
                           (cons 'nhints nhints))
                     rest-of-the-file mach-o)))

            ((or #.*LC_LOAD_DYLIB* #.*LC_LOAD_WEAK_DYLIB* #.*LC_ID_DYLIB*)
             ;; TO-DO: Read the Discussion section in the
             ;; dylib_command section to know more about the linker's
             ;; responsibilities when doing dynamic loading of
             ;; executables.

             ;; For lc_str union:

             ;; * A variable length string in a load command is
             ;; * represented by an lc_str union.  The strings are
             ;; * stored just after the load command structure and the
             ;; * offset is from the start of the load command
             ;; * structure.  The size of the string is reflected in
             ;; * the cmdsize field of the load command.  Once again
             ;; * any padded bytes to bring the cmdsize field to a
             ;; * multiple of 4 bytes must be zero.

             (b* (((mv dylib.name->lc_str.offset   rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv dylib.timestamp             rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv dylib.current_version       rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv dylib.compatibility_version rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ;; The size of the string is the total size of this
                  ;; command minus the offset.
                  (lc_str-size (nfix (- cmdsize dylib.name->lc_str.offset)))
                  ;; The following removes padding (if any) between
                  ;; the end of this command and the beginning of the
                  ;; string.  (* 6 4) is the size of the (effectively)
                  ;; six fields of this command field.
                  (rest-of-the-file (nthcdr (nfix (- dylib.name->lc_str.offset (* 6 4))) rest-of-the-file))
                  ((mv lc_str->bytes rest-of-the-file) (rnbbi lc_str-size rest-of-the-file))
                  (lc_str->str (bytes-to-string lc_str->bytes)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'dylib.name->lc_str.offset dylib.name->lc_str.offset)
                           (cons 'dylib.timestamp dylib.timestamp)
                           (cons 'dylib.current_version dylib.current_version)
                           (cons 'dylib.compatibility_version dylib.compatibility_version)
                           (cons 'dylib.name->lc_str.offset lc_str->str))
                     rest-of-the-file mach-o)))

            ((or #.*LC_ID_DYLINKER* #.*LC_LOAD_DYLINKER*)
             (b* (((mv name->lc_str.offset rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ;; The size of the string is the total size of this
                  ;; command minus the offset.
                  (lc_str-size (nfix (- cmdsize name->lc_str.offset)))
                  ;; The following removes padding (if any) between
                  ;; the end of this command and the beginning of the
                  ;; string.  (* 3 4) is the size of the three fields
                  ;; of this command field.
                  (rest-of-the-file (nthcdr (nfix (- name->lc_str.offset (* 3 4))) rest-of-the-file))
                  ((mv lc_str->bytes rest-of-the-file) (rnbbi lc_str-size rest-of-the-file))
                  (lc_str->str (bytes-to-string lc_str->bytes)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'name->lc_str.offset name->lc_str.offset)
                           (cons 'lc_str->str lc_str->str)
                           )
                     rest-of-the-file mach-o)))

            (#.*LC_PREBOUND_DYLIB*
             (b* (((mv name->lc_str.offset           rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv nmodules                      rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv linked_modules->lc_str.offset rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ;; The size of the string is the total size of this
                  ;; command minus the offset.
                  (linked_modules-lc_str-size (nfix (- cmdsize linked_modules->lc_str.offset)))
                  (name-lc_str-size (nfix (- (nfix (- cmdsize name->lc_str.offset)) linked_modules-lc_str-size)))
                  ;; The following removes padding (if any) between
                  ;; the end of this command and the beginning of the
                  ;; string.  (* 5 4) is the size of the (effectively)
                  ;; six fields of this command field.
                  (rest-of-the-file (nthcdr (nfix (- name->lc_str.offset (* 5 4))) rest-of-the-file))
                  ((mv name-lc_str->bytes rest-of-the-file) (rnbbi name-lc_str-size rest-of-the-file))
                  (name-lc_str->str (bytes-to-string name-lc_str->bytes))
                  ((mv linked_modules-lc_str->bytes rest-of-the-file) (rnbbi linked_modules-lc_str-size rest-of-the-file))
                  (linked_modules-lc_str->str (bytes-to-string linked_modules-lc_str->bytes)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'name->lc_str.offset name->lc_str.offset)
                           (cons 'nmodules nmodules)
                           (cons 'linked_modules->lc_str.offset linked_modules->lc_str.offset)
                           (cons 'name-lc_str->str name-lc_str->str)
                           (cons 'linked_modules-lc_str->str linked_modules-lc_str->str))
                     rest-of-the-file mach-o)))

            ((or #.*LC_THREAD* #.*LC_UNIXTHREAD*)
             ;; TO-DO: Specific to each architecture.
             (mv (list (cons 'cmd cmd)
                       (cons 'cmdsize cmdsize))
                 rest-of-the-file mach-o))

            (#.*LC_ROUTINES*
             (b* (((mv init_address rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv init_module  rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv reserved1    rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv reserved2    rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv reserved3    rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv reserved4    rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv reserved5    rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ((mv reserved6    rest-of-the-file) (rnbni 4 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'init_address init_address)
                           (cons 'init_module init_module)
                           (cons 'reserved1 reserved1)
                           (cons 'reserved2 reserved2)
                           (cons 'reserved3 reserved3)
                           (cons 'reserved4 reserved4)
                           (cons 'reserved5 reserved5)
                           (cons 'reserved6 reserved6))
                     rest-of-the-file mach-o)))

            (#.*LC_ROUTINES_64*
             (b* (((mv init_address rest-of-the-file) (rnbni 8 rest-of-the-file))
                  ((mv init_module  rest-of-the-file) (rnbni 8 rest-of-the-file))
                  ((mv reserved1    rest-of-the-file) (rnbni 8 rest-of-the-file))
                  ((mv reserved2    rest-of-the-file) (rnbni 8 rest-of-the-file))
                  ((mv reserved3    rest-of-the-file) (rnbni 8 rest-of-the-file))
                  ((mv reserved4    rest-of-the-file) (rnbni 8 rest-of-the-file))
                  ((mv reserved5    rest-of-the-file) (rnbni 8 rest-of-the-file))
                  ((mv reserved6    rest-of-the-file) (rnbni 8 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'init_address init_address)
                           (cons 'init_module init_module)
                           (cons 'reserved1 reserved1)
                           (cons 'reserved2 reserved2)
                           (cons 'reserved3 reserved3)
                           (cons 'reserved4 reserved4)
                           (cons 'reserved5 reserved5)
                           (cons 'reserved6 reserved6))
                     rest-of-the-file mach-o)))

            (#.*LC_SUB_FRAMEWORK*
             (b* (((mv umbrella->lc_str.offset rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ;; The size of the string is the total size of this
                  ;; command minus the offset.
                  (lc_str-size (nfix (- cmdsize umbrella->lc_str.offset)))
                  ;; The following removes padding (if any) between
                  ;; the end of this command and the beginning of the
                  ;; string.  (* 3 4) is the size of the three fields
                  ;; of this command field.
                  (rest-of-the-file (nthcdr (nfix (- umbrella->lc_str.offset (* 3 4))) rest-of-the-file))
                  ((mv lc_str->bytes rest-of-the-file) (rnbbi lc_str-size rest-of-the-file))
                  (lc_str->str (bytes-to-string lc_str->bytes)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'umbrella->lc_str.offset umbrella->lc_str.offset)
                           (cons 'lc_str->str lc_str->str))
                     rest-of-the-file mach-o)))

            (#.*LC_SUB_UMBRELLA*
             (b* (((mv sub_umbrella->lc_str.offset rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ;; The size of the string is the total size of this
                  ;; command minus the offset.
                  (lc_str-size (nfix (- cmdsize sub_umbrella->lc_str.offset)))
                  ;; The following removes padding (if any) between
                  ;; the end of this command and the beginning of the
                  ;; string.  (* 3 4) is the size of the three fields
                  ;; of this command field.
                  (rest-of-the-file (nthcdr (nfix (- sub_umbrella->lc_str.offset (* 3 4))) rest-of-the-file))
                  ((mv lc_str->bytes rest-of-the-file) (rnbbi lc_str-size rest-of-the-file))
                  (lc_str->str (bytes-to-string lc_str->bytes)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'sub_umbrella->lc_str.offset sub_umbrella->lc_str.offset)
                           (cons 'lc_str->str lc_str->str))
                     rest-of-the-file mach-o)))

            (#.*LC_SUB_LIBRARY*
             (b* (((mv sub_library->lc_str.offset rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ;; The size of the string is the total size of this
                  ;; command minus the offset.
                  (lc_str-size (nfix (- cmdsize sub_library->lc_str.offset)))
                  ;; The following removes padding (if any) between
                  ;; the end of this command and the beginning of the
                  ;; string.  (* 3 4) is the size of the three fields
                  ;; of this command field.
                  (rest-of-the-file (nthcdr (nfix (- sub_library->lc_str.offset (* 3 4))) rest-of-the-file))
                  ((mv lc_str->bytes rest-of-the-file) (rnbbi lc_str-size rest-of-the-file))
                  (lc_str->str (bytes-to-string lc_str->bytes)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'sub_library->lc_str.offset sub_library->lc_str.offset)
                           (cons 'lc_str->str lc_str->str))
                     rest-of-the-file mach-o)))

            (#.*LC_SUB_CLIENT*
             (b* (((mv client->lc_str.offset rest-of-the-file) (rnbni 4 rest-of-the-file))
                  ;; The size of the string is the total size of this
                  ;; command minus the offset.
                  (lc_str-size (nfix (- cmdsize client->lc_str.offset)))
                  ;; The following removes padding (if any) between
                  ;; the end of this command and the beginning of the
                  ;; string.  (* 3 4) is the size of the three fields
                  ;; of this command field.
                  (rest-of-the-file (nthcdr (nfix (- client->lc_str.offset (* 3 4))) rest-of-the-file))
                  ((mv lc_str->bytes rest-of-the-file) (rnbbi lc_str-size rest-of-the-file))
                  (lc_str->str (bytes-to-string lc_str->bytes)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'client->lc_str.offset client->lc_str.offset)
                           (cons 'lc_str->str lc_str->str))
                     rest-of-the-file mach-o)))

            (#.*LC_SYMTAB*
             (b* (((mv symoff  rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nsyms   rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv stroff  rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv strsize rest-of-the-file)  (rnbni 4 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'symoff symoff)
                           (cons 'nsyms nsyms)
                           (cons 'stroff stroff)
                           (cons 'strsize strsize))
                     rest-of-the-file mach-o)))

            (#.*LC_DYSYMTAB*
             (b* (((mv ilocalsym      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nlocalsym      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv iextdefsym     rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nextdefsym     rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv iundefsym      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nundefsym      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv tocoff         rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv ntoc           rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv modtaboff      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nmodtab        rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv extrefsymoff   rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nextrefsyms    rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv indirectsymoff rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nindirectsyms  rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv extreloff      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nextrel        rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv locreloff      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv nlocrel        rest-of-the-file)  (rnbni 4 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'ilocalsym ilocalsym)
                           (cons 'nlocalsym nlocalsym)
                           (cons 'iextdefsym iextdefsym)
                           (cons 'nextdefsym nextdefsym)
                           (cons 'iundefsym iundefsym)
                           (cons 'nundefsym nundefsym)
                           (cons 'tocoff tocoff)
                           (cons 'ntoc ntoc)
                           (cons 'modtaboff modtaboff)
                           (cons 'nmodtab nmodtab)
                           (cons 'extrefsymoff extrefsymoff)
                           (cons 'nextrefsyms nextrefsyms)
                           (cons 'indirectsymoff indirectsymoff)
                           (cons 'nindirectsyms nindirectsyms)
                           (cons 'extreloff extreloff)
                           (cons 'nextrel nextrel)
                           (cons 'locreloff locreloff)
                           (cons 'nlocrel nlocrel))
                     rest-of-the-file mach-o)))

            ((or #.*LC_DYLD_INFO* #.*LC_DYLD_INFO_ONLY*)
             (b* (((mv rebase_off     rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv rebase_size    rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv bind_off       rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv bind_size      rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv weak_bind_off  rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv weak_bind_size rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv lazy_bind_off  rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv lazy_bind_size rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv export_off     rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv export_size    rest-of-the-file)  (rnbni 4 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'rebase_off     rebase_off)
                           (cons 'rebase_size    rebase_size)
                           (cons 'bind_off       bind_off)
                           (cons 'bind_size      bind_size)
                           (cons 'weak_bind_off  weak_bind_off)
                           (cons 'weak_bind_size weak_bind_size)
                           (cons 'lazy_bind_off  lazy_bind_off)
                           (cons 'lazy_bind_size lazy_bind_size)
                           (cons 'export_off     export_off)
                           (cons 'export_size    export_size))
                     rest-of-the-file mach-o)))

            ((or #.*LC_CODE_SIGNATURE*
                 #.*LC_SEGMENT_SPLIT_INFO*
                 #.*LC_FUNCTION_STARTS*
                 #.*LC_DATA_IN_CODE*
                 #.*LC_DYLIB_CODE_SIGN_DRS*)
             (b* (((mv data_off     rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv data_size    rest-of-the-file)  (rnbni 4 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'data_off data_off)
                           (cons 'data_size data_size))
                     rest-of-the-file mach-o)))

            ((or #.*LC_VERSION_MIN_MACOSX*
                 #.*LC_VERSION_MIN_IPHONEOS*)
             (b* (((mv version rest-of-the-file)  (rnbni 4 rest-of-the-file))
                  ((mv sdk     rest-of-the-file)  (rnbni 4 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'version version)
                           (cons 'sdk sdk))
                     rest-of-the-file mach-o)))

            (#.*LC_SOURCE_VERSION*
             (b* (((mv version rest-of-the-file)  (rnbni 8 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'version version))
                     rest-of-the-file mach-o)))

            (#.*LC_MAIN*
             (b* (((mv entryoff  rest-of-the-file)  (rnbni 8 rest-of-the-file))
                  ((mv stacksize rest-of-the-file)  (rnbni 8 rest-of-the-file)))
                 (mv (list (cons 'cmd cmd)
                           (cons 'cmdsize cmdsize)
                           (cons 'entryoff entryoff)
                           (cons 'stacksize stacksize))
                     rest-of-the-file mach-o)))

            (t
             (mv (cw "(Error: Unrecognized/unimplemented load command:~x0)~%" cmd) rest-of-the-file mach-o)))))

        (read-load_commands (1- ncmds) remaining-file
                            (cons cmd_list acc) mach-o))))

(defthm byte-listp-mv-nth-1-read-load_commands
  (implies (byte-listp rest-of-the-file)
           (byte-listp (mv-nth 1 (read-load_commands
                                  ncmds rest-of-the-file acc mach-o))))
  :hints (("Goal" :in-theory (e/d ()
                                  (nfix
                                   fix reverse
                                   (:meta acl2::mv-nth-cons-meta)
                                   member-equal
                                   len-mv-nth-1-rnbni-1
                                   len-mv-nth-1-rnbni-2
                                   byte-listp-mv-nth-1-rnbni
                                   mv-nth-0-rnbni-linear-1
                                   mv-nth-0-rnbni-linear-2
                                   len
                                   nthcdr)))))

(defthm mach-op-mv-nth-2-read-load_commands
  (implies (and (mach-op mach-o)
                (byte-listp rest-of-the-file))
           (mach-op (mv-nth 2 (read-load_commands
                               ncmds rest-of-the-file acc mach-o))))
  :hints (("Goal" :in-theory (e/d ()
                                  (nfix fix member-equal
                                        nthcdr append reverse atom
                                        len-mv-nth-1-rnbni-1
                                        len-mv-nth-1-rnbni-2)))))

(in-theory (disable read-load_commands))

;;----------------------------------------------------------------------
;; Fill the sections of the __TEXT segment into mach-o:
;;----------------------------------------------------------------------

(defun fill-TEXT-text-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (TEXT-text-section-size mach-o))
       (offset (TEXT-text-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly.  TEXT::text section could not be read.~%") mach-o state))
       (mach-o (!TEXT-text-section-bytes section mach-o)))
      (mv nil mach-o state)))

(defthm mach-op-mv-nth-1-fill-TEXT-text-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-TEXT-text-section-bytes
                      h-size lc-size remaining-file mach-o state))))
  :hints (("Goal" :in-theory (e/d ()
                                  (nfix fix member-equal
                                        nthcdr append reverse atom
                                        len-mv-nth-1-rnbni-1
                                        len-mv-nth-1-rnbni-2)))))

(defthm state-p-mv-nth-2-fill-TEXT-text-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-TEXT-text-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-TEXT-text-section-bytes))

(defun fill-TEXT-cstring-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (TEXT-cstring-section-size mach-o))
       (offset (TEXT-cstring-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly.  TEXT::cstring section could not be read.~%")
         mach-o state))
       (mach-o (!TEXT-cstring-section-bytes section mach-o)))
      (mv nil mach-o state)))


(defthm mach-op-mv-nth-1-fill-TEXT-cstring-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-TEXT-cstring-section-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-TEXT-cstring-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-TEXT-cstring-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-TEXT-cstring-section-bytes))

(defun fill-TEXT-const-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (TEXT-const-section-size mach-o))
       (offset (TEXT-const-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly.  TEXT::const section could not be read.~%")
         mach-o state))
       (mach-o (!TEXT-const-section-bytes section mach-o)))
      (mv nil mach-o state)))

(defthm mach-op-mv-nth-1-fill-TEXT-const-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                   1
                   (fill-TEXT-const-section-bytes
                    h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-TEXT-const-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-TEXT-const-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-TEXT-const-section-bytes))

(defun fill-TEXT-segment-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))
  (b* (
       ;; text section
       ((mv flg mach-o state)
        (fill-TEXT-text-section-bytes h-size lc-size
                                      remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; cstring section
       ((mv flg mach-o state)
        (fill-TEXT-cstring-section-bytes h-size lc-size
                                         remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; const section:
       ((mv flg mach-o state)
        (fill-TEXT-const-section-bytes h-size lc-size
                                       remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state)))

      (mv flg mach-o state)))

(defthm mach-op-mv-nth-1-fill-TEXT-segment-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-TEXT-segment-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-TEXT-segment-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-TEXT-segment-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-TEXT-segment-bytes))

;;----------------------------------------------------------------------
;; Fill the sections of the __DATA segment into mach-o:
;;----------------------------------------------------------------------

(defun fill-DATA-data-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (DATA-data-section-size mach-o))
       (offset (DATA-data-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly.  DATA::data section could not be read.~%")
         mach-o state))
       (mach-o (!DATA-data-section-bytes section mach-o)))
      (mv nil mach-o state)))

(defthm mach-op-mv-nth-1-fill-DATA-data-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-DATA-data-section-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-DATA-data-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-DATA-data-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-DATA-data-section-bytes))

(defun fill-DATA-dyld-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (DATA-dyld-section-size mach-o))
       (offset (DATA-dyld-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly in file ~x0.  DATA::dyld section could not be read.~%")
         mach-o state))
       (mach-o (!DATA-dyld-section-bytes section mach-o)))
      (mv nil mach-o state)))

(defthm mach-op-mv-nth-1-fill-DATA-dyld-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-DATA-dyld-section-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-DATA-dyld-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-DATA-dyld-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-DATA-dyld-section-bytes))

(defun fill-DATA-const-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (DATA-const-section-size mach-o))
       (offset (DATA-const-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly. DATA::const section could not be read.~%")
         mach-o state))
       (mach-o (!DATA-const-section-bytes section mach-o)))
      (mv nil mach-o state)))

(defthm mach-op-mv-nth-1-fill-DATA-const-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-DATA-const-section-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-DATA-const-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-DATA-const-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-DATA-const-section-bytes))

(defun fill-DATA-bss-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (DATA-bss-section-size mach-o))
       (offset (DATA-bss-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly.  DATA::bss section could not be read.~%")
         mach-o state))
       (mach-o (!DATA-bss-section-bytes section mach-o)))
      (mv nil mach-o state)))

(defthm mach-op-mv-nth-1-fill-DATA-bss-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-DATA-bss-section-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-DATA-bss-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-DATA-bss-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-DATA-bss-section-bytes))

(defun fill-DATA-common-section-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))

  (b* ((size (DATA-common-section-size mach-o))
       (offset (DATA-common-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (mv
         (cw "EOF encountered unexpectedly. DATA::common section could not be read.~%")
         mach-o state))
       (mach-o (!DATA-common-section-bytes section mach-o)))
      (mv nil mach-o state)))

(defthm mach-op-mv-nth-1-fill-DATA-common-section-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-DATA-common-section-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-DATA-common-section-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-DATA-common-section-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-DATA-common-section-bytes))

(defun fill-DATA-segment-bytes
  (h-size lc-size remaining-file mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (and (n64p h-size)
                              (n64p lc-size)
                              (byte-listp remaining-file))))
  (b* (
       ;; data section:
       ((mv flg mach-o state)
        (fill-DATA-data-section-bytes h-size lc-size
                                      remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; dyld section:

       ((mv flg mach-o state)
        (fill-DATA-dyld-section-bytes h-size lc-size
                                      remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; const section:

       ((mv flg mach-o state)
        (fill-DATA-const-section-bytes h-size lc-size
                                       remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; bss section:

       ((mv flg mach-o state)
        (fill-DATA-bss-section-bytes h-size lc-size
                                     remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; common section:

       ((mv flg mach-o state)
        (fill-DATA-common-section-bytes h-size lc-size
                                        remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state)))

      (mv flg mach-o state)))

(defthm mach-op-mv-nth-1-fill-DATA-segment-bytes
  (implies (mach-op mach-o)
           (mach-op (mv-nth
                     1
                     (fill-DATA-segment-bytes
                      h-size lc-size remaining-file mach-o state)))))

(defthm state-p-mv-nth-2-fill-DATA-segment-bytes
  (implies (ACL2::state-p state)
           (ACL2::state-p
            (mv-nth 2
                    (fill-DATA-segment-bytes
                     h-size lc-size remaining-file mach-o
                     state))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(in-theory (disable fill-DATA-segment-bytes))

;;----------------------------------------------------------------------
;; Function file-read and supporting events:
;;----------------------------------------------------------------------

(defun mach-o-file-read (file-byte-list mach-o state)
  (declare (xargs :stobjs (mach-o state)
                  :guard (byte-listp file-byte-list)
                  :guard-hints (("Goal"
                                 :in-theory
                                 (e/d (read-mach_header)
                                      (byte-listp
                                       unsigned-byte-p
                                       nfix fix
                                       not natp mach-op))))))

  (b* ((file-size (len file-byte-list))
       (mach-o (!mach-o-file-size file-size mach-o))
       (file-header (take 32 file-byte-list))
       ((when (not (byte-listp file-header)))
        (mv
         (cw "Header could not be read.~%")
         mach-o state))

       ;; The following checks are also done in the top-level function
       ;; binary-file-read (in tools/execution/top.lisp).  They're
       ;; done here again in case someone wants to use this function
       ;; at the top level.
       (header (read-mach_header file-header))
       (magic (nfix (cdr (assoc 'MAGIC header))))
       ((when (and (not (equal magic #.*MH_MAGIC*))
                   (not (equal magic #.*MH_CIGAM*))
                   (not (equal magic #.*MH_MAGIC_64*))
                   (not (equal magic #.*MH_CIGAM_64*))))
        (mv (cw "Error: Not an object file (as suggested by the magic number).~%")
            mach-o
            state))
       ((when (not (n64p (cdr (assoc 'sizeofcmds header)))))
        (mv (cw "Mach-O File Read Error: Sizeofcmds ~x0 ill-formed~%" (cdr (assoc 'sizeofcmds header)))
            mach-o
            state))
       (mach-o (!load-cmds-size (cdr (assoc 'sizeofcmds header)) mach-o))
       (mach-o-header-size
        (if (and (or (equal magic #.*MH_MAGIC*)
                     (equal magic #.*MH_CIGAM*))
                 (equal (cdr (assoc 'reserved header)) nil))
            28
          32))
       (mach-o (!mach-o-header-size mach-o-header-size mach-o))
       (file-byte-list (nthcdr mach-o-header-size file-byte-list))
       (ncmds (nfix (cdr (assoc 'NCMDS header))))
       ((mv cmds remaining-file mach-o)
        (read-load_commands ncmds file-byte-list nil mach-o))
       (h-size (mach-o-header-size mach-o))
       (lc-size (load-cmds-size mach-o))

       ;; TEXT segment
       ((mv flg mach-o state)
        (fill-TEXT-segment-bytes h-size lc-size
                                 remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; DATA segment
       ((mv flg mach-o state)
        (fill-DATA-segment-bytes h-size lc-size
                                 remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state)))

      (mv (acons 'HEADER header
                 (acons 'CMDS cmds nil))
          mach-o
          state)))

(defthm mach-op-mv-nth-1-file-read
  (implies (and (byte-listp file-byte-list)
                (mach-op mach-o))
           (mach-op (mv-nth 1 (mach-o-file-read file-byte-list mach-o state)))))

(defthm state-p-mv-nth-2-file-read
  (implies (ACL2::state-p state)
           (ACL2::state-p (mv-nth 2 (mach-o-file-read file-byte-list mach-o state)))))

(in-theory (disable mach-o-file-read))

;; ======================================================================

;;----------------------------------------------------------------------
;; Functions to load the x86 stobj based on the information in the
;; mach-o stobj:
;; ----------------------------------------------------------------------

;; (mach-o-file-read <file-byte-list> mach-o state)

;; (load-qwords-into-physical-memory-list *1-gig-page-tables* x86)

(defun mach-o-load-text-section (mach-o x86)
  (declare (xargs :stobjs (mach-o x86)))
  (b* ((text-sec-load-addr (TEXT-text-section-addr mach-o))
       (text-section-bytes (TEXT-text-section-bytes mach-o))
       (- (if (equal text-section-bytes nil)
              (cw "~%Text section empty.~%~%")
            t))
       ((when (or (not (canonical-address-p text-sec-load-addr))
                  (not (canonical-address-p (+ text-sec-load-addr
                                               (len text-section-bytes))))))
        (mv (cons 'text-sec-load-addr text-sec-load-addr) x86)))
      (write-bytes-to-memory text-sec-load-addr text-section-bytes x86)))

(defun mach-o-load-data-section (mach-o x86)
  (declare (xargs :stobjs (mach-o x86)))
  (b* ((data-sec-load-addr (DATA-data-section-addr mach-o))
       (data-section-bytes (DATA-data-section-bytes mach-o))
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

       (cr0        (!cr0-slice       :cr0-pg        1 cr0))
       (cr4        (!cr4-slice       :cr4-pae       1 cr4))
       (ia32e-efer (!ia32_efer-slice :ia32_efer-lme 1 ia32e-efer))

       (x86 (!ctri *cr0*           cr0        x86))
       (x86 (!ctri *cr4*           cr4        x86))
       (x86 (!msri *ia32_efer-idx* ia32e-efer x86))

       (x86 (!ctri *cr3* #x0 x86)))
  x86)

(mach-o-load-text-section mach-o x86)

||#

;; ======================================================================
