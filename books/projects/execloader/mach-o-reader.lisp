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
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>

; [Shilpi Goel] This book used to live in
; [books]/projects/x86isa/tools/execution/exec-loaders, but now it's
; in a stand-alone library of its own.

;; A very simple Mach-O File Reader and Loader

;; ======================================================================

(in-package "EXLD")

(include-book "mach-o-stobj")
(include-book "mach-o-structs")
(include-book "std/io/read-file-bytes" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (in-theory (e/d () (unsigned-byte-p))))

;; ======================================================================

(defxdoc mach-o-reader
  :parents (execloader)
  :short "Read in parts of MACH-O format files into fields of the @('mach-o') stobj"
  )

(local (xdoc::set-default-parents mach-o-reader))

;; ----------------------------------------------------------------------

(define read-mach_header ((file-header byte-listp))
  :short "Parse Mach-O header"
  :guard-debug t
  :returns (header mach-o-header-p)
  (b* (((unless (or (= (len file-header) 28)
                    (= (len file-header) 32)))
        (prog2$
         (raise "Mach-O header's length should be either 28 or 32, but it is ~x0 instead!"
                (len file-header))
         (make-mach-o-header)))
       ((mv magic       file-header) (merge-first-split-bytes 4 file-header))
       ((mv cputype     file-header) (merge-first-split-bytes 4 file-header))
       ((mv cpusubtype  file-header) (merge-first-split-bytes 4 file-header))
       ((mv filetype    file-header) (merge-first-split-bytes 4 file-header))
       ((mv ncmds       file-header) (merge-first-split-bytes 4 file-header))
       ((mv sizeofcmds  file-header) (merge-first-split-bytes 4 file-header))
       ((mv flags       file-header) (merge-first-split-bytes 4 file-header))
       ((mv reserved   ?file-header)
        (if (or (equal magic *MH_MAGIC_64*)
                (equal magic *MH_CIGAM_64*))
            (merge-first-split-bytes 4 file-header)
          ;; No reserved field for 32-bit object files.
          (mv nil file-header))))
    (make-mach-o-header
     :magic      magic
     :cputype    cputype
     :cpusubtype cpusubtype
     :filetype   filetype
     :ncmds      ncmds
     :sizeofcmds sizeofcmds
     :flags      flags
     :reserved   reserved)))

(local
 (defthm unsigned-byte-p-64-of-mv-nth-0-merge-first-split-bytes-4
   (implies (byte-listp bytes)
            (unsigned-byte-p 64 (mv-nth 0 (merge-first-split-bytes 4 bytes))))
   :hints (("Goal"
            :use ((:instance width-of-mv-nth-0-merge-first-split-bytes
                             (m 32) (n 4) (bytes bytes)))
            :in-theory (e/d ()
                            (width-of-mv-nth-0-merge-first-split-bytes))))))

(define read-section_data_sz_structures ((nsects natp)
                                         sz
                                         (rest-of-the-file byte-listp)
                                         (acc true-listp)
                                         mach-o)
  :short "Read the section data structures"
  :guard (and (or (and (equal sz 4)
                       (<= (* nsects 68) (len rest-of-the-file)))
                  (and (equal sz 8)
                       (<= (* nsects 80) (len rest-of-the-file)))))

  :returns (mv new-acc
               (file-bytes byte-listp :hyp (byte-listp rest-of-the-file))
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o)))

  (if (zp nsects)
      (mv (reverse acc) rest-of-the-file mach-o)

    (b* (((mv sectbytes rest-of-the-file)  (split-bytes  16 rest-of-the-file))
         ((mv segbytes  rest-of-the-file)  (split-bytes  16 rest-of-the-file))
         ((mv addr      rest-of-the-file)  (merge-first-split-bytes  sz rest-of-the-file))
         ((mv size      rest-of-the-file)  (merge-first-split-bytes  sz rest-of-the-file))
         ((mv offset    rest-of-the-file)  (merge-first-split-bytes   4 rest-of-the-file))
         ((mv align     rest-of-the-file)  (merge-first-split-bytes   4 rest-of-the-file))
         ((mv reloff    rest-of-the-file)  (merge-first-split-bytes   4 rest-of-the-file))
         ((mv nreloc    rest-of-the-file)  (merge-first-split-bytes   4 rest-of-the-file))
         ((mv flags     rest-of-the-file)  (merge-first-split-bytes   4 rest-of-the-file))
         ((mv reserved1 rest-of-the-file)  (merge-first-split-bytes   4 rest-of-the-file))
         ((mv reserved2 rest-of-the-file)  (merge-first-split-bytes   4 rest-of-the-file))
         (sectname                         (bytes->string sectbytes))
         (segname                          (bytes->string segbytes))
         (sect                             (merge-bytes (take-till-zero sectbytes)))
         (seg                              (merge-bytes (take-till-zero segbytes)))
         ((mv reserved3 rest-of-the-file)
          (if (equal sz 8)
              (merge-first-split-bytes 4 rest-of-the-file)
            (mv nil rest-of-the-file)))

         (mach-o
          (cond
           ((equal seg *MACH-O-TEXT*)

            (cond

             ((equal sect *TEXT-text*)
              (b* ((mach-o (!TEXT-text-section-addr addr mach-o))
                   (mach-o (!TEXT-text-section-size size mach-o))
                   (mach-o (!TEXT-text-section-offset offset mach-o)))
                mach-o))

             ((equal sect *TEXT-cstring*)
              (b* ((mach-o (!TEXT-cstring-section-addr addr mach-o))
                   (mach-o (!TEXT-cstring-section-size size mach-o))
                   (mach-o (!TEXT-cstring-section-offset offset mach-o)))
                mach-o))

             ((equal sect *TEXT-const*)
              (b* ((mach-o (!TEXT-const-section-addr addr mach-o))
                   (mach-o (!TEXT-const-section-size size mach-o))
                   (mach-o (!TEXT-const-section-offset offset mach-o)))
                mach-o))

             (t mach-o)))

           ((equal seg *MACH-O-DATA*)

            (cond

             ((equal sect *DATA-data*)
              (b* ((mach-o (!DATA-data-section-addr addr mach-o))
                   (mach-o (!DATA-data-section-size size mach-o))
                   (mach-o (!DATA-data-section-offset offset mach-o)))
                mach-o))

             ((equal sect *DATA-dyld*)
              (b* ((mach-o (!DATA-dyld-section-addr addr mach-o))
                   (mach-o (!DATA-dyld-section-size size mach-o))
                   (mach-o (!DATA-dyld-section-offset offset mach-o)))
                mach-o))

             ((equal sect *DATA-const*)
              (b* ((mach-o (!DATA-const-section-addr addr mach-o))
                   (mach-o (!DATA-const-section-size size mach-o))
                   (mach-o (!DATA-const-section-offset offset mach-o)))
                mach-o))

             ((equal sect *DATA-bss*)
              (b* ((mach-o (!DATA-bss-section-addr addr mach-o))
                   (mach-o (!DATA-bss-section-size size mach-o))
                   (mach-o (!DATA-bss-section-offset offset mach-o)))
                mach-o))

             ((equal sect *DATA-common*)
              (b* ((mach-o (!DATA-common-section-addr addr mach-o))
                   (mach-o (!DATA-common-section-size size mach-o))
                   (mach-o (!DATA-common-section-offset offset mach-o)))
                mach-o))

             (t mach-o)))

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
             acc)
       mach-o)))

  ///

  (defthm len-mv-nth-1-read-section_data_sz_structures-sz=4
    (implies (and (natp nsects)
                  (and (equal sz 4)
                       (<= (* nsects 68) (len (double-rewrite rest-of-the-file))))
                  (byte-listp (double-rewrite rest-of-the-file)))
             (<= (- (len (double-rewrite rest-of-the-file)) (* nsects 68))
                 (len (mv-nth 1 (read-section_data_sz_structures
                                 nsects sz rest-of-the-file acc mach-o)))))
    :rule-classes :linear)

  (defthm len-mv-nth-1-read-section_data_sz_structures-sz=8
    (implies (and (natp nsects)
                  (and (equal sz 8)
                       (<= (* nsects 80) (len (double-rewrite rest-of-the-file))))
                  (byte-listp (double-rewrite rest-of-the-file)))
             (<= (- (len (double-rewrite rest-of-the-file)) (* nsects 80))
                 (len (mv-nth 1 (read-section_data_sz_structures
                                 nsects sz rest-of-the-file acc mach-o)))))
    :rule-classes :linear))

(define read-load_commands ((ncmds natp)
                            (rest-of-the-file byte-listp)
                            (acc true-listp)
                            mach-o)
  :short "Read the load commands (which in turn read the section data
  structures; see @(tsee read-section_data_sz_structures))"
  :returns
  (mv new-acc
      (file-bytes byte-listp :hyp (byte-listp rest-of-the-file))
      (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o)
                  :hints (("Goal" :in-theory (e/d () (good-mach-o-p))))))

  (if (zp ncmds)
      (mv (reverse acc) rest-of-the-file mach-o)

    (b* (((mv cmd rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv cmdsize rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
         ((mv cmd_list remaining-file mach-o)
          (cond

           ((equal cmd *LC_UUID*)
            (b* (((mv uuid rest-of-the-file) (merge-first-split-bytes 16 rest-of-the-file)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'uuid uuid))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_SEGMENT*)
            (b* (((mv segbytes rest-of-the-file) (split-bytes  16 rest-of-the-file))
                 ((mv vmaddr   rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv vmsize   rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv fileoff  rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv filesize rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv maxprot  rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv initprot rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv nsects   rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv flags    rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 (segname                        (bytes->string segbytes))
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

           ((equal cmd *LC_SEGMENT_64*)
            (b* (((mv segbytes      rest-of-the-file) (split-bytes  16 rest-of-the-file))
                 ((mv vmaddr        rest-of-the-file) (merge-first-split-bytes  8 rest-of-the-file))
                 ((mv vmsize        rest-of-the-file) (merge-first-split-bytes  8 rest-of-the-file))
                 ((mv fileoff       rest-of-the-file) (merge-first-split-bytes  8 rest-of-the-file))
                 ((mv filesize      rest-of-the-file) (merge-first-split-bytes  8 rest-of-the-file))
                 ((mv maxprot       rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv initprot      rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv nsects        rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 ((mv flags         rest-of-the-file) (merge-first-split-bytes  4 rest-of-the-file))
                 (segname                             (bytes->string segbytes))
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

           ((equal cmd *LC_TWOLEVEL_HINTS*)
            ;; TO-DO: Fetch the two-level namespace hint table
            ;; located at offset. nhints specifies the number of
            ;; twolevel_hint data structures.
            (b* (((mv offset   rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv  nhints   rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'offset offset)
                        (cons 'nhints nhints))
                  rest-of-the-file mach-o)))

           ((member-equal cmd (list *LC_LOAD_DYLIB* *LC_LOAD_WEAK_DYLIB* *LC_ID_DYLIB*))
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

            (b* (((mv dylib.name->lc_str.offset   rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv dylib.timestamp             rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv dylib.current_version       rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv dylib.compatibility_version rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ;; The size of the string is the total size of this
                 ;; command minus the offset.
                 (lc_str-size (nfix (- cmdsize dylib.name->lc_str.offset)))
                 ;; The following removes padding (if any) between
                 ;; the end of this command and the beginning of the
                 ;; string.  (* 6 4) is the size of the (effectively)
                 ;; six fields of this command field.
                 (rest-of-the-file (nthcdr (nfix (- dylib.name->lc_str.offset (* 6 4))) rest-of-the-file))
                 ((mv lc_str->bytes rest-of-the-file) (split-bytes lc_str-size rest-of-the-file))
                 (lc_str->str (bytes->string lc_str->bytes)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'dylib.name->lc_str.offset dylib.name->lc_str.offset)
                        (cons 'dylib.timestamp dylib.timestamp)
                        (cons 'dylib.current_version dylib.current_version)
                        (cons 'dylib.compatibility_version dylib.compatibility_version)
                        (cons 'dylib.name->lc_str.offset lc_str->str))
                  rest-of-the-file mach-o)))

           ((member-equal cmd (list *LC_ID_DYLINKER* *LC_LOAD_DYLINKER*))
            (b* (((mv name->lc_str.offset rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ;; The size of the string is the total size of this
                 ;; command minus the offset.
                 (lc_str-size (nfix (- cmdsize name->lc_str.offset)))
                 ;; The following removes padding (if any) between
                 ;; the end of this command and the beginning of the
                 ;; string.  (* 3 4) is the size of the three fields
                 ;; of this command field.
                 (rest-of-the-file (nthcdr (nfix (- name->lc_str.offset (* 3 4))) rest-of-the-file))
                 ((mv lc_str->bytes rest-of-the-file) (split-bytes lc_str-size rest-of-the-file))
                 (lc_str->str (bytes->string lc_str->bytes)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'name->lc_str.offset name->lc_str.offset)
                        (cons 'lc_str->str lc_str->str)
                        )
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_PREBOUND_DYLIB*)
            (b* (((mv name->lc_str.offset           rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nmodules                      rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv linked_modules->lc_str.offset rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ;; The size of the string is the total size of this
                 ;; command minus the offset.
                 (linked_modules-lc_str-size (nfix (- cmdsize linked_modules->lc_str.offset)))
                 (name-lc_str-size (nfix (- (nfix (- cmdsize name->lc_str.offset)) linked_modules-lc_str-size)))
                 ;; The following removes padding (if any) between
                 ;; the end of this command and the beginning of the
                 ;; string.  (* 5 4) is the size of the (effectively)
                 ;; six fields of this command field.
                 (rest-of-the-file (nthcdr (nfix (- name->lc_str.offset (* 5 4))) rest-of-the-file))
                 ((mv name-lc_str->bytes rest-of-the-file) (split-bytes name-lc_str-size rest-of-the-file))
                 (name-lc_str->str (bytes->string name-lc_str->bytes))
                 ((mv linked_modules-lc_str->bytes rest-of-the-file) (split-bytes linked_modules-lc_str-size rest-of-the-file))
                 (linked_modules-lc_str->str (bytes->string linked_modules-lc_str->bytes)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'name->lc_str.offset name->lc_str.offset)
                        (cons 'nmodules nmodules)
                        (cons 'linked_modules->lc_str.offset linked_modules->lc_str.offset)
                        (cons 'name-lc_str->str name-lc_str->str)
                        (cons 'linked_modules-lc_str->str linked_modules-lc_str->str))
                  rest-of-the-file mach-o)))

           ((member-equal cmd (list *LC_THREAD* *LC_UNIXTHREAD*))
            ;; TO-DO: Specific to each architecture.
            (mv (list (cons 'cmd cmd)
                      (cons 'cmdsize cmdsize))
                rest-of-the-file mach-o))

           ((equal cmd *LC_ROUTINES*)
            (b* (((mv init_address rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv init_module  rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv reserved1    rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv reserved2    rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv reserved3    rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv reserved4    rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv reserved5    rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv reserved6    rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file)))
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

           ((equal cmd *LC_ROUTINES_64*)
            (b* (((mv init_address rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv init_module  rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv reserved1    rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv reserved2    rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv reserved3    rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv reserved4    rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv reserved5    rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv reserved6    rest-of-the-file) (merge-first-split-bytes 8 rest-of-the-file)))
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

           ((equal cmd *LC_SUB_FRAMEWORK*)
            (b* (((mv umbrella->lc_str.offset rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ;; The size of the string is the total size of this
                 ;; command minus the offset.
                 (lc_str-size (nfix (- cmdsize umbrella->lc_str.offset)))
                 ;; The following removes padding (if any) between
                 ;; the end of this command and the beginning of the
                 ;; string.  (* 3 4) is the size of the three fields
                 ;; of this command field.
                 (rest-of-the-file (nthcdr (nfix (- umbrella->lc_str.offset (* 3 4))) rest-of-the-file))
                 ((mv lc_str->bytes rest-of-the-file) (split-bytes lc_str-size rest-of-the-file))
                 (lc_str->str (bytes->string lc_str->bytes)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'umbrella->lc_str.offset umbrella->lc_str.offset)
                        (cons 'lc_str->str lc_str->str))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_SUB_UMBRELLA*)
            (b* (((mv sub_umbrella->lc_str.offset rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ;; The size of the string is the total size of this
                 ;; command minus the offset.
                 (lc_str-size (nfix (- cmdsize sub_umbrella->lc_str.offset)))
                 ;; The following removes padding (if any) between
                 ;; the end of this command and the beginning of the
                 ;; string.  (* 3 4) is the size of the three fields
                 ;; of this command field.
                 (rest-of-the-file (nthcdr (nfix (- sub_umbrella->lc_str.offset (* 3 4))) rest-of-the-file))
                 ((mv lc_str->bytes rest-of-the-file) (split-bytes lc_str-size rest-of-the-file))
                 (lc_str->str (bytes->string lc_str->bytes)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'sub_umbrella->lc_str.offset sub_umbrella->lc_str.offset)
                        (cons 'lc_str->str lc_str->str))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_SUB_LIBRARY*)
            (b* (((mv sub_library->lc_str.offset rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ;; The size of the string is the total size of this
                 ;; command minus the offset.
                 (lc_str-size (nfix (- cmdsize sub_library->lc_str.offset)))
                 ;; The following removes padding (if any) between
                 ;; the end of this command and the beginning of the
                 ;; string.  (* 3 4) is the size of the three fields
                 ;; of this command field.
                 (rest-of-the-file (nthcdr (nfix (- sub_library->lc_str.offset (* 3 4))) rest-of-the-file))
                 ((mv lc_str->bytes rest-of-the-file) (split-bytes lc_str-size rest-of-the-file))
                 (lc_str->str (bytes->string lc_str->bytes)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'sub_library->lc_str.offset sub_library->lc_str.offset)
                        (cons 'lc_str->str lc_str->str))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_SUB_CLIENT*)
            (b* (((mv client->lc_str.offset rest-of-the-file) (merge-first-split-bytes 4 rest-of-the-file))
                 ;; The size of the string is the total size of this
                 ;; command minus the offset.
                 (lc_str-size (nfix (- cmdsize client->lc_str.offset)))
                 ;; The following removes padding (if any) between
                 ;; the end of this command and the beginning of the
                 ;; string.  (* 3 4) is the size of the three fields
                 ;; of this command field.
                 (rest-of-the-file (nthcdr (nfix (- client->lc_str.offset (* 3 4))) rest-of-the-file))
                 ((mv lc_str->bytes rest-of-the-file) (split-bytes lc_str-size rest-of-the-file))
                 (lc_str->str (bytes->string lc_str->bytes)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'client->lc_str.offset client->lc_str.offset)
                        (cons 'lc_str->str lc_str->str))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_SYMTAB*)
            (b* (((mv symoff  rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nsyms   rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv stroff  rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv strsize rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'symoff symoff)
                        (cons 'nsyms nsyms)
                        (cons 'stroff stroff)
                        (cons 'strsize strsize))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_DYSYMTAB*)
            (b* (((mv ilocalsym      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nlocalsym      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv iextdefsym     rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nextdefsym     rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv iundefsym      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nundefsym      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv tocoff         rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv ntoc           rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv modtaboff      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nmodtab        rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv extrefsymoff   rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nextrefsyms    rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv indirectsymoff rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nindirectsyms  rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv extreloff      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nextrel        rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv locreloff      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv nlocrel        rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file)))
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

           ((member-equal cmd (list *LC_DYLD_INFO* *LC_DYLD_INFO_ONLY*))
            (b* (((mv rebase_off     rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv rebase_size    rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv bind_off       rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv bind_size      rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv weak_bind_off  rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv weak_bind_size rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv lazy_bind_off  rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv lazy_bind_size rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv export_off     rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv export_size    rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file)))
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

           ((member-equal cmd (list *LC_CODE_SIGNATURE*
                                    *LC_SEGMENT_SPLIT_INFO*
                                    *LC_FUNCTION_STARTS*
                                    *LC_DATA_IN_CODE*
                                    *LC_DYLIB_CODE_SIGN_DRS*))
            (b* (((mv data_off     rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv data_size    rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'data_off data_off)
                        (cons 'data_size data_size))
                  rest-of-the-file mach-o)))

           ((member-equal cmd (list *LC_VERSION_MIN_MACOSX*
                                    *LC_VERSION_MIN_IPHONEOS*))
            (b* (((mv version rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file))
                 ((mv sdk     rest-of-the-file)  (merge-first-split-bytes 4 rest-of-the-file)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'version version)
                        (cons 'sdk sdk))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_SOURCE_VERSION*)
            (b* (((mv version rest-of-the-file)  (merge-first-split-bytes 8 rest-of-the-file)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'version version))
                  rest-of-the-file mach-o)))

           ((equal cmd *LC_MAIN*)
            (b* (((mv entryoff  rest-of-the-file)  (merge-first-split-bytes 8 rest-of-the-file))
                 ((mv stacksize rest-of-the-file)  (merge-first-split-bytes 8 rest-of-the-file)))
              (mv (list (cons 'cmd cmd)
                        (cons 'cmdsize cmdsize)
                        (cons 'entryoff entryoff)
                        (cons 'stacksize stacksize))
                  rest-of-the-file mach-o)))

           (t
            (mv (cw "(Unrecognized/unimplemented load command:~x0)~%" cmd) rest-of-the-file mach-o)))))

      (read-load_commands (1- ncmds) remaining-file (cons cmd_list acc) mach-o))))

;; ----------------------------------------------------------------------
;; Fill the sections of the __TEXT segment into mach-o stobj:

(local
 (defthm mach-o-lemma-1
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :text-text-section-size i mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-text-text-section-size
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-text-text-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))
(local
 (defthm mach-o-lemma-2
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :text-text-section-offset i mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-text-text-section-offset                             
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-text-text-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(define fill-TEXT-text-section-bytes ((h-size :type (unsigned-byte 64))
                                      (lc-size :type (unsigned-byte 64))
                                      (remaining-file byte-listp)
                                      mach-o state)
  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))
  (b* ((size (@TEXT-text-section-size mach-o))
       (offset (@TEXT-text-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size (nthcdr (- offset (+ h-size lc-size)) remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly.  TEXT::text section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!TEXT-text-section-bytes section mach-o)))
    (mv nil mach-o state)))


(local
 (defthm mach-o-lemma-3
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :text-cstring-section-size nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-text-cstring-section-size
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-text-cstring-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))
(local
 (defthm mach-o-lemma-4
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :text-cstring-section-offset nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-text-cstring-section-offset
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-text-cstring-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(define fill-TEXT-cstring-section-bytes ((h-size :type (unsigned-byte 64))
                                         (lc-size :type (unsigned-byte 64))
                                         (remaining-file byte-listp)
                                         mach-o state)
  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))
  (b* ((size (@TEXT-cstring-section-size mach-o))
       (offset (@TEXT-cstring-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly.  TEXT::cstring section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!TEXT-cstring-section-bytes section mach-o)))
    (mv nil mach-o state)))


(local
 (defthm mach-o-lemma-5
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :text-const-section-size nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-text-const-section-size
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-text-const-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))
(local
 (defthm mach-o-lemma-6
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :text-const-section-offset nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-text-const-section-offset
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-text-const-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(define fill-TEXT-const-section-bytes ((h-size :type (unsigned-byte 64))
                                       (lc-size :type (unsigned-byte 64))
                                       (remaining-file byte-listp)
                                       mach-o state)
  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))

  (b* ((size (@TEXT-const-section-size mach-o))
       (offset (@TEXT-const-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly.  TEXT::const section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!TEXT-const-section-bytes section mach-o)))
    (mv nil mach-o state)))

(define fill-TEXT-segment-bytes ((h-size :type (unsigned-byte 64))
                                 (lc-size :type (unsigned-byte 64))
                                 (remaining-file byte-listp)
                                 mach-o state)
  :short "Fill the sections of the @('__TEXT') segment into @('mach-o') stobj"

  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))
  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o)
                           :hints (("Goal" :in-theory (e/d () (good-mach-o-p)))))
               (new-state acl2::state-p :hyp (acl2::state-p state)))
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

;;----------------------------------------------------------------------
;; Fill the sections of the __DATA segment into mach-o:

(local
 (defthm mach-o-lemma-7
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-data-section-size nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-data-section-size
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-data-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))
(local
 (defthm mach-o-lemma-8
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-data-section-offset nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-data-section-offset
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-data-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(define fill-DATA-data-section-bytes ((h-size  :type (unsigned-byte 64))
                                      (lc-size :type (unsigned-byte 64))
                                      (remaining-file byte-listp)
                                      mach-o state)
  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))

  (b* ((size (@DATA-data-section-size mach-o))
       (offset (@DATA-data-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly.  DATA::data section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!DATA-data-section-bytes section mach-o)))
    (mv nil mach-o state)))

(local
 (defthm mach-o-lemma-9
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-dyld-section-size nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-dyld-section-size
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-dyld-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))
(local
 (defthm mach-o-lemma-10
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-dyld-section-offset nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-dyld-section-offset
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-dyld-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))


(define fill-DATA-dyld-section-bytes ((h-size  :type (unsigned-byte 64))
                                      (lc-size :type (unsigned-byte 64))
                                      (remaining-file byte-listp)
                                      mach-o state)
  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))

  (b* ((size (@DATA-dyld-section-size mach-o))
       (offset (@DATA-dyld-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly in file ~x0.  DATA::dyld section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!DATA-dyld-section-bytes section mach-o)))
    (mv nil mach-o state)))

(local
 (defthm mach-o-lemma-11
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-const-section-size nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-const-section-size
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-const-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(local
 (defthm mach-o-lemma-12
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-const-section-offset nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-const-section-offset
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-const-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(define fill-DATA-const-section-bytes ((h-size :type (unsigned-byte 64))
                                       (lc-size :type (unsigned-byte 64))
                                       (remaining-file byte-listp)
                                       mach-o state)
  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))

  (b* ((size (@DATA-const-section-size mach-o))
       (offset (@DATA-const-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly. DATA::const section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!DATA-const-section-bytes section mach-o)))
    (mv nil mach-o state)))

(local
 (defthm mach-o-lemma-13
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-bss-section-size nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-bss-section-size
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-bss-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))
(local
 (defthm mach-o-lemma-14
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-bss-section-offset nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-bss-section-offset
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-bss-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(define fill-DATA-bss-section-bytes ((h-size :type (unsigned-byte 64))
                                     (lc-size :type (unsigned-byte 64))
                                     (remaining-file byte-listp)
                                     mach-o state)

  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))
  (b* ((size (@DATA-bss-section-size mach-o))
       (offset (@DATA-bss-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly.  DATA::bss section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!DATA-bss-section-bytes section mach-o)))
    (mv nil mach-o state)))

(local
 (defthm mach-o-lemma-15
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-common-section-size nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-common-section-size
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-common-section-size
                             good-mach-o-p))))
   :rule-classes :type-prescription))
(local
 (defthm mach-o-lemma-16
   (implies (good-mach-o-p mach-o)
            (natp (@mach-o :data-common-section-offset nil mach-o)))
   :hints (("Goal"
            :use ((:instance elem-p-of-@mach-o-data-common-section-offset
                             (i nil)
                             (mach-o$a mach-o)))
            :in-theory (e/d (unsigned-byte-p)
                            (elem-p-of-@mach-o-data-common-section-offset
                             good-mach-o-p))))
   :rule-classes :type-prescription))

(define fill-DATA-common-section-bytes ((h-size :type (unsigned-byte 64))
                                        (lc-size :type (unsigned-byte 64))
                                        (remaining-file byte-listp)
                                        mach-o state)
  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o))
               (new-state acl2::state-p :hyp (acl2::state-p state)))

  (b* ((size (@DATA-common-section-size mach-o))
       (offset (@DATA-common-section-offset mach-o))
       (section
        (if (equal size 0)
            nil
          (if (not (natp (- offset (+ h-size lc-size))))
              t ;; Will raise an error in the following "when".
            (take size
                  (nthcdr (- offset (+ h-size lc-size))
                          remaining-file)))))
       ((when (not (byte-listp section)))
        (cw "EOF encountered unexpectedly. DATA::common section could not be read.~%")
        (mv t mach-o state))
       (mach-o (!DATA-common-section-bytes section mach-o)))
    (mv nil mach-o state)))

(define fill-DATA-segment-bytes ((h-size :type (unsigned-byte 64))
                                 (lc-size :type (unsigned-byte 64))
                                 (remaining-file byte-listp)
                                 mach-o state)
  :short "Fill the sections of the @('__DATA') segment into @('mach-o')"
  :guard-hints (("Goal" :in-theory (e/d () (good-mach-o-p))))

  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o)
                           :hints (("Goal" :in-theory (e/d () (good-mach-o-p)))))
               (new-state acl2::state-p :hyp (acl2::state-p state)))
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

;;----------------------------------------------------------------------

(local
 (defthm mach-o-lemma-17
   (implies (good-mach-o-p mach-o)
            (and (good-mach-o-p (!mach-o :mach-o-file-size nil x mach-o))
                 (good-mach-o-p (!mach-o :load-cmds-size nil x mach-o))
                 (good-mach-o-p (!mach-o :mach-o-header-size nil x mach-o))))))

(define populate-mach-o-contents ((file-byte-list byte-listp)
                                  mach-o state)
  :short "Initialize the Mach-O stobj with @('file-byte-list')"
  :guard-hints (("Goal" :do-not-induct t
                 :in-theory
                 (e/d (read-mach_header)
                      (byte-listp
                       unsigned-byte-p
                       nfix fix
                       not natp good-mach-o-p))))
  :returns (mv err
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o)
                           :hints (("Goal" :in-theory (e/d () (good-mach-o-p)))))
               (new-state acl2::state-p :hyp (acl2::state-p state)))

  (b* ((file-size (len file-byte-list))
       (mach-o (!mach-o-file-size file-size mach-o))
       (file-header (take 32 file-byte-list))
       ((when (not (byte-listp file-header)))
        (cw "Header could not be read.~%")
        (mv t mach-o state))

       ((mach-o-header header) (read-mach_header file-header))
       (magic header.magic)
       ((when (and (not (equal magic *MH_MAGIC*))
                   (not (equal magic *MH_CIGAM*))
                   (not (equal magic *MH_MAGIC_64*))
                   (not (equal magic *MH_CIGAM_64*))))
        (cw "Error: Not a Mach-O object file (as suggested by the magic number).~%")
        (mv t mach-o state))
       ((when (not (unsigned-byte-p 64 header.sizeofcmds)))
        (cw "Mach-O File Read Error: Sizeofcmds ~x0 ill-formed~%" header.sizeofcmds)
        (mv t mach-o state))
       (mach-o (!load-cmds-size header.sizeofcmds mach-o))
       (mach-o-header-size
        (if (and (or (equal magic *MH_MAGIC*)
                     (equal magic *MH_CIGAM*))
                 (equal header.reserved nil))
            28
          32))
       (mach-o (!mach-o-header-size mach-o-header-size mach-o))
       (file-byte-list (nthcdr mach-o-header-size file-byte-list))
       (ncmds (nfix header.ncmds))
       ((mv cmds remaining-file mach-o)
        (read-load_commands ncmds file-byte-list nil mach-o))
       (h-size (@mach-o-header-size mach-o))
       (lc-size (@load-cmds-size mach-o))

       ;; TEXT segment
       ((mv flg mach-o state)
        (fill-TEXT-segment-bytes h-size lc-size remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state))

       ;; DATA segment
       ((mv flg mach-o state)
        (fill-DATA-segment-bytes h-size lc-size remaining-file mach-o state))
       ((when flg)
        (mv flg mach-o state)))

    (mv (list 'HEADER header (list 'CMDS cmds))
        mach-o
        state)))

(define populate-mach-o ((filename stringp)
                         mach-o
                         state)
  :short "Initialize the MACH-O stobj with contents of MACH-O binary @('filename')"
  :returns (mv alst
               (new-mach-o good-mach-o-p :hyp (good-mach-o-p mach-o)
                           :hints (("Goal" :in-theory (e/d () (good-mach-o-p)))))
               state)
  (b* (((mv contents state)
        (acl2::read-file-bytes filename state))
       ((unless (byte-listp contents))
        (prog2$
         (raise "Error reading file ~s0!" filename)
         (mv nil mach-o state))))
    (populate-mach-o-contents contents mach-o state)))

;; ======================================================================
