; Tools for processing the alists that represent parsed mach-o files.
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Should these be in the x86isa package?

;; TODO: Add guards (will require defining what a well-formed parsed mach-o looks like)

(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/memory/memory-regions" :dir :system)
(include-book "kestrel/lists-light/repeat-def" :dir :system)
(include-book "parse-mach-o-file") ; todo: reduce?
(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))
(local (include-book "kestrel/bv-lists/byte-listp2" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/repeat" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (in-theory (disable strip-cars symbol-alistp ; prevent induction
                           natp)))

(defund mach-o-sectionp (sec)
  (declare (xargs :guard t))
  (symbol-alistp sec))

(defund mach-o-section-listp (sections)
  (declare (xargs :guard t))
  (if (atom sections)
      (null sections)
    (and (mach-o-sectionp (first sections))
         (mach-o-section-listp (rest sections)))))

(local
  (defthm true-listp-when-mach-o-section-listp
    (implies (mach-o-section-listp sections)
             (true-listp sections))
    :hints (("Goal" :in-theory (enable mach-o-section-listp)))))

(defthm mach-o-section-listp-of-append
  (implies (and (mach-o-section-listp secs1)
                (mach-o-section-listp secs2))
           (mach-o-section-listp (append secs1 secs2)))
  :hints (("Goal" :in-theory (enable mach-o-section-listp))))

(defund mach-o-commandp (cmd)
  (declare (xargs :guard t))
  (and (symbol-alistp cmd)
       (mach-o-section-listp (lookup-equal :sections cmd))))

(local
  (defthm mach-o-section-listp-when-mach-o-commandp
    (implies (mach-o-commandp cmd)
             (mach-o-section-listp (lookup-equal :sections cmd)))
    :hints (("Goal" :in-theory (enable mach-o-commandp)))))

(local
  (defthm alistp-when-mach-o-commandp
    (implies (mach-o-commandp cmd)
             (alistp cmd))
    :hints (("Goal" :in-theory (enable mach-o-commandp)))))

(defund mach-o-command-listp (cmds)
  (declare (xargs :guard t))
  (if (atom cmds)
      (null cmds)
    (and (mach-o-commandp (first cmds))
         (mach-o-command-listp (rest cmds)))))

;move
(defun mach-o-symbol-table-entryp (entry)
  (declare (xargs :guard t))
  (symbol-alistp entry))

(local
  (defthm alistp-when-mach-o-symbol-table-entryp
    (implies (mach-o-symbol-table-entryp entry)
             (alistp entry))
    :hints (("Goal" :in-theory (enable mach-o-symbol-table-entryp)))))

;move
(defund mach-o-symbol-tablep (entriess)
  (declare (xargs :guard t))
  (if (atom entriess)
      (null entriess)
    (and (mach-o-symbol-table-entryp (first entriess))
         (mach-o-symbol-tablep (rest entriess)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets the first element of LOAD-COMMANDS that has :cmd type CMD-TYPE.
;; Returns a load-command, or throws an error
(defund get-mach-o-load-command (cmd-type load-commands)
  (declare (xargs :guard (and (symbolp cmd-type)
                              (mach-o-command-listp load-commands))
                  :guard-hints (("Goal" :in-theory (enable mach-o-command-listp)))
                  ))
  (if (endp load-commands)
      (er hard? 'get-mach-o-load-command "Can't find a load command of type: ~x0." cmd-type)
    (let* ((load-command (first load-commands))
           (this-cmd-type (acl2::lookup-eq-safe :cmd load-command)))
      (if (eq cmd-type this-cmd-type)
          load-command
        (get-mach-o-load-command cmd-type (rest load-commands))))))

(defopeners get-mach-o-load-command) ;drop?

(defthm mach-o-commandp-of-get-mach-o-load-command
  (implies (and (symbolp cmd-type)
                (mach-o-command-listp load-commands))
           (mach-o-commandp (get-mach-o-load-command cmd-type load-commands)))
  :hints (("Goal" :in-theory (enable get-mach-o-load-command
                                     mach-o-command-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
(defund parsed-mach-o-p (parsed-mach-o)
  (declare (xargs :guard t))
  (and (symbol-alistp parsed-mach-o)
       (equal (strip-cars parsed-mach-o) '(:magic :header :cmds :bytes))
       (let ((magic (lookup-eq :magic parsed-mach-o))
             (header (lookup-eq :header parsed-mach-o))
             (cmds (lookup-eq :cmds parsed-mach-o))
             (bytes (lookup-eq :bytes parsed-mach-o)))
         (and (or (member-eq magic *32-bit-magic-numbers*)
                  (member-eq magic *64-bit-magic-numbers*))
              (symbol-alistp header) ; todo: strengthen
              (mach-o-command-listp cmds)
              (mach-o-symbol-tablep (lookup-equal :syms (get-mach-o-load-command :lc_symtab cmds)))
              (byte-listp bytes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets the first element of LOAD-COMMANDS that has has command :LC_SEGMENT or
;; :LC_SEGMENT_64 and that has :segname SEGNAME.
;; Returns a load-command, or throws an error
(defund get-mach-o-segment (segname load-commands)
  (declare (xargs :guard (and (stringp segname)
                              (mach-o-command-listp load-commands))
                  :guard-hints (("Goal" :in-theory (enable mach-o-command-listp)))))
  (if (endp load-commands)
      (er hard? 'get-mach-o-segment "Can't find a segment named: ~x0." segname)
    (let* ((load-command (first load-commands))
           (cmd (acl2::lookup-eq-safe :cmd load-command)))
      (if (not (or (eq cmd :lc_segment)
                   (eq cmd :lc_segment_64)))
          (get-mach-o-segment segname (rest load-commands))
        (let ((this-name (acl2::lookup-eq-safe :segname load-command)))
          (if (equal segname this-name)
              load-command
            (get-mach-o-segment segname (rest load-commands))))))))

(defopeners get-mach-o-segment)

(defthm mach-o-commandp-of-get-mach-o-segment
  (implies (mach-o-command-listp load-commands)
           (mach-o-commandp (get-mach-o-segment segname load-commands)))
  :hints (("Goal" :in-theory (enable mach-o-command-listp
                                     get-mach-o-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a section, or throws an error.
(defund get-mach-o-section (name sections)
  (declare (xargs :guard (and (stringp name)
                              (mach-o-section-listp sections))
                  :guard-hints (("Goal" :in-theory (enable mach-o-section-listp)))))
  (if (endp sections)
      (er hard? 'get-mach-o-section "Can't find a section named: ~x0." name)
    (let* ((section (first sections))
           (this-name (acl2::lookup-eq-safe :sectname section)))
      (if (equal name this-name)
          section
        (get-mach-o-section name (rest sections))))))

(defopeners get-mach-o-section)

(defthm mach-o-sectionp-of-get-mach-o-section
  (implies (mach-o-section-listp sections)
           (mach-o-sectionp (get-mach-o-section name sections)))
  :hints (("Goal" :in-theory (enable mach-o-section-listp
                                     get-mach-o-section))))

(local
  (defthm alistp-when-mach-o-sectionp
    (implies (mach-o-sectionp sec)
             (alistp sec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Get the code from the __TEXT,__text section
;; todo: return an error?
(defund get-mach-o-code (parsed-mach-o)
  (declare (xargs :guard (parsed-mach-o-p parsed-mach-o)
                  :guard-hints (("Goal" :in-theory (enable parsed-mach-o-p)))))
  ;; todo: what if :contents is (:zero-fill ...)?
  (acl2::lookup-eq-safe :contents (get-mach-o-section "__text" (acl2::lookup-eq-safe :SECTIONS (get-mach-o-segment "__TEXT" (acl2::lookup-eq-safe :cmds parsed-mach-o))))))

;; Get the load address for the code from the __TEXT,__text section
(defund get-mach-o-code-address (parsed-mach-o)
  (declare (xargs :guard (parsed-mach-o-p parsed-mach-o)
                  :guard-hints (("Goal" :in-theory (enable parsed-mach-o-p)))))
  (acl2::lookup-eq-safe :addr (get-mach-o-section "__text" (acl2::lookup-eq-safe :SECTIONS (get-mach-o-segment "__TEXT" (acl2::lookup-eq-safe :cmds parsed-mach-o))))))

(defun get-all-sections-from-mach-o-load-command (cmd)
  (declare (xargs :guard (mach-o-commandp cmd)))
  (let ((cmd-name (lookup-eq-safe :cmd cmd)))
    (if (or (eq cmd-name :LC_SEGMENT)
            (eq cmd-name :LC_SEGMENT_64))
        (lookup-eq-safe :sections cmd)
      nil ;can anything else contain sections?
      )))

(defun get-all-sections-from-mach-o-load-commands (cmds)
  (declare (xargs :guard (mach-o-command-listp cmds)
                  :guard-hints (("Goal" :in-theory (enable mach-o-command-listp mach-o-commandp)))))
  (if (endp cmds)
      nil
    (append (get-all-sections-from-mach-o-load-command (first cmds))
            (get-all-sections-from-mach-o-load-commands (rest cmds)))))

(local
  (defthm mach-o-section-listp-of-get-all-sections-from-mach-o-load-commands
    (implies (mach-o-command-listp cmds)
             (mach-o-section-listp (get-all-sections-from-mach-o-load-commands cmds)))
    :hints (("Goal" :in-theory (enable get-all-sections-from-mach-o-load-commands
                                     ;mach-o-section-listp
                                       mach-o-command-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Get all sections of all segments, in the order they appear in the load commands
(defund get-all-sections-from-mach-o (parsed-mach-o)
  (declare (xargs :guard (parsed-mach-o-p parsed-mach-o)
                  :guard-hints (("Goal" :in-theory (enable parsed-mach-o-p)))))
  (let* ((cmds (lookup-eq :cmds parsed-mach-o)))
    (get-all-sections-from-mach-o-load-commands cmds)))

(defthm mach-o-section-listp-of-get-all-sections-from-mach-o
  (implies (parsed-mach-o-p parsed-mach-o)
           (mach-o-section-listp (get-all-sections-from-mach-o parsed-mach-o)))
  :hints (("Goal" :in-theory (enable get-all-sections-from-mach-o
                                     parsed-mach-o-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-section-number-mach-o-aux (segname sectname sections curr)
  (declare (xargs :guard (and (stringp segname)
                              (stringp sectname)
                              (mach-o-section-listp sections)
                              (natp curr))
                  :guard-hints (("Goal" :in-theory (enable mach-o-section-listp)))))
  (if (endp sections)
      (er hard? 'get-section-number-mach-o-aux "Could not find section with segment name ~x0 and section name ~x1" segname sectname)
    (let* ((section (first sections))
           (segname2 (lookup-eq-safe :segname section))
           (sectname2 (lookup-eq-safe :sectname section)))
      (if (and (equal segname2 segname)
               (equal sectname2 sectname))
          curr
        (get-section-number-mach-o-aux segname sectname (rest sections) (+ 1 curr))))))

(local
  (defthm natp-of-get-section-number-mach-o-aux-iff
    (implies (and (parsed-mach-o-p parsed-mach-o)
                  (natp curr))
             (iff (natp (get-section-number-mach-o-aux segname sectname sections curr))
                  (get-section-number-mach-o-aux segname sectname sections curr)))
    :hints (("Goal" :in-theory (enable get-section-number-mach-o-aux)))))

;; Get the position in the list SECTIONS of the section indicated by
;; SEGNAME and SECTNAME (e.g., "__Text" and "__text"), where the
;; numbering starts at 1.
(defund get-section-number-mach-o (segname sectname sections)
  (declare (xargs :guard (and (stringp segname)
                              (stringp sectname)
                              (mach-o-section-listp sections))
                  :guard-hints (("Goal" :in-theory (enable mach-o-section-listp)))))
  (get-section-number-mach-o-aux segname sectname sections 1))

(local
  (defthm natp-of-get-section-number-mach-o-iff
    (implies (parsed-mach-o-p parsed-mach-o)
             (iff (natp (get-section-number-mach-o segname sectname sections))
                  (get-section-number-mach-o segname sectname sections)))
    :hints (("Goal" :in-theory (enable get-section-number-mach-o)))))

;; Get the number of the __TEXT,__text section in a parsed Mach-O
;; file.  Section numbering spans all segments in order of their load
;; commands and starts at 1.
(defund get-text-section-number-mach-o (parsed-mach-o)
  (declare (xargs :guard (parsed-mach-o-p parsed-mach-o)))
  (let* ((sections (get-all-sections-from-mach-o parsed-mach-o)))
    (get-section-number-mach-o "__TEXT" "__text" sections)))

(local
  (defthm natp-of-get-text-section-number-mach-o-off
    (implies (parsed-mach-o-p parsed-mach-o)
             (iff (natp (get-text-section-number-mach-o parsed-mach-o))
                  (get-text-section-number-mach-o parsed-mach-o)))
    :hints (("Goal" :in-theory (enable get-text-section-number-mach-o)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-symbol-table-entry-mach-o (subroutine-name text-section-number symbol-table)
  (declare (xargs :guard (and (stringp subroutine-name)
                              (natp text-section-number)
                              (mach-o-symbol-tablep symbol-table))
                  :guard-hints (("Goal" :in-theory (enable mach-o-symbol-tablep)))))
  (if (endp symbol-table)
      nil ;not found
    (let* ((entry (first symbol-table))
           (name (lookup-eq-safe :string entry))
           (n-sect (lookup-eq-safe :n-sect entry)))
      (if (and (equal name subroutine-name)
               (eql n-sect text-section-number))
          entry
        (get-symbol-table-entry-mach-o subroutine-name text-section-number (rest symbol-table))))))

(defthm mach-o-symbol-table-entryp-of-get-symbol-table-entry-mach-o
  (implies (and (get-symbol-table-entry-mach-o subroutine-name text-section-number symbol-table) ; found
                (mach-o-symbol-tablep symbol-table))
           (mach-o-symbol-table-entryp (get-symbol-table-entry-mach-o subroutine-name text-section-number symbol-table)))
  :hints (("Goal" :in-theory (enable get-symbol-table-entry-mach-o mach-o-symbol-tablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun get-names-from-mach-o-symbol-table (text-section-number symbol-table acc)
  (declare (xargs :guard (and (natp text-section-number)
                              (mach-o-symbol-tablep symbol-table)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable mach-o-symbol-tablep)))))
  (if (endp symbol-table)
      (reverse acc)
    (let* ((entry (first symbol-table))
           (name (lookup-eq-safe :string entry))
           (n-sect (lookup-eq-safe :n-sect entry)))
      (if (eql n-sect text-section-number)
          (get-names-from-mach-o-symbol-table text-section-number (rest symbol-table) (cons name acc))
        (get-names-from-mach-o-symbol-table text-section-number (rest symbol-table) acc)))))

;; this is for the text section
(defund get-mach-o-symbol-table (parsed-mach-o)
  (declare (xargs :guard (parsed-mach-o-p parsed-mach-o)
                  :guard-hints (("Goal" :in-theory (enable parsed-mach-o-p)))))
  (let* ((load-commands (acl2::lookup-eq-safe :cmds parsed-mach-o))
         (symbol-table-load-command (get-mach-o-load-command :LC_SYMTAB load-commands))
         (symbol-table (lookup-eq-safe :syms symbol-table-load-command)))
    symbol-table))

(local
  (defthm mach-o-symbol-tablep-of-get-mach-o-symbol-table
    (implies (parsed-mach-o-p parsed-mach-o)
             (mach-o-symbol-tablep (get-mach-o-symbol-table parsed-mach-o)))
    :hints (("Goal" :in-theory (enable parsed-mach-o-p get-mach-o-symbol-table)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Get the starting address of the subroutine called subroutine-name
;; in the __Text,__text section of, MACH-O, which should be a parsed
;; Mach-O executable.
(defund subroutine-address-mach-o (subroutine-name parsed-mach-o)
  (declare (xargs :guard (and (stringp subroutine-name)
                              (parsed-mach-o-p parsed-mach-o))
                  :guard-hints (("Goal" :in-theory (e/d (parsed-mach-o-p) (natp))))))
  (let ((text-section-number (get-text-section-number-mach-o parsed-mach-o)))
    (if (not (natp text-section-number))
        (er hard? 'subroutine-address-mach-o "No text section found.")
      (let* ((symbol-table (get-mach-o-symbol-table parsed-mach-o))
             (symbol-entry (get-symbol-table-entry-mach-o subroutine-name text-section-number symbol-table)))
        (if (not symbol-entry)
            (er hard? 'subroutine-address-mach-o "No symbol table entry found for ~x0." subroutine-name)
          (lookup-eq-safe :N-VALUE symbol-entry))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this is for the text section
(defun get-all-mach-o-symbols (parsed-mach-o)
  (declare (xargs :guard (parsed-mach-o-p parsed-mach-o)
                  :guard-hints (("Goal" :in-theory (disable natp)))))
  (let ((text-section-number (get-text-section-number-mach-o parsed-mach-o)))
    (if (not text-section-number)
        (er hard? 'get-all-mach-o-symbols "Can't find text section number.")
    (get-names-from-mach-o-symbol-table text-section-number (get-mach-o-symbol-table parsed-mach-o) nil))))

(defun mach-o-cpu-type (parsed-mach-o)
  (declare (xargs :guard (parsed-mach-o-p parsed-mach-o)
                  :guard-hints (("Goal" :in-theory (enable parsed-mach-o-p)))))
  (lookup-eq-safe :cputype (lookup-eq-safe :header parsed-mach-o)))

;; Returns the segment, or nil if the segment doesn't exist
(defund maybe-get-mach-o-segment-from-load-commands (segment-name load-commands)
  (declare (xargs :guard (and (stringp segment-name)
                              (mach-o-command-listp load-commands))
                  :guard-hints (("Goal" :in-theory (enable mach-o-command-listp)))))
  (if (endp load-commands)
      nil
    (let* ((load-command (first load-commands))
           (cmd (acl2::lookup-eq-safe :cmd load-command)))
      (if (not (or (eq cmd :LC_SEGMENT)
                   (eq cmd :LC_SEGMENT_64)))
          (maybe-get-mach-o-segment-from-load-commands segment-name (rest load-commands))
        (let ((this-name (acl2::lookup-eq-safe :SEGNAME load-command)))
          (if (equal segment-name this-name)
              load-command
            (maybe-get-mach-o-segment-from-load-commands segment-name (rest load-commands))))))))

(defthm mach-o-commandp-of-maybe-get-mach-o-segment-from-load-commands
  (implies (and (maybe-get-mach-o-segment-from-load-commands segment-name load-commands) ; found
                (mach-o-command-listp load-commands))
           (mach-o-commandp (maybe-get-mach-o-segment-from-load-commands segment-name load-commands)))
  :hints (("Goal" :in-theory (enable maybe-get-mach-o-segment-from-load-commands
                                     mach-o-command-listp))))


;; Returns the segment, or nil if the segment doesn't exist.
(defund maybe-get-mach-o-segment (segment-name parsed-mach-o)
  (declare (xargs :guard (and (stringp segment-name)
                              (parsed-mach-o-p parsed-mach-o))
                  :guard-hints (("Goal" :in-theory (enable parsed-mach-o-p)))))
  (maybe-get-mach-o-segment-from-load-commands segment-name (acl2::lookup-eq-safe :cmds parsed-mach-o)))

(defthm mach-o-commandp-of-maybe-get-mach-o-segment
  (implies (and (maybe-get-mach-o-segment segment-name parsed-mach-o) ; found
                (parsed-mach-o-p parsed-mach-o))
           (mach-o-commandp (maybe-get-mach-o-segment segment-name parsed-mach-o)))
  :hints (("Goal" :in-theory (enable maybe-get-mach-o-segment
                                     parsed-mach-o-p))))

;; Returns the section, or nil if the section doesn't exist.
(defund maybe-get-mach-o-section (name sections)
  (declare (xargs :guard (and (stringp name)
                              (mach-o-section-listp sections))
                  :guard-hints (("Goal" :in-theory (enable mach-o-section-listp)))))
  (if (endp sections)
      nil
    (let* ((section (first sections)))
      (if (not (alistp section))
          (er hard? 'maybe-get-mach-o-section "Ill-formed section: ~x0." section)
        (if (equal name (acl2::lookup-eq-safe :sectname section))
            section
          (maybe-get-mach-o-section name (rest sections)))))))

(defund mach-o-section-presentp (segment-name section-name parsed-mach-o)
  (declare (xargs :guard (and (stringp segment-name)
                              (stringp section-name)
                              (parsed-mach-o-p parsed-mach-o))))
  (let ((seg (maybe-get-mach-o-segment segment-name parsed-mach-o)))
    (and seg
         (if (maybe-get-mach-o-section section-name (acl2::lookup-eq-safe :sections seg))
             t
           nil))))

(def-constant-opener maybe-get-mach-o-segment-from-load-commands)
(def-constant-opener maybe-get-mach-o-segment)
(def-constant-opener maybe-get-mach-o-section)
(def-constant-opener mach-o-section-presentp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move to a more general place (this must exist?)
(defun make-code-alist (addr code)
  (if (endp code)
      nil
    (acons addr (first code)
           (make-code-alist (+ 1 addr) (rest code)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun macho64-regions-to-load-aux (commands all-bytes-len all-bytes acc)
  (declare (xargs :guard (and (acl2::mach-o-command-listp commands)
                              (acl2::byte-listp all-bytes)
                              (equal all-bytes-len (len all-bytes))
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::mach-o-command-listp
                                                           acl2::mach-o-commandp)))))
  (if (endp commands)
      (mv nil (reverse acc))
    (let* ((command (first commands))
           (cmd-type (lookup-eq :cmd command)))
      (if (not (member-eq cmd-type '(:LC_SEGMENT :LC_SEGMENT_64)))
          ;; not a load command, so skip:
          (macho64-regions-to-load-aux (rest commands) all-bytes-len all-bytes acc)
        (b* ((vaddr (lookup-eq :vmaddr command)) ; var names here match what we do for ELF
             (memsz (lookup-eq :vmsize command))
             (offset (lookup-eq :fileoff command))
             (filesz (lookup-eq :filesize command))
             ((when (not (and (natp offset)
                              (natp filesz)
                              (natp vaddr)
                              (natp memsz)
                              ;; The file size can't be larger than the memory size:
                              (<= filesz memsz))))
              (er hard? 'macho64-regions-to-load-aux "Bad load command: vaddr=~x0, memsz=~x1, offset=~x2, filesz=~x3." vaddr memsz offset filesz)
              (mv :bad-load-command nil))
             (last-byte-num (+ -1 offset filesz))
             ((when (not (< last-byte-num all-bytes-len)))
              (mv :not-enough-bytes nil))
             ;; If the file size is smaller than the memory size, we fill with zeros (todo: what if there are too many?):
             (numzeros (- memsz filesz))
             ((when (> numzeros 10000)) ; allows padding with zeros up a multiple of 4k
              (cw "Too many zeros (~x0)!  Skipping this segment!~%" numzeros) ; ttodo!
              (macho64-regions-to-load-aux (rest commands) all-bytes-len all-bytes acc))
             (bytes (take filesz (nthcdr offset all-bytes)))
             ;; Zero bytes at the end of the segment may not be stored in the file:
             (bytes (if (posp numzeros)
                        (append bytes (acl2::repeat numzeros 0)) ; optimize?
                      bytes)))
          (macho64-regions-to-load-aux (rest commands)
                                       all-bytes-len all-bytes
                                       (cons (list memsz vaddr bytes)
                                             acc)))))))

(local
  (defthm memory-regionsp-of-mv-nth-1-of-macho64-regions-to-load-aux
    (implies (and (x::memory-regionsp acc)
                  (acl2::byte-listp all-bytes)
                  (equal all-bytes-len (len all-bytes)))
             (x::memory-regionsp (mv-nth 1 (macho64-regions-to-load-aux command all-bytes-len all-bytes acc))))
    :hints (("Goal" :in-theory (enable macho64-regions-to-load-aux x::memory-regionsp x::memory-regionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp regions).
(defund macho64-regions-to-load (parsed-macho)
  (declare (xargs :guard (acl2::parsed-mach-o-p parsed-macho)
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-mach-o-p)))))
  (b* ((commands (lookup-eq :cmds parsed-macho))
       (all-bytes (lookup-eq :bytes parsed-macho)))
    (macho64-regions-to-load-aux commands (len all-bytes) all-bytes nil)))

(defthm memory-regionsp-of-mv-nth-1-of-macho64-regions-to-load
  (implies (acl2::parsed-mach-o-p parsed-macho)
           (x::memory-regionsp (mv-nth 1 (macho64-regions-to-load parsed-macho))))
  :hints (("Goal" :in-theory (enable macho64-regions-to-load acl2::parsed-mach-o-p))))
