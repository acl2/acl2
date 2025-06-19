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

(include-book "parse-mach-o-file") ; todo: reduce

(local (in-theory (disable strip-cars symbol-alistp))) ; prevent induction

(defun mach-o-sectionp (sec)
  (declare (xargs :guard t))
  (symbol-alistp sec))

(defund mach-o-section-listp (sections)
  (declare (xargs :guard t))
  (if (atom sections)
      (null sections)
    (and (mach-o-sectionp (first sections))
         (mach-o-section-listp (rest sections)))))

(defund mach-o-commandp (cmd)
  (declare (xargs :guard t))
  (symbol-alistp cmd))

(defund mach-o-command-listp (cmds)
  (declare (xargs :guard t))
  (if (atom cmds)
      (null cmds)
    (and (mach-o-commandp (first cmds))
         (mach-o-command-listp (rest cmds)))))

;move
(defund parsed-mach-o-p (parsed-mach-o)
  (declare (xargs :guard t))
  (and (symbol-alistp parsed-mach-o)
       (equal (strip-cars parsed-mach-o) '(:magic :header :cmds))
       (let ((magic (lookup-eq :magic parsed-mach-o))
             (header (lookup-eq :header parsed-mach-o))
             (cmds (lookup-eq :cmds parsed-mach-o)))
         (and (or (member-eq magic *32-bit-magic-numbers*)
                  (member-eq magic *64-bit-magic-numbers*))
              (symbol-alistp header) ; todo: strengthen
              (mach-o-command-listp cmds)))))

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

;; Get the code from the __TEXT,__text section
(defund get-mach-o-code (mach-o)
  ;; (declare (xargs :guard (parsed-mach-o-p mach-o)
  ;;                 :guard-hints (("Goal" :in-theory (enable parsed-mach-o-p)))
  ;;                 ))
  ;; todo: what if :contents is (:zero-fill ...)?
  (acl2::lookup-eq-safe :contents (get-mach-o-section "__text" (acl2::lookup-eq-safe :SECTIONS (get-mach-o-segment "__TEXT" (acl2::lookup-eq-safe :cmds mach-o))))))

;; Get the load address for the code from the __TEXT,__text section
(defund get-mach-o-code-address (mach-o)
  (acl2::lookup-eq-safe :addr (get-mach-o-section "__text" (acl2::lookup-eq-safe :SECTIONS (get-mach-o-segment "__TEXT" (acl2::lookup-eq-safe :cmds mach-o))))))


(defun get-all-sections-from-mach-o-load-command (cmd)
  (let ((cmd-name (lookup-eq-safe :cmd cmd)))
    (if (or (eq cmd-name :LC_SEGMENT)
            (eq cmd-name :LC_SEGMENT_64))
        (lookup-eq-safe :sections cmd)
      nil ;can anything else contain sections?
      )))

(defun get-all-sections-from-mach-o-load-commands (cmds)
  (if (endp cmds)
      nil
    (append (get-all-sections-from-mach-o-load-command (first cmds))
            (get-all-sections-from-mach-o-load-commands (rest cmds)))))

;; Get all sections of all segments, in the order they appear in the load commands
(defun get-all-sections-from-mach-o (mach-o)
  (let* ((cmds (lookup-eq :cmds mach-o)))
    (get-all-sections-from-mach-o-load-commands cmds)))

(defun get-section-number-mach-o-aux (segname sectname sections curr)
  (if (endp sections)
      (er hard 'get-section-number-mach-o-aux "Could not find section with segment name ~x0 and section name ~x1" segname sectname)
    (let* ((section (first sections))
           (segname2 (lookup-eq-safe :segname section))
           (sectname2 (lookup-eq-safe :sectname section)))
      (if (and (equal segname2 segname)
               (equal sectname2 sectname))
          curr
        (get-section-number-mach-o-aux segname sectname (rest sections) (+ 1 curr))))))

;; Get the position in the list SECTIONS of the section indicated by
;; SEGNAME and SECTNAME (e.g., "__Text" and "__text"), where the
;; numbering starts at 1.
(defun get-section-number-mach-o (segname sectname sections)
  (get-section-number-mach-o-aux segname sectname sections 1))

;; Get the number of the __TEXT,__text section in a parsed Mach-O
;; file.  Section numbering spans all segments in order of their load
;; commands and starts at 1.
(defun get-text-section-number-mach-o (mach-o)
  (let* ((sections (get-all-sections-from-mach-o mach-o)))
    (get-section-number-mach-o "__TEXT" "__text" sections)))

(defun get-symbol-entry-mach-o (subroutine-name text-section-number symbol-table)
  (if (endp symbol-table)
      nil ;not found
    (let* ((entry (first symbol-table))
           (name (lookup-eq-safe :string entry))
           (n-sect (lookup-eq-safe :n-sect entry)))
      (if (and (equal name subroutine-name)
               (eql n-sect text-section-number))
          entry
        (get-symbol-entry-mach-o subroutine-name text-section-number (rest symbol-table))))))

(defun get-names-from-mach-o-symbol-table (text-section-number symbol-table acc)
  (if (endp symbol-table)
      (reverse acc)
    (let* ((entry (first symbol-table))
           (name (lookup-eq-safe :string entry))
           (n-sect (lookup-eq-safe :n-sect entry)))
      (if (eql n-sect text-section-number)
          (get-names-from-mach-o-symbol-table text-section-number (rest symbol-table) (cons name acc))
        (get-names-from-mach-o-symbol-table text-section-number (rest symbol-table) acc)))))

;; this is for the text section
(defun get-mach-o-symbol-table (mach-o)
  (let* ((load-commands (acl2::lookup-eq-safe :cmds mach-o))
         (symbol-table-load-command (get-mach-o-load-command :LC_SYMTAB load-commands))
         (symbol-table (lookup-eq-safe :syms symbol-table-load-command)))
    symbol-table))

;; Get the starting address of the subroutine called subroutine-name
;; in the __Text,__text section of, MACH-O, which should be a parsed
;; Mach-O executable.
(defun subroutine-address-mach-o (subroutine-name mach-o)
  (let* ((text-section-number (get-text-section-number-mach-o mach-o))
         (symbol-table (get-mach-o-symbol-table mach-o))
         (symbol-entry (get-symbol-entry-mach-o subroutine-name text-section-number symbol-table)))
    (if (not symbol-entry)
        (er hard? 'get-start-address "No symbol table entry found for ~x0." subroutine-name)
      (lookup-eq-safe :N-VALUE symbol-entry))))

;; this is for the text section
(defun get-all-mach-o-symbols (parsed-mach-o)
  (let ((text-section-number (get-text-section-number-mach-o parsed-mach-o)))
    (get-names-from-mach-o-symbol-table text-section-number (get-mach-o-symbol-table parsed-mach-o) nil)))

(defun mach-o-cpu-type (parsed-mach-o)
  (lookup-eq-safe :cputype (lookup-eq-safe :header parsed-mach-o)))

;; Returns the segment, or nil if the segment doesn't exist
(defund maybe-get-mach-o-segment-from-load-commands (segment-name load-commands)
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

;; Returns the segment, or nil if the segment doesn't exist.
(defund maybe-get-mach-o-segment (segment-name parsed-mach-o)
  (declare (xargs :guard (and (stringp segment-name)
                              ;; parsed-mach-o
                              )
                  :verify-guards nil))
  (maybe-get-mach-o-segment-from-load-commands segment-name (acl2::lookup-eq-safe :cmds parsed-mach-o)))

;; Returns the section, or nil if the section doesn't exist.
(defund maybe-get-mach-o-section (name sections)
  (declare (xargs :guard (and (stringp name)
                              (alistp sections))))
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
                              ;; parsed-mach-o
                              )
                  :verify-guards nil))
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
