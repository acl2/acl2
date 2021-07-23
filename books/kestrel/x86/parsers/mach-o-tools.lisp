; Tools for processing the alists that represent parsed mach-o files.
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
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

;; Get the first element of LOAD-COMMANDS that has :cmd type CMD-TYPE.
(defun get-mach-o-load-command (cmd-type load-commands)
;  (declare (xargs :guard (true-listp load-commands)))
  (if (endp load-commands)
      (er hard 'get-mach-o-load-command "Can't find a load command of type: ~x0." cmd-type)
    (let* ((load-command (first load-commands))
           (this-cmd-type (acl2::lookup-eq-safe :cmd load-command)))
      (if (eq cmd-type this-cmd-type)
          load-command
        (get-mach-o-load-command cmd-type (rest load-commands))))))

(defun get-mach-o-segment (segname load-commands)
  (if (endp load-commands)
      (er hard 'get-mach-o-segment "Can't find a segment named: ~x0." segname)
    (let* ((load-command (first load-commands))
           (cmd (acl2::lookup-eq-safe :cmd load-command)))
      (if (not (or (eq cmd :LC_SEGMENT)
                   (eq cmd :LC_SEGMENT_64)))
          (get-mach-o-segment segname (rest load-commands))
        (let ((this-name (acl2::lookup-eq-safe :SEGNAME load-command)))
          (if (equal segname this-name)
              load-command
            (get-mach-o-segment segname (rest load-commands))))))))

(defun get-mach-o-section (name sections)
  (if (endp sections)
      (er hard 'get-mach-o-section "Can't find a section named: ~x0." name)
    (let* ((section (first sections))
           (this-name (acl2::lookup-eq-safe :sectname section)))
      (if (equal name this-name)
          section
        (get-mach-o-section name (rest sections))))))


;; Get the code from the __TEXT,__text section
(defund get-mach-o-code (mach-o)
  (acl2::lookup-eq-safe :contents (get-mach-o-section "__text" (acl2::lookup-eq-safe :SECTIONS (get-mach-o-segment "__TEXT" (acl2::lookup-eq-safe :cmds mach-o))))))

;; Get the load address for the code from the __TEXT,__text section
(defund get-mach-o-code-address (mach-o)
  (acl2::lookup-eq-safe :addr (get-mach-o-section "__text" (acl2::lookup-eq-safe :SECTIONS (get-mach-o-segment "__TEXT" (acl2::lookup-eq-safe :cmds mach-o))))))

;move to a more general place (this must exist?)
(defun make-code-alist (addr code)
  (if (endp code)
      nil
    (acons addr (first code)
           (make-code-alist (+ 1 addr) (rest code)))))

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

;; Get the starting address of the subroutine called subroutine-name
;; in the __Text,__text section of, MACH-O, which should be a parsed
;; Mach-O executable.
(defun subroutine-address-mach-o (subroutine-name mach-o)
  (let* ((text-section-number (get-text-section-number-mach-o mach-o))
         (load-commands (acl2::lookup-eq-safe :cmds mach-o))
         (symbol-table-load-command (get-mach-o-load-command :LC_SYMTAB load-commands))
         (symbol-table (lookup-eq-safe :syms symbol-table-load-command))
         (symbol-entry (get-symbol-entry-mach-o subroutine-name text-section-number symbol-table)))
    (if (not symbol-entry)
        (er hard? 'get-start-address "No symbol table entry found for ~x0." subroutine-name)
      (lookup-eq-safe :N-VALUE symbol-entry))))
