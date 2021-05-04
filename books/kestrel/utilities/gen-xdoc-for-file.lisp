; A utility for building xdoc by extracting text from .lisp files
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book provides a tool, gen-xdoc-for-file, that generates xdoc topics for
;; the events (defuns, defthms, etc.) in a file by extracting the actual
;; relevant text (the definition and any immediately preceding or following
;; comment lines) from the .lisp file.  Contrast this with the standard
;; approach of extracting the bodies of the events from the ACL2 world and
;; attempting to reformat them for presentation in the doc topic.  Advantages
;; of gen-xdoc-for-file include:
;;
;; 1. Formatting of the definition is preserved.
;;
;; 2. Comments are preserved, including comment lines immediately preceding
;; (and following) the definition and comments inside the definition.  This
;; allows individual parts (subterms of a function body, hyps of a rewrite
;; rule) to be explained.
;;
;; 3. Uses of backquote are preserved, instead of being printed as cons nests.
;;
;; 4. Disabled status (defund vs defun) is preserved.
;;
;; 5. A define is printed as the original define form, not the defun to which
;; it expands.  This can be more readable, in part because define adds some
;; things under the hood (such as binding __function__ to support exceptions).
;;
;; 6. Xdoc can be quickly generated for legacy definitions that are already
;; documented in comments.  One must only supply the names to be documented and
;; their :short descriptions.

;; TODO: Consider deleting :hints and :guard-hints when generating xdoc.

;; TODO: Consider allowing the ITEMS given to have different parents.  For now,
;; one can just call gen-xdoc-for-file more than once, one for each set of
;; parents.

;; TODO: Allow some ITEMS to be combined in the same topic.

(include-book "std/io/read-file-lines-no-newlines" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "kestrel/utilities/strings" :dir :system)

(verify-termination cbd-fn) ;todo: move

(local (in-theory (disable SEARCH-FN)))

(local
 (defthm string-listp-of-rev
   (implies (string-listp x)
            (string-listp (rev x)))))

;; Add lines to ACC until an empty line ("") is found.
(defund get-non-empty-lines (lines acc)
  (declare (xargs :guard (and (string-listp lines)
                              (string-listp acc))))
  (if (endp lines)
      acc
    (let ((line (first lines)))
      (if (equal "" line)
          acc ;; empty line found
        (get-non-empty-lines (rest lines) (cons line acc))))))

(defthm true-listp-of-get-non-empty-lines
  (implies (true-listp acc)
           (true-listp (get-non-empty-lines lines acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable get-non-empty-lines))))

(defthm string-listp-of-get-non-empty-lines
  (implies (and (string-listp lines)
                (string-listp acc))
           (string-listp (get-non-empty-lines lines acc)))
  :hints (("Goal" :in-theory (enable get-non-empty-lines))))

;; Find the block of lines (surrounded by blank lines) that contains the definition of the given name.
(defund get-block-for-name (name-string ;lowercase
                            lines current-block-lines-rev
                            filename ; just for use in error messages
                            )
  (declare (xargs :guard (and (stringp name-string)
                              (string-listp lines)
                              (string-listp current-block-lines-rev)
                              (stringp filename))))
  (if (endp lines)
      (er hard? 'get-block-for-name "No block of lines found for ~s0 in ~s1." name-string filename)
    (let ((line (first lines)))
      (if (equal line "") ;; empty string (line with only a newline) divides blocks
          (get-block-for-name name-string (rest lines) nil filename)
        (let* ((downcase-line (str::downcase-string line)) ;todo: try case-insensitive searches below, but adding :test 'char-equal there required standard chars
               )
          (if (and (search name-string downcase-line) ;; ensure the line contains the name (fail fast if not)
                   ;; TODO: Make these things into a list that can be easily extended:
                   ;; TODO: Consider allowing anything of the form (xxxxx name-string ...), or
                   ;; perhaps anything of the form (defxxxxx name-string ...)
                   (or (search (concatenate 'string "(defun " name-string " ") downcase-line)
                       (search (concatenate 'string "(defund " name-string " ") downcase-line)
                       (search (concatenate 'string "(defmacro " name-string " ") downcase-line)
                       (search (concatenate 'string "(defthm " name-string " ") downcase-line)
                       (search (concatenate 'string "(defthmd " name-string " ") downcase-line)
                       (search (concatenate 'string "(define " name-string " ") downcase-line)))
              ;; This block contains the definition of name, so get the rest of the lines in the block and return:
              (rev (get-non-empty-lines (rest lines) (cons line current-block-lines-rev)))
            ;; This line doesn't contain the definition of name, but it may come later in this block
            (get-block-for-name name-string (rest lines) (cons line current-block-lines-rev) filename)))))))

(defthm string-listp-of-get-block-for-name
  (implies (and (stringp name-string)
                (string-listp lines)
                (string-listp current-block-lines-rev))
           (string-listp (get-block-for-name name-string lines current-block-lines-rev filename)))
  :hints (("Goal" :in-theory (enable get-block-for-name))))

(defun append-string-lines (lines)
  (declare (xargs :guard (string-listp lines)))
  (if (endp lines)
      ""
    (concatenate 'string
                 (first lines)
                 (newline-string)
                 (append-string-lines (rest lines)))))

(defun gen-xdoc-form-for-item (item lines parents
                                    filename ; just for use in error messages
                                    )
  (declare (xargs :guard (and (true-listp item)
                              (eql (len item) 2)
                              ;; (doubletp item)
                              (string-listp lines)
                              (symbol-listp parents)
                              (stringp filename))))
  (let ((name (first item))
        (short (second item)))
    (if (not (symbolp name))
        (er hard? 'gen-xdoc-form-for-item "Bad name: ~x0." name)
      (if (not (stringp short))
          (er hard? 'gen-xdoc-form-for-item "Bad short description, ~x0, for ~x1." short name)
        (let ((block (get-block-for-name (str::downcase-string (symbol-name name)) lines nil filename)))
          `(defxdoc ,name
             :parents ,parents
             :short ,short
             :long
             ,(concatenate 'string "@({"
                           (append-string-lines block)
                           "})")))))))

(defun gen-xdoc-forms-for-items (items lines parents
                                       filename ; just for use in error messages
                                       )
  (declare (xargs :guard (and (doublet-listp items)
                              (string-listp lines)
                              (symbol-listp parents)
                              (stringp filename))))
  (if (endp items)
      nil
    (cons (gen-xdoc-form-for-item (first items) lines parents filename)
          (gen-xdoc-forms-for-items (rest items) lines parents filename))))

;; Returns (mv erp form state).
(defun gen-xdoc-for-file-fn (filename
                             items ;; todo: allow this to be :all
                             parents
                             state
                             )
  (declare (xargs :guard (and (stringp filename)
                              (doublet-listp items)
                              (symbol-listp parents))
                  :verify-guards nil ;because of cbd-fn
                  :stobjs state))
  (b* ((cbd (cbd-fn state)) ;should end in slash
       (full-filename (concatenate 'string cbd filename))
       ((mv lines state)
        (read-file-lines-no-newlines full-filename state))
       ((when (stringp lines)) ;indicates an error
        (mv t                  ;erp
            (er hard? 'gen-xdoc-for-file "Error reading file ~x0." full-filename)
            state)))
    (mv nil ;no error
        `(progn ,@(gen-xdoc-forms-for-items items lines parents full-filename))
        state)))

;; Generate xdoc topics for the given ITEMS, each of which is a doublet of a
;; name and its :short xdoc string.  The body of each generated xdoc topic will
;; contain the block of lines (demarcated by empty lines) from the given
;; FILENAME that defines the given name.  Each name must be defined in a defun,
;; defund, defmacro, defthm, defthmd, or define.
(defmacro gen-xdoc-for-file (filename
                             items
                             parents)
  `(make-event (gen-xdoc-for-file-fn ',filename ',items ',parents state)))

;; Use the utility to generate xdoc for itself:
(gen-xdoc-for-file "gen-xdoc-for-file.lisp"
                   ((gen-xdoc-for-file "Generate xdoc using textual definitions from a .lisp file."))
                   (xdoc))
