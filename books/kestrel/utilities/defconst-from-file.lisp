; A tool to read an object from a file and turn it into a defconst.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-object-from-file" :dir :system)

;; Returns (mv erp event state).
(defun defconst-from-file-fn (defconst-name filename package state)
  (declare (xargs :guard (and (symbolp defconst-name)
                              (stringp filename)
                              (stringp package))
                  :mode :program
                  :stobjs state))
  (let ((original-package (current-package state)))
    (er-progn (in-package-fn package state) ; switch to the given package before reading
              (er-let* ((object (read-object-from-file filename state)))
                (er-progn (in-package-fn original-package state) ; switch back to original package (could perhaps skip this)
                          (mv nil ;; no error
                              `(defconst ,defconst-name ',object)
                              state))))))

;; Creates a defconst called DEFCONST-NAME representing the form read from
;; FILENAME.  Symbols read from the file are interned into the package whose
;; name is supplied as the :PACKAGE argument, or the "ACL2" package by default.
(defmacro defconst-from-file (defconst-name filename &key
                               (package '"ACL2") ; package to use for symbols read from file
                               )
  `(make-event (defconst-from-file-fn ',defconst-name ',filename ',package state)))
