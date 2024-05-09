; A utiliy to split a path into a dir and a filename
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in split-path-tests.lisp.

(include-book "kestrel/strings-light/split-string-last" :dir :system)

;; Splits a file path into a directory and filename.
;; Returns (mv dir filename) where DIR has no trailing slash.
(defund split-path (path)
  (declare (xargs :guard (stringp path)))
  (mv-let (foundp dir filename)
    (split-string-last path #\/)
    (if (not foundp)
        ;; No slash, so the whole thing is the filename, and the directory is ".":
        (mv "." path)
      (mv dir filename))))

;; no trailing slash
(defund dir-of-path (path)
  (declare (xargs :guard (stringp path)))
  (mv-let (dir filename)
    (split-path path)
    (declare (ignore filename))
    dir))
