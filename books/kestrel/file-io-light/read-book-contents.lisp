; Reading the objects in a book
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also read-objects-from-book, which this calls.

(include-book "read-objects-from-book")
(include-book "kestrel/utilities/maybe-add-dot-lisp-extension" :dir :system)
(include-book "kestrel/utilities/extend-pathname-dollar" :dir :system)

;; Returns (mv erp forms full-book-path state).
;; Adds the .lisp extension, if needed.
(defund read-book-contents (bookname
                            dir ; todo: allow keyword dirs
                            state)
  (declare (xargs :guard (and (stringp bookname)
                              (or (eq :cbd dir)
                                  (stringp dir)))
                  :mode :program ; todo
                  :stobjs state))
  (let* ((file-name (maybe-add-dot-lisp-extension bookname))
         (full-book-path (extend-pathname$ (if (eq dir :cbd) "." dir) file-name state)))
    (mv-let (existsp state)
      (file-write-date$ full-book-path state)
      (if (not existsp)
          (prog2$ (er hard? 'read-book-contents "~s0 does not exist." full-book-path)
                  (mv :file-does-not-exist nil full-book-path state))
        (mv-let (erp events state)
          (read-objects-from-book full-book-path state)
          (mv erp events full-book-path state))))))
