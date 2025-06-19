; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Call Common Lisp directory function
; and convert returned pathnames to namestrings.

(defun cl-directory (file-pattern)
  (let ((pathnames (directory file-pattern)))
    (mapcar #'namestring pathnames)))

(defun cl-directory-relative (root-dir rest-of-file-pattern)
  (let ((filenames (cl-directory (string-append
                                  root-dir
                                  rest-of-file-pattern)))
        (root-dir-len (length root-dir)))
    (mapcar #'(lambda (f)
                (subseq f root-dir-len))
            filenames)))
