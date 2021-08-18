; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun package-name-from-rune-base-symbol (x)
  (declare (xargs :guard (symbolp x)))
  (and (equal (symbol-package-name x)
              "ACL2")
       (let* ((name (symbol-name x))
              (len (length name)))
         (and (> len 8) ; "-PACKAGE" has length 8
              (subseq name 0 (- len 8))))))

(defun book-of-event (name wrld)

; Evaluate (book-of-event NAME (w state)) to get the pathname of the book in
; which the event named NAME is introduced.  If that event exists but is not
; introduced in a book, return :top-level.  If that event doesn't exist, return
; nil.

  (declare (xargs :mode :program
                  :guard (or (symbolp name) (stringp name))))
  (cond
   ((and (symbolp name)
         (getpropc name 'predefined nil wrld))
    :built-in)
   (t
    (let ((ev-wrld (decode-logical-name name wrld)))
      (cond
       (ev-wrld
        (let ((book-path
               (getpropc 'include-book-path 'global-value nil ev-wrld)))
          (cond
           (book-path (car book-path))
           ((and (stringp name)
                 (or (equal name "ACL2-USER") ; defpkgs.lisp
                     (equal name "ACL2-PC") ; proof-builder-pkg.lisp
                     (find-package-entry name *initial-known-package-alist*)))
            :built-in)
           (t :top-level))))
       (t (and (symbolp name)
               (let ((str (package-name-from-rune-base-symbol name)))
                 (and str
                      (book-of-event str wrld))))))))))
