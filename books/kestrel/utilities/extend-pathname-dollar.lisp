; An improved version of extend-pathname
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(verify-termination expand-tilde-to-user-home-dir)
;(verify-guards expand-tilde-to-user-home-dir :otf-flg t) ; todo: needs a guard

(include-book "system/extend-pathname" :dir :system) ; for the verify termination

;; (verify-guards merge-using-dot-dot) ; todo

;; Drop-in replacement for extend-pathname that doesn't fail on stuff like
;; (extend-pathname "." "../foo" state).
;; DIR is either a string or a keyword representing a project directory
;; Note: This can add a slash if the filename is a dir.
(defund extend-pathname$ (dir filename state)
  (declare (xargs :guard (and (or (keywordp dir)
                                  (stringp dir))
                              (stringp filename))
                  :stobjs state
                  :verify-guards nil ; todo
                  ))
  (if (keywordp dir)
      (extend-pathname dir filename state)
    ;; canonical-pathname makes the path absolute:
    (extend-pathname (canonical-pathname dir t state) filename state)))

;; ;; TODO: Make these into proper tests:
;; (extend-pathname$ "/home/smith" "foo" state) ; seems to work with or without slash
;; (extend-pathname$ "/home/smith/" "foo" state)
;; (extend-pathname$ "." "foo" state)
;; (extend-pathname$ "./" "foo" state)
;; (extend-pathname$ "~" "foo" state)
;; (extend-pathname$ "~/" "foo" state)
;; (extend-pathname$ ".sys" "foo" state) ; relative pathname, dir must exist
;; (extend-pathname$ ".sys/" "foo" state)
;; (extend-pathname$ ".." "foo" state)
;; (extend-pathname$ "../" "foo" state)
;; (extend-pathname$ :system "foo" state)
;; ;; (extend-pathname$ :cbd "foo" state) ; not allowed

(defund extend-pathnames$ (dir filenames state)
  (declare (xargs :guard (and (or (keywordp dir)
                                  (stringp dir))
                              (string-listp filenames))
                  :stobjs state
                  :verify-guards nil ; todo
                  ))
  (if (endp filenames)
      nil
    (cons (extend-pathname$ dir (first filenames) state)
          (extend-pathnames$ dir (rest filenames) state))))
