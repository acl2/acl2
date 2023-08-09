; An improved version of extend-pathname
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(verify-termination expand-tilde-to-user-home-dir)
;(verify-guards expand-tilde-to-user-home-dir :otf-flg t) ; todo: needs a guard
;(verify-termination merge-using-dot-dot) ;todo
;(verify-termination our-merge-pathnames)
;(verify-termination extend-pathname+)
;(verify-termination extend-pathname)

;; Drop-in replacement for extend-pathname that doesn't fail on stuff like
;; (extend-pathname "." "../foo" state).
;; DIR is either a string or a keyword representing a project directory
;; Note: This can add a slash if the filename is a dir.
;move
(defund extend-pathname$ (dir filename state)
  (declare (xargs :guard (or (keywordp dir)
                             (stringp dir))
                  :stobjs state
                  :mode :program))
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
