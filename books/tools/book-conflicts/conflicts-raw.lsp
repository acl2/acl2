;;
;; Copyright (C) 2014, David Greve
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2.
;;
(in-package "COMMON-LISP-USER")

(defun analyze-file-list (flist)
  (let ((state acl2::*the-live-state*))
    (progn
      (ignore-errors (acl2::analyze-files flist state))
      (quit 0))))

(defmacro analyzer-command (&rest args)
  `(analyze-file-list '(,@args)))
