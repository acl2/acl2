; Syntactic functions for Axe R1CS prover
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; TODO: Switch package to ACL2?  These are not r1cs-specific.

(include-book "kestrel/crypto/r1cs/portcullis" :dir :system)
(include-book "kestrel/axe/dag-arrays" :dir :system)

(defun acl2::var-less-than-unquoted-keyp (var-darg key-darg acl2::dag-array)
  (declare (xargs :guard (and (or (acl2::myquotep var-darg)
                                  (and (natp var-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 var-darg))))
                              (or (acl2::myquotep key-darg)
                                  (and (natp key-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 key-darg)))))))
  (and (consp key-darg) ;checks for quotep
       (let ((unquoted-key (unquote key-darg)))
         (and (symbolp unquoted-key)
              (natp var-darg)
              (let ((var-expr (aref1 'acl2::dag-array acl2::dag-array var-darg)))
                (and (symbolp var-expr)
                     (symbol< var-expr unquoted-key)))))))

(defun acl2::var-not-less-than-unquoted-keyp (var-darg key-darg acl2::dag-array)
  (declare (xargs :guard (and (or (acl2::myquotep var-darg)
                                  (and (natp var-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 var-darg))))
                              (or (acl2::myquotep key-darg)
                                  (and (natp key-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 key-darg)))))))
  (and (consp key-darg) ;checks for quotep
       (let ((unquoted-key (unquote key-darg)))
         (and (symbolp unquoted-key)
              (natp var-darg)
              (let ((var-expr (aref1 'acl2::dag-array acl2::dag-array var-darg)))
                (and (symbolp var-expr)
                     (not (symbol< var-expr unquoted-key))))))))
