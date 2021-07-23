; Recognize a true list of bytes
;
; Copyright (C) 2020-2021 Kestrel Institute
; The definition of byte-listp is in books/kestrel/fty/byte-list.lisp.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The purpose of this book is to provide byte-listp without bringing
;; in lots of other machinery.

(include-book "kestrel/bv/bytep" :dir :system)

;; Matches what's in books/kestrel/fty
(defun byte-listp (x)
  (declare (xargs :guard t
                  :measure (acl2-count x)))
  (let ((__function__ 'byte-listp))
    (declare (ignorable __function__))
    (if (atom x)
        (eq x nil)
      (and (bytep (car x))
           (byte-listp (cdr x))))))
