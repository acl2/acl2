; Checking whether a string ends with another string
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/prefixp-def" :dir :system)

;; See also [books]/std/strings/suffixp.lisp but that brings in many books.

;; Check whether STR ends with SUFFIX.
;; TODO: Consider giving this a name that includes 'suffix'
;; TODO: What order should the arguments be in?
;; TODO: Define an analogous operation on lists and call it here?
(defund string-ends-inp (str suffix)
  (declare (xargs :guard (and (stringp str)
                              (stringp suffix))))
  (let ((strchars (coerce str 'list))
        (suffixchars (coerce suffix 'list)))
    (prefixp (reverse suffixchars) (reverse strchars))))

;; (string-ends-inp "foo.cert" ".cert")
;; (string-ends-inp ".cert" ".cert")
;; (not (string-ends-inp "rt" ".cert"))
;; (not (string-ends-inp "foo.bert" ".cert"))
;; (not (string-ends-inp "foo" ".cert"))
