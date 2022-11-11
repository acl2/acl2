; Checking whether a string starts with another string
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/prefixp-def" :dir :system)
(local (include-book "kestrel/lists-light/prefixp" :dir :system))

;; Check whether STR starts with PREFIX.
;; TODO: Consider giving this a name that includes 'prefix'
;; TODO: What order should the arguments be in?
(defund string-starts-withp (str prefix)
  (declare (xargs :guard (and (stringp str)
                              (stringp prefix))))
  (let ((strchars (coerce str 'list))
        (prefixchars (coerce prefix 'list)))
    (prefixp prefixchars strchars)))

;; TODO: Better normal form for string length than "len of coerce"?
(defthm string-starts-withp-forward
  (implies (string-starts-withp str prefix)
           (<= (len (coerce prefix 'list))
               (len (coerce str 'list))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable string-starts-withp))))
