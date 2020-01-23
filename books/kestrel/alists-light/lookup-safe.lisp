; Look up a key using EQL, throwing an error if not found.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "lookup-equal")

;what about when the value is nil?
;uses eql as the equiv, just like assoc
(defund lookup-safe (key alist)
  (declare (xargs :guard (if (eqlablep key)
                             (alistp alist)
                             (eqlable-alistp alist))))
  (let ((result (assoc key alist)))
    (if result
        (cdr result)
      (hard-error
       'lookup-safe
       "The lookup returned nil, which is an error for this operation. Key: ~x0. Alist: ~x1."
       (acons #\0 key (acons #\1 alist nil))))))

(defthm lookup-safe-becomes-lookup-equal
  (equal (lookup-safe key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-safe lookup-equal))))
