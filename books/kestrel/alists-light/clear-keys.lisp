; Clearing key in an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund clear-keys-aux (keys alist acc)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist)
                              (alistp acc))))
  (if (endp alist)
      (reverse acc)
    (let ((pair (first alist)))
      (if (member-equal (car pair) keys)
          ;; Drop this pair:
          (clear-keys-aux keys (rest alist) acc)
        ;; Keep this pair:
        (clear-keys-aux keys (rest alist) (cons pair acc))))))

;; Removes all pairs in ALIST whose cars are among the KEYS.
(defund clear-keys (keys alist)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (clear-keys-aux keys alist nil))
