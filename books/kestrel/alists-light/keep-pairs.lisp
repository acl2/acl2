; A utility to filter an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Rename to filter-alist?
;; Keep the pairs in ALIST whose keys are in KEYS.
(defun keep-pairs (keys alist)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp alist)
      nil
    (let* ((pair (first alist))
           (key (car pair)))
      (if (member-equal key keys)
          ;; keep the pair:
          (cons pair (keep-pairs keys (rest alist)))
        ;; drop the pair
        (keep-pairs keys (rest alist))))))
