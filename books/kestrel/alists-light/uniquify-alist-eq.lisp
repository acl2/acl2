; A utility to remove duplicate bindings from an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/alists-light/acons" :dir :system))

;; See also the deshadow function from the alist books.
;the first binding for each key is the one kept
(defun uniquify-alist-eq-aux (alist acc)
  (declare (xargs :guard (and (symbol-alistp acc)
                              (symbol-alistp alist))))
  (if (atom alist)
      acc ; could reverse this but not necessary
    (let* ((entry (car alist))
           (key (car entry)))
      (if (assoc-eq key acc) ;the acc may be much smaller than the alist..
          (uniquify-alist-eq-aux (cdr alist) acc)
        (uniquify-alist-eq-aux (cdr alist) (acons key (cdr entry) acc))))))

(defthm true-listp-of-uniquify-alist-eq-aux
  (equal (true-listp (uniquify-alist-eq-aux alist acc))
         (true-listp acc)))

;the first binding for each key is the one kept
;fixme prove that this preserves assoc-eq?
(defun uniquify-alist-eq (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (uniquify-alist-eq-aux alist nil))
