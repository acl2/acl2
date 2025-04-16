; A utility to remove duplicate bindings from an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "acons"))

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

(defthm assoc-equal-of-assoc-equal-when-assoc-equal-arg2
  (implies (assoc-equal key acc)
           (equal (assoc-equal key (uniquify-alist-eq-aux alist acc))
                  (assoc-equal key acc))))

;; for when we want the whole pair
(defthm assoc-equal-of-uniquify-alist-eq-aux
  (implies (alistp alist)
           (equal (assoc-equal key (uniquify-alist-eq-aux alist acc))
                  (if (assoc-equal key acc)
                      (assoc-equal key acc)
                    (assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;; for when we only want the value (no alistp hyp)
(defthm cdr-of-assoc-equal-of-uniquify-alist-eq-aux
  (equal (cdr (assoc-equal key (uniquify-alist-eq-aux alist acc)))
         (if (assoc-equal key acc)
             (cdr (assoc-equal key acc))
           (cdr (assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removes shadowed pairs from ALIST (that is, pairs that bind keys already
;; bound by earlier pairs).  The first binding for each key is the one kept.
(defun uniquify-alist-eq (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (uniquify-alist-eq-aux alist nil))

;; Shows that calling uniquify-alist-eq does not change the result of looking up a key
(defthm assoc-equal-of-uniquify-alist-eq
  (implies (alistp alist)
           (equal (assoc-equal key (uniquify-alist-eq alist))
                  (assoc-equal key alist))))

(defthm cdr-of-assoc-equal-of-uniquify-alist-eq
  (equal (cdr (assoc-equal key (uniquify-alist-eq alist)))
         (cdr (assoc-equal key alist))))
