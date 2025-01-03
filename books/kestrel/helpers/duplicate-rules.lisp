; A tool to find duplicate rules in the world
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Relax the comparison (currently only finds exact-duplicates, except for variable normalization)
;; TODO: Think about the same body but different rule-classes!
;; TODO: Think about corollaries.

(include-book "kestrel/world-light/defs-in-world" :dir :system)
(include-book "kestrel/utilities/defmergesort" :dir :system)
(include-book "kestrel/utilities/world" :dir :system) ; reduce
(include-book "kestrel/utilities/make-var-names" :dir :system) ; reduce?
(include-book "kestrel/terms-light/sublis-var-simple" :dir :system)
(local (include-book "kestrel/terms-light/all-vars1" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(defun name-and-bodyp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (symbolp (car x))
       (pseudo-termp (cdr x))))

(defun name-and-body-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (name-and-bodyp (first x))
         (name-and-body-listp (rest x)))))

(defun name-and-body-< (x y)
  (declare (xargs :guard (and (name-and-bodyp x)
                              (name-and-bodyp y))))
  ;; term-order is like <=
  (not (term-order (cdr y) (cdr x))))

(defmergesort merge-sort-names-and-bodies merge-names-and-bodies name-and-body-< name-and-bodyp)

(defun standardize-vars (term)
  (declare (xargs :guard (pseudo-termp term)))
  (let* ((vars (all-vars term))
         (new-vars (make-var-names 'x (len vars)))
         (alist (pairlis$ vars new-vars)))
    ;; Can't use sublis-var here as it does too much!
    ;; Example: (sublis-var nil '(< '0 '0)) = 'NIL
    (sublis-var-simple alist term)))

(defun names-and-bodies (names wrld acc)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp wrld)
                              (true-listp acc))))
  (if (endp names)
      acc
    (let* ((name (first names))
           (body (standardize-vars (defthm-body name wrld))))
      (names-and-bodies (rest names)
                        wrld
                        (cons (cons name body)
                              acc)))))

;; Returns (mv rules-with-same-body rest)
(defun leading-rules-with-body (body names-and-bodies acc)
  (declare (xargs :guard (and (pseudo-termp body)
                              (name-and-body-listp names-and-bodies)
                              (true-listp acc))))
  (if (endp names-and-bodies)
      (mv acc nil)
    (let* ((first-name-and-body (first names-and-bodies))
           (first-body (cdr first-name-and-body)))
      (if (equal body first-body)
          (leading-rules-with-body body
                                   (rest names-and-bodies)
                                   (cons first-name-and-body acc))
        (mv acc names-and-bodies)))))

(local
  (defthm leading-rules-with-body-shorter
    (<= (len (mv-nth 1 (leading-rules-with-body body names-and-bodies acc)))
        (len names-and-bodies))
    :rule-classes :linear))

(local
  (defthm name-and-body-listp-of-mv-nth-1-of-leading-rules-with-body
    (implies (name-and-body-listp names-and-bodies)
             (name-and-body-listp (mv-nth 1 (leading-rules-with-body body names-and-bodies acc))))))

;; the names-and-bodies must be sorted, so that duplicate rules are consecutive
(defun group-same-body (names-and-bodies acc)
  (declare (xargs :guard (and (name-and-body-listp names-and-bodies)
                              (true-listp acc))
                  :measure (len names-and-bodies)))
  (if (endp names-and-bodies)
      acc
    (if (endp (rest names-and-bodies))
        (cons (list (first names-and-bodies))
              acc)
      (let* ((first-name-and-body (first names-and-bodies))
             (first-body (cdr first-name-and-body)))
        (mv-let (rules-with-same-body rest)
          (leading-rules-with-body first-body (rest names-and-bodies) nil)
          (group-same-body rest
                           (cons (cons first-name-and-body
                                       rules-with-same-body)
                                 acc)))))))

(defun non-singletons (lists)
  (declare (xargs :guard (true-list-listp lists)))
  (if (endp lists)
      nil
    (let ((list (first lists)))
      (if (< 1 (len list))
          (cons list (non-singletons (rest lists)))
        (non-singletons (rest lists))))))

;; Prints groups of rules with the same body.  Warning: May have different rule-classes!
(defun duplicate-rules (wrld)
;  (declare (xargs :guard (plist-worldp wrld))) ; todo
  (let* ((defthm-and-defaxiom-names (defthms-in-world wrld))
         (names-and-bodies (names-and-bodies defthm-and-defaxiom-names wrld nil))
         (sorted-names-and-bodies (merge-sort-names-and-bodies names-and-bodies))
         (grouped-names-and-bodies (group-same-body sorted-names-and-bodies nil)))
    (non-singletons grouped-names-and-bodies)))

