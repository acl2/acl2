(in-package "R1CS")

;; utilities for doing proofs about R1CSes

(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system)
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system)) ;todo: add symbol-listp-of-take, etc
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(defun make-valuation-from-keyword-vars-aux (vars acc)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      acc
    (let* ((var (first vars)) ;the keyword
           (var-in-acl2-package (intern-in-package-of-symbol (symbol-name var) 'defthm)))
      (make-valuation-from-keyword-vars-aux (rest vars)
                                            `(acons ',var ,var-in-acl2-package ,acc)))))

(defun make-valuation-from-keyword-vars (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (make-valuation-from-keyword-vars-aux (acl2::reverse-list vars) acl2::*nil*))

(defun make-valuation-from-keyword-vars2-aux (sorted-vars)
  (declare (xargs :guard (symbol-listp sorted-vars)
                  :measure (len sorted-vars)))
  (let ((len (len sorted-vars)))
    (if (< len 3) ;; could try different values here (must be at least 2)
        (make-valuation-from-keyword-vars sorted-vars)
      ;; At least 2 vars:
      (let* ((first-half-len (floor len 2))
             (first-half (take first-half-len sorted-vars))
             (second-half (nthcdr first-half-len sorted-vars))
             (var (first second-half)))
        `(acl2::filter-and-combine-symbol-alists ',var
                                                 ,(make-valuation-from-keyword-vars2-aux first-half)
                                                 ,(make-valuation-from-keyword-vars2-aux second-half))))))

;; Makes a tree of calls to filter-and-combine-symbol-alists instead of a
;; (potentially very deep) nest of calls to acons.
(defun make-valuation-from-keyword-vars2 (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (make-valuation-from-keyword-vars2-aux (acl2::merge-sort-symbol-< vars)))

(defun make-fep-assumptions-from-keyword-vars-aux (vars prime acc)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      acc
    (let* ((var (first vars)) ;the keyword
           (var-in-acl2-package (intern-in-package-of-symbol (symbol-name var) 'defthm)))
      (make-fep-assumptions-from-keyword-vars-aux (rest vars)
                                                  prime
                                                  (cons `(pfield::fep ,var-in-acl2-package ,prime) acc)))))

(defun make-fep-assumptions-from-keyword-vars (vars prime)
  (declare (xargs :guard (symbol-listp vars)))
  (make-fep-assumptions-from-keyword-vars-aux (acl2::reverse-list vars) prime nil))

;; (make-fep-assumptions-from-keyword-vars '(:a :b :c) 21888242871839275222246405745257275088548364400416034343698204186575808495617)

;; Is this needed?  Used in one example..
(defun make-bitp-assumptions-from-keyword-vars-aux (vars acc)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      acc
    (let* ((var (first vars)) ;the keyword
           (var-in-acl2-package (intern-in-package-of-symbol (symbol-name var) 'defthm)))
      (make-bitp-assumptions-from-keyword-vars-aux (rest vars)
                                                  (cons `(bitp ,var-in-acl2-package) acc)))))

;; Is this needed?  Used in one example..
(defun make-bitp-assumptions-from-keyword-vars (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (make-bitp-assumptions-from-keyword-vars-aux (acl2::reverse-list vars) nil))
