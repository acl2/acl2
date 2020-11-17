(in-package "R1CS")

;; utilities for doing proofs about R1CSes

(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defun make-valuation-from-keyword-vars-aux (vars acc)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      acc
    (let* ((var (first vars)) ;the keyword
           (var-in-acl2-package (intern-in-package-of-symbol (symbol-name var) 'defthm)))
      (make-valuation-from-keyword-vars-aux (rest vars)
                                            `(acons ',var ,var-in-acl2-package ,acc)))))

(defun acl2::make-valuation-from-keyword-vars (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (make-valuation-from-keyword-vars-aux (acl2::reverse-list vars) acl2::*nil*))

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

(defun make-bitp-assumptions-from-keyword-vars-aux (vars acc)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      acc
    (let* ((var (first vars)) ;the keyword
           (var-in-acl2-package (intern-in-package-of-symbol (symbol-name var) 'defthm)))
      (make-bitp-assumptions-from-keyword-vars-aux (rest vars)
                                                  (cons `(bitp ,var-in-acl2-package) acc)))))

(defun make-bitp-assumptions-from-keyword-vars (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (make-bitp-assumptions-from-keyword-vars-aux (acl2::reverse-list vars) nil))
