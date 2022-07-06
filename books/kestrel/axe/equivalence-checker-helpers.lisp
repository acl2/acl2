(in-package "ACL2")

(include-book "kestrel/booleans/bool-fix" :dir :system)
(include-book "kestrel/booleans/boolif" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "axe-types")

;; Helps justify the correctness of using IFF when dealing with contexts
(defthm if-of-bool-fix
  (equal (if (bool-fix test) x y)
         (if test x y)))

;; Helps justify the correctness of using IFF when dealing with contexts
(defthm myif-of-bool-fix
  (equal (myif (bool-fix test) x y)
         (myif test x y))
  :hints (("Goal" :in-theory (enable bool-fix))))

;; Helps justify the correctness of using IFF when dealing with contexts
(defthm boolif-of-bool-fix
  (equal (boolif (bool-fix test) x y)
         (boolif test x y))
  :hints (("Goal" :in-theory (enable boolif))))

;dup
(defun pairlis$-safe (lst1 lst2)
  (if (equal (len lst1) (len lst2))
      (pairlis$ lst1 lst2)
    (hard-error 'pairlis$-safe "Lists lengths unequal" nil)))

;; todo: use this (or byte-types-for-vars) more, in place of pairlis$-safe
(defun assign-type-to-vars (type vars)
  (declare (xargs :guard (and (axe-typep type)
                              (symbol-listp vars))))
  (if (endp vars)
      nil
    (acons (first vars) type
           (assign-type-to-vars type (rest vars)))))

;; Returns an alist mapping each of the VARS to the BV8 type.
(defun byte-types-for-vars (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (assign-type-to-vars (make-bv-type 8) vars))

;; Returns an alist mapping each of the VARS to the BV1 (= bit) type.
(defun bit-types-for-vars (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (assign-type-to-vars (make-bv-type 1) vars))

;; Returns an alist mapping each of the VARS to the BV type of size SIZE.
(defun bv-types-for-vars (size vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (natp size))))
  (assign-type-to-vars (make-bv-type size) vars))
