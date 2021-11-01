(in-package "R1CS")

;; utilities for doing proofs about R1CSes

(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system)
(include-book "kestrel/utilities/defmergesort" :dir :system)
(include-book "filter-and-combine-symbol-alists")
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system)) ;todo: add symbol-listp-of-take, etc
(local (include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defund acl2::symbol<-of-cars (x y)
  (declare (xargs :guard (and (consp x)
                              (consp y)
                              (symbolp (car x))
                              (symbolp (car y)))))
  (symbol< (car x) (car y)))

(defun acl2::consp-and-symbolp-car (x)
  (declare (xargs :guard t))
  (and (consp x)
       (symbolp (car x))))

(acl2::defmergesort acl2::merge-symbol<-of-cars
                    acl2::merge-sort-symbol<-of-cars
                    acl2::symbol<-of-cars
                    acl2::consp-and-symbolp-car)

(defthm consp-of-nth-when-symbol-alistp
  (implies (and (symbol-alistp alist)
                (natp n))
           (equal (consp (nth n alist))
                  (< n (len alist))))
  :hints (("Goal" :in-theory (enable nth))))

;; todo: arrange to have defmergesort use symbol-alistp instead of generating ACL2::ALL-CONSP-AND-SYMBOLP-CAR
(defthm all-consp-and-symbolp-car-when-symbol-alistp
  (implies (symbol-alistp alist)
           (acl2::all-consp-and-symbolp-car alist))
  :hints (("Goal" :in-theory (enable symbol-alistp acl2::all-consp-and-symbolp-car))))

(defthm symbol-alistp-of-merge-symbol<-of-cars
  (implies (and (symbol-alistp x)
                (symbol-alistp y)
                (symbol-alistp acc))
           (symbol-alistp (acl2::merge-symbol<-of-cars x y acc)))
  :hints (("Goal" :in-theory (enable acl2::merge-symbol<-of-cars))))

;defforall could do these too?
(defthm symbol-alistp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (symbol-alistp lst)
                (symbol-alistp acc)
                (<= (len tail) (len lst)))
           (symbol-alistp (mv-nth 0 (acl2::split-list-fast-aux lst tail acc)))))

(defthm symbol-alistp-of-mv-nth-0-of-split-list-fast
  (implies (symbol-alistp lst)
           (symbol-alistp (mv-nth 0 (acl2::split-list-fast lst))))
  :hints (("Goal" :in-theory (enable acl2::split-list-fast))))

(defthm symbol-alistp-of-mv-nth-1-of-split-list-fast-aux
  (implies (symbol-alistp lst)
           (symbol-alistp (mv-nth 1 (acl2::split-list-fast-aux lst tail acc)))))

(defthm symbol-alistp-of-mv-nth-1-of-split-list-fast
  (implies (symbol-alistp lst)
           (symbol-alistp (mv-nth 1 (acl2::split-list-fast lst))))
  :hints (("Goal" :in-theory (enable acl2::split-list-fast))))

(defthm symbol-alistp-of-merge-sort-symbol<-of-cars
  (implies(symbol-alistp alist)
          (symbol-alistp (acl2::merge-sort-symbol<-of-cars alist)))
  :hints (("Goal" :in-theory (enable acl2::merge-sort-symbol<-of-cars))))

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
  (make-valuation-from-keyword-vars2-aux (acl2::merge-sort-symbol< vars)))

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


;;; new stuff (deprecate the old stuff?):

;; Makes an acons nest
(defun make-symbolic-valuation-for-alist-aux (alist acc)
  (declare (xargs :guard (symbol-alistp alist)))
  (if (endp alist)
      acc
    (let ((entry (first alist)))
      (make-symbolic-valuation-for-alist-aux (rest alist)
                                             `(acons ',(car entry) ; quoted
                                                     ,(cdr entry)  ; unquoted
                                                     ,acc)))))

;; Makes an acons nest
(defun make-symbolic-valuation-for-alist (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (make-symbolic-valuation-for-alist-aux (acl2::reverse-list alist) acl2::*nil*))

;; Makes a nest of calls to filter-and-combine-symbol-alists
;; Alist may pair r1cs vars (which may be keywords) with their correspinding acl2 vars
;; Alist should be sorted by symbol< applied to the cars of its entries.
(defun make-efficient-symbolic-valuation-for-alist-aux (alist)
  (declare (xargs :guard (symbol-alistp alist)
                  :measure (len alist)))
  (let ((len (len alist)))
    (if (< len 3) ;; could try different values here (must be at least 2)
        (make-symbolic-valuation-for-alist alist)
      ;; At least 2 vars:
      (let* ((first-half-len (floor len 2))
             (first-half (take first-half-len alist))
             (second-half (nthcdr first-half-len alist))
             (var (car (first second-half))))
        `(acl2::filter-and-combine-symbol-alists ',var
                                                 ,(make-efficient-symbolic-valuation-for-alist-aux first-half)
                                                 ,(make-efficient-symbolic-valuation-for-alist-aux second-half))))))

;; Makes a tree of calls to filter-and-combine-symbol-alists instead of a
;; (potentially very deep) nest of calls to acons.
(defun make-efficient-symbolic-valuation-for-alist (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (make-efficient-symbolic-valuation-for-alist-aux (acl2::merge-sort-symbol<-of-cars alist)))
