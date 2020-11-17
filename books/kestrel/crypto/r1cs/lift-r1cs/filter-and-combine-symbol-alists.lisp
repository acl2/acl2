(in-package "ACL2")

;; A way to represent symbolic symbol-alists (which are linear structures and
;; can be very deep) using tree-shaped terms.  Resolving a lookup using the
;; rule lookup-equal-of-filter-and-combine-symbol-alists-safe should be
;; logarithmic instead of linear in the depth of the alist.

;; To be useful, this machinery requires that keys of the alist are a known set
;; of constant symbols.

(include-book "kestrel/alists-light/assoc-equal" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "proof-utils") ;for make-valuation-from-keyword-vars (move that here?)
(local (include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system)) ;todo: add symbol-listp-of-take, etc
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(local
 (defthm symbol-listp-of-take
   (implies (symbol-listp l)
            (symbol-listp (take n l)))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm symbol-listp-of-nthcdr
   (implies (symbol-listp l)
            (symbol-listp (nthcdr n l)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm symbolp-of-nth-when-symbol-listp
   (implies (symbol-listp l)
            (symbolp (nth n l)))
   :hints (("Goal" :in-theory (enable nth)))))


;;from axioms.lisp:
(defthm equal-coerce
    (implies (and (stringp x)
                  (stringp y))
             (equal (equal (coerce x 'list)
                           (coerce y 'list))
                    (equal x y)))
    :hints (("Goal" :use
             ((:instance coerce-inverse-2 (x x))
              (:instance coerce-inverse-2 (x y)))
             :in-theory (disable coerce-inverse-2))))

(defthm symbol-<-antisymmetric-cheap
  (implies (symbol-< x y)
           (not (symbol-< y x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-< STRING<))))

;;see also SYMBOL-<-TRICHOTOMY
(defthm symbol-<-when-not-symbol-<-and-not-equal-cheap
  (implies (and (not (symbol-< y x))
                (not (equal x y))
                (symbolp x)
                (symbolp y))
           (symbol-< x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil nil)))
  :hints (("Goal" :in-theory (enable symbol-< string<))))

;;; end of library stuff

(defun filter-keys-symbol-< (key alist)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-alistp alist))))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (entry-key (car entry)))
      (if (symbol-< entry-key key)
          (acons entry-key
                 (cdr entry)
                 (filter-keys-symbol-< key (rest alist)))
        (filter-keys-symbol-< key (rest alist))))))

(defthm true-listp-of-filter-keys-symbol-<
  (true-listp (filter-keys-symbol-< key alist))
  :rule-classes :type-prescription)

(defthm alistp-of-filter-keys-symbol-<
  (alistp (filter-keys-symbol-< key alist))
  :rule-classes :type-prescription)

(defthm lookup-equal-of-filter-keys-symbol-<-when-symbol-<
  (implies (symbol-< key1 key2)
           (equal (lookup-equal key1 (filter-keys-symbol-< key2 alist))
                  (lookup-equal key1 alist))))

(defthm lookup-equal-of-filter-keys-symbol-<-when-symbol->
  (implies (symbol-< key2 key1)
           (equal (lookup-equal key1 (filter-keys-symbol-< key2 alist))
                  nil)))

(defthm assoc-equal-of-filter-keys-symbol-<-when-symbol-<
  (implies (and (symbol-< key1 key2)
                (alistp alist))
           (equal (assoc-equal key1 (filter-keys-symbol-< key2 alist))
                  (assoc-equal key1 alist))))

(defthm cdr-of-assoc-equal-of-filter-keys-symbol-<-when-symbol-<
  (implies (symbol-< key1 key2)
           (equal (cdr (assoc-equal key1 (filter-keys-symbol-< key2 alist)))
                  (cdr (assoc-equal key1 alist)))))

(defthm assoc-equal-of-filter-keys-symbol-<-when-symbol->=
  (implies (not (symbol-< key1 key2))
           (equal (assoc-equal key1 (filter-keys-symbol-< key2 alist))
                  nil)))

(defun filter-keys-symbol->= (key alist)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-alistp alist))))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (entry-key (car entry)))
      (if (not (symbol-< entry-key key))
          (acons entry-key
                 (cdr entry)
                 (filter-keys-symbol->= key (rest alist)))
        (filter-keys-symbol->= key (rest alist))))))

(defthm true-listp-of-filter-keys-symbol->=
  (true-listp (filter-keys-symbol->= key alist))
  :rule-classes :type-prescription)

(defthm alistp-of-filter-keys-symbol->=
  (alistp (filter-keys-symbol->= key alist))
  :rule-classes :type-prescription)

(defthm assoc-equal-of-filter-keys-symbol->=-when-symbol-<
  (implies (symbol-< key1 key2)
           (equal (assoc-equal key1 (filter-keys-symbol->= key2 alist))
                  nil)))

(defthm cdr-of-assoc-equal-of-filter-keys-symbol->=-when-symbol->=
  (implies (not (symbol-< key1 key2))
           (equal (cdr (assoc-equal key1 (filter-keys-symbol->= key2 alist)))
                  (cdr (assoc-equal key1 alist)))))

;; Drop pairs from alist-small and alist-large that violate the constraints
(defun filter-and-combine-symbol-alists (key alist-small alist-large)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-alistp alist-small)
                              (symbol-alistp alist-large)
                              ;; (all-symbol-< (strip-cars alist-small key))
                              ;; (all-symbol-> (strip-cars alist-large key))
                              )))
  (append (filter-keys-symbol-< key alist-small)
          (filter-keys-symbol->= key alist-large)))

(defthm alistp-of-filter-and-combine-symbol-alists
  (alistp (filter-and-combine-symbol-alists key alist-small alist-large)))

;; The key rule
(defthm lookup-equal-of-filter-and-combine-symbol-alists
  (implies (and (symbolp key1)
                (symbolp key2))
           (equal (lookup-equal key1 (filter-and-combine-symbol-alists key2 alist-small alist-large))
                  (if (symbol-< key1 key2)
                      (lookup-equal key1 alist-small)
                    (lookup-equal key1 alist-large))))
  :hints (("Goal" :in-theory (enable lookup-equal))))

;; Since key1 and key2 are required to be constants, this does not introduce
;; IFs.  Furthermore, the resulting lookup-equal term should be about half the
;; size of the LHS, provided alist-small and alist-large are roughly the same
;; size.
(defthm lookup-equal-of-filter-and-combine-symbol-alists-safe
  (implies (and (syntaxp (and (quotep key1)
                              (quotep key2)))
                (symbolp key1)
                (symbolp key2))
           (equal (lookup-equal key1 (filter-and-combine-symbol-alists key2 alist-small alist-large))
                  (if (symbol-< key1 key2)
                      (lookup-equal key1 alist-small)
                    (lookup-equal key1 alist-large))))
  :hints (("Goal" :in-theory (enable lookup-equal))))

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
        `(filter-and-combine-symbol-alists ',var
                                           ,(make-valuation-from-keyword-vars2-aux first-half)
                                           ,(make-valuation-from-keyword-vars2-aux second-half))))))

;; Makes a tree of calls to filter-and-combine-symbol-alists instead of a
;; (potentially very deep) nest of calls to acons.
(defun make-valuation-from-keyword-vars2 (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (make-valuation-from-keyword-vars2-aux (merge-sort-symbol-< vars)))
