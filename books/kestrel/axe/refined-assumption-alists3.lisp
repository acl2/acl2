; More material on refined-assumption-alists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "refined-assumption-alists")
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))

;; This material is only used by legacy rewriters

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Just call member-equal and remove the p from this name?
;; Only called by the legacy rewriter?
(defund nodenum-equal-to-refined-assumptionp (nodenum refined-assumption-alist dag-array)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                              (refined-assumption-alistp refined-assumption-alist))))
  (let* ((expr (aref1 'dag-array dag-array nodenum)))
    (and (consp expr) ;refined assumptions must be function calls
         (let ((fn (ffn-symb expr)))
           (and (not (eq 'quote fn))
                (let ((arglists-for-fn (lookup-eq fn refined-assumption-alist)))
                  (memberp (dargs expr) arglists-for-fn)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun largest-non-quotep-in-darg-lists (darg-lists)
  (declare (xargs :guard (darg-list-listp darg-lists)))
  (if (endp darg-lists)
      -1 ;think about this as the default
    (max (largest-non-quotep (first darg-lists))
         (largest-non-quotep-in-darg-lists (rest darg-lists)))))

;; only used by the legacy rewriter
;; also reverses.
(defund fixup-refined-assumption-arg-lists (darg-lists renaming-array-name renaming-array acc)
  (declare (xargs :guard (and (darg-list-listp darg-lists)
                              (renaming-arrayp renaming-array-name renaming-array (+ 1 (largest-non-quotep-in-darg-lists darg-lists))))))
  (if (endp darg-lists)
      acc ; could reverse here
    (fixup-refined-assumption-arg-lists (rest darg-lists)
                                        renaming-array-name
                                        renaming-array
                                        (cons (rename-dargs (first darg-lists) renaming-array-name renaming-array)
                                              acc))))

;; only used by the legacy rewriter
;; todo: guard is awkward.  pass in the nume-valid-nodes of the renaming-array and use as the bound
(defund fixup-refined-assumption-alist (refined-assumption-alist renaming-array-name renaming-array acc)
  ;; (declare (xargs :guard (and (bounded-refined-assumption-alistp refined-assumption-alist num-valid-nodes)
  ;;                             (renaming-arrayp renaming-array-name renaming-array num-valid-nodes))))
  (if (endp refined-assumption-alist)
      acc
    (let* ((entry (first refined-assumption-alist))
           (fn (car entry))
           (arg-lists (cdr entry))
           (fixed-up-arg-lists (fixup-refined-assumption-arg-lists arg-lists renaming-array-name renaming-array nil)))
      (fixup-refined-assumption-alist (rest refined-assumption-alist)
                                      renaming-array-name
                                      renaming-array
                                      (acons-fast fn fixed-up-arg-lists acc)))))

;;;
;;; decoding refined-assumption-alists (only used to implement WORK-HARD)
;;;

;see cons-onto-all
(defund add-fn-calls (fn arg-lists acc)
  (declare (xargs :guard (true-listp arg-lists)))
  (if (endp arg-lists)
      acc
    (add-fn-calls fn
                  (rest arg-lists)
                  (cons (cons fn (first arg-lists)) acc))))

(defund decode-refined-assumption-alist-aux (refined-assumption-alist acc)
  (declare (xargs :guard (refined-assumption-alistp refined-assumption-alist)
                  :guard-hints (("Goal" :in-theory (enable refined-assumption-alistp)))))
  (if (endp refined-assumption-alist)
      acc
    (let* ((entry (car refined-assumption-alist))
           (fn (car entry))
           (arg-lists (cdr entry)))
      (decode-refined-assumption-alist-aux (cdr refined-assumption-alist)
                                           (add-fn-calls fn arg-lists acc)))))

;turns refined-assumption-alist back into the equivalent list of axe-trees
;; todo: prove return type
(defund decode-refined-assumption-alist (refined-assumption-alist)
  (declare (xargs :guard (refined-assumption-alistp refined-assumption-alist)))
  (decode-refined-assumption-alist-aux refined-assumption-alist nil))
