; Utilities for terms that are clearly lists
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "forms")
(include-book "quote")

;dup
(defun enquote-list (items)
  (declare (xargs :guard t))
  (if (atom items)
      nil
    (cons (enquote (car items))
          (enquote-list (cdr items)))))

(defthm pseudo-term-listp-of-enquote-list
  (pseudo-term-listp (enquote-list items)))

;; Test whether TERM is syntactically a true-list: a nest of CONSes
;; terminating in a quoted true list (often 'nil).
(defund syntactic-true-listp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      nil
    (let ((fn (ffn-symb term)))
      (case fn
        (quote (true-listp (unquote term)))
        (cons (and (= 2 (len (fargs term)))
                   (syntactic-true-listp (farg2 term))))
        (otherwise nil)))))

(defthm syntactic-true-listp-forward-to-consp
  (implies (syntactic-true-listp term)
           (consp term))
  :hints (("Goal" :in-theory (enable syntactic-true-listp))))

;; Gets the length of a term that syntactically is clearly a list.
(defund syntactic-length (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (syntactic-true-listp term))
                  :verify-guards nil ; done below
                  ))
  (if (not (mbt (consp term))) ;for termination
      0
    (let ((fn (ffn-symb term)))
      (if (eq 'quote fn)
          (len (unquote term))
        ;; must be a cons:
        (+ 1 (syntactic-length (farg2 term)))))))

(verify-guards syntactic-length :hints (("Goal" :in-theory (enable syntactic-true-listp))))

;; Extracts the elements of a syntactic list
(defun syntactic-list-elements (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (syntactic-true-listp term))
                  :guard-hints (("Goal" :in-theory (enable syntactic-true-listp)))))
  (if (not (mbt (consp term))) ;for termination
      nil
    (if (quotep term)
        (enquote-list (unquote term))
      ;; must be a cons:
      (cons (farg1 term) ; must be a call of cons
            (syntactic-list-elements (farg2 term))))))

(defthm pseudo-term-listp-of-syntactic-list-elements
  (implies (and (pseudo-termp term)
                (syntactic-true-listp term))
           (pseudo-term-listp (syntactic-list-elements term)))
  :hints (("Goal" :in-theory (enable syntactic-true-listp))))
