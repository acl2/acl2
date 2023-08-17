; A custom-keyword hint to generate 2^N combinations of N cases
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;dup
(defun cons-onto-all (item lsts)
  (declare (xargs :guard (true-listp lsts)))
  (if (endp lsts)
      nil
    (cons (cons item (car lsts))
          (cons-onto-all item (cdr lsts)))))

;; Returns a list of lists
(defun all-case-combinations-aux (terms)
  (if (endp terms)
      nil
    (let* ((term (first terms))
           (negated-term (if (and (consp term)
                                  (eq 'not (car term))
                                  (consp (cdr term)))
                             (cadr term)
                           `(not ,term))))
      (if (endp (rest terms))
          (list (list term) (list negated-term))
        (append (cons-onto-all term
                               (all-case-combinations-aux (rest terms)))
                (cons-onto-all negated-term
                               (all-case-combinations-aux (rest terms))))))))

;(all-case-combinations-aux '((foo x) (not (bar y))))

;; Returns a list of cases covering all ways that the TERMS can be true/false.
(defun all-case-combinations (terms)
  (if (not (consp terms))
      (er hard? ':casesx "We do not permit empty :casesx hints.")
    (if (= 1 (len terms))
        ;; special case (no AND required):
        (let ((term (first terms)))
          (list term `(not ,term)))
      (cons-onto-all 'and (all-case-combinations-aux terms)))))

(add-custom-keyword-hint :casesx (splice-keyword-alist :casesx (list :cases (all-case-combinations val)) keyword-alist)
                         :checker (mv nil (true-listp val) state))
