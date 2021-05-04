; Checking whether a term is equal to part of a DAG
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")

(mutual-recursion
 ;; Test whether TERM is equal to ITEM wrt DAG-ARRAY.
 ;; Can throw an error if arities are wrong.
 (defun term-equal-dag-itemp (term item dag-array)
   (declare (xargs :guard (and (pseudo-termp term)
                               (or (myquotep item)
                                   (natp item))
                               (if (natp item)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 item))
                                 t))))
   (if (consp item) ;test for a quotep
       (equal term item)
     ;; item is a nodenum, so look it up:
     (let ((expr (aref1 'dag-array dag-array item)))
       (if (consp expr)
           (let ((fn (ffn-symb expr)))
             (if (eq 'quote fn)
                 (equal term expr)
               ;;expr is a function call:
               (and (consp term)
                    (eq (ffn-symb term) fn)
                    (terms-equal-dag-itemsp (fargs term) (dargs expr) dag-array))))
         ;; expr is a variable:
         (eq term expr)))))

 ;; Test whether the TERMS are equal to the ITEMS wrt DAG-ARRAY.
 (defun terms-equal-dag-itemsp (terms items dag-array)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (true-listp items)
                               (all-dargp items)
                               (implies (not (all-myquotep items))
                                        (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep items)))))))
   (if (endp terms)
       (if (not (endp items))
           (er hard? 'terms-equal-dag-itemsp "Arity mismatch.")
         t)
     (if (endp items)
         (er hard? 'terms-equal-dag-itemsp "Arity mismatch.")
       (and (term-equal-dag-itemp (first terms) (first items) dag-array)
            (terms-equal-dag-itemsp (rest terms) (rest items) dag-array))))))

;; Test whether TERM is equal to FN applied to ARGS wrt DAG-ARRAY.
(defund term-equal-dag-exprp (term fn args dag-array)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp fn)
                              (not (eq 'quote fn))
                              (true-listp args)
                              (all-dargp args)
                              (implies (not (all-myquotep args))
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep args)))))))
  (and (consp term) ; ensure TERM is not a var
       (eq (ffn-symb term) fn)
       (terms-equal-dag-itemsp (fargs term) args dag-array)))
