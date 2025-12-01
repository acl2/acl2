; A model term transformation that does nothing but copy the term
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book, and the accompanying book copy-term-proofs.lisp, provides a
;; template for term transformations.  To create a function that transforms
;; terms, one can copy and modify this.

(local (include-book "tools/flag" :dir :system))

;; A "deep copy" of a term
(mutual-recursion
 (defun copy-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (case fn
         (quote term)
         ;; special handling for other functions would go here...
         (t ;; normal function call or lambda application:
          (let ((args (copy-terms (fargs term))))
            (if (consp fn)
             ;; it's a lambda:
                (let* ((formals (lambda-formals fn))
                       (body (lambda-body fn))
                       (body (copy-term body)))
                  ;; todo: use cons-with-hint
                  `((lambda ,formals ,body) ,@args))
              ;; non-lambda:
              (cons-with-hint fn args term))))))))

 (defun copy-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons-with-hint (copy-term (first terms))
                     (copy-terms (rest terms))
                     terms))))

(local (make-flag copy-term))

(defthm len-of-copy-terms
  (equal (len (copy-terms terms))
         (len terms))
  :hints (("Goal" :induct (len terms))))

;; This can be non-local, because the make-event expansion gets stored in the certificate
(defthm-flag-copy-term
  (defthm pseudo-termp-of-copy-term
    (implies (pseudo-termp term)
             (pseudo-termp (copy-term term)))
    :flag copy-term)
  (defthm pseudo-termp-of-copy-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (copy-terms terms)))
    :flag copy-terms))

(verify-guards copy-term :hints (("Goal" :expand ((pseudo-termp term)))))
