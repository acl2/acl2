; A tool to turn lambdas into lets
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/non-trivial-bindings" :dir :system)

(mutual-recursion
 ;; Note that the result is no longer a translated term (pseudo-termp).
 ;; TODO: Consider combining nested LETs into LET*s.
 (defund reconstruct-lets-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)))
   (if (or (variablep term)
           (fquotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((fn (ffn-symb term))
            (new-args (reconstruct-lets-in-terms (fargs term))))
       (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           `(let ,(alist-to-doublets (non-trivial-bindings (lambda-formals fn) new-args))
              ,(reconstruct-lets-in-term (lambda-body fn)))
         ;; not a lambda application, so just rebuild the function call:
         `(,fn ,@new-args)))))

 (defund reconstruct-lets-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-lets-in-term (first terms))
           (reconstruct-lets-in-terms (rest terms))))))
