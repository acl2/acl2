; Utilities to support transformations
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sublis-var-simple")
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

;; Change each call to TARGET-FN in TERM to have a new parameter
;; (given as the last param), whose value is expressed in terms of the
;; values of the other parameters in that call according to EXPR.
;; EXPR may also mention other vars that are not formals of TARGET-FN
;; (these parts of EXPR are left as-is - TODO: Think about this).
;;TODO: we could change this to be like
;;add-param-to-calls-in-untranslated-term (gather calls, then fixup
;;calls, then apply the replacement)
(mutual-recursion
 (defun add-param-to-calls-in-term (term
                                    target-fn ;the function whose calls we will change
                                    formals   ;the usual formals of fn
                                    expr ;an expression for the new parameter, in terms of the formals of fn (these will get replaced by the actuals for each call)
                                    )
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbolp target-fn)
                               (symbol-listp formals)
                               (pseudo-termp expr))
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       term
     (if (quotep term)
         term
       ;;it's a function call (maybe a lambda application):
       (let* ((args (fargs term))
              (args (add-param-to-calls-in-terms args target-fn formals expr)) ;process the args first
              (fn (ffn-symb term)))
         (if (eq fn target-fn)
             ;; Add the new parameter:
             `(,fn ,@args ,(sublis-var-simple (pairlis$ formals args) expr))
           (let ((fn (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
                         (let* ((lambda-formals (second fn))
                                (lambda-body (third fn))
                                (lambda-body (add-param-to-calls-in-term lambda-body target-fn formals expr))) ;;apply recursively to the lambda body
                           `(lambda (,@lambda-formals) ,lambda-body))
                       fn)))
             `(,fn ,@args)))))))

 (defun add-param-to-calls-in-terms (terms
                                     target-fn ;the function whose calls we will change
                                     formals ;the usual formals of fn
                                     expr ;an expression for the new parameter, in terms of the formals of fn (these will get replaced by the actuals for each call)
                                     )
   (declare (xargs :measure (acl2-count terms)
                   :guard (and (pseudo-term-listp terms)
                               (symbolp target-fn)
                               (symbol-listp formals)
                               (pseudo-termp expr))))
   (if (endp terms)
       nil
     (cons (add-param-to-calls-in-term (first terms) target-fn formals expr)
           (add-param-to-calls-in-terms (rest terms) target-fn formals expr)))))

(verify-guards add-param-to-calls-in-term)
