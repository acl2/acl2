; Checking whether functions are called in terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Rename this term-calls-some-fnp?
;; Instead of calling this, one could gather all called functions and check for
;; membership in the result, but that might be slower.
;; The FNS should not include quotep.
(mutual-recursion
 (defund expr-calls-some-fn (fns term)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-termp term))))
   (if (variablep term)
       nil
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           nil
         ;; function call:
         (or (if (flambdap fn)
                 (expr-calls-some-fn fns (lambda-body fn))
               ;; non-lambda:
               (if (member-eq fn fns) t nil))
             (some-expr-calls-some-fn fns (fargs term)))))))

 (defund some-expr-calls-some-fn (fns terms)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       nil
     (or (expr-calls-some-fn fns (first terms))
         (some-expr-calls-some-fn fns (rest terms))))))

(defund expr-calls-fn (fn term)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-termp term))))
  (expr-calls-some-fn (list fn) term))

(defund some-expr-calls-fn (fn terms)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-listp terms))))
  (some-expr-calls-some-fn (list fn) terms))
