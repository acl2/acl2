; A tool to count occurrences of a term in another term
;
; Copyright (C) 2014-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add tests

(include-book "non-trivial-formals")
(include-book "free-vars-in-term")

(mutual-recursion
 ;; Count how many times TARGET-TERM appears in TERM (attempts to handle
 ;; lambdas sensibly, without risking blowup from beta reduction).
 ;; TARGET-TERM-VARS should be the free vars in TARGET-TERM.
 (defun count-occurences-in-term-aux (target-term term target-term-vars)
   (declare (xargs :guard (and (pseudo-termp target-term)
                               (pseudo-termp term)
                               (symbol-listp target-term-vars))))
   (if (equal term target-term)
       1
     (if (or (variablep term)
             (fquotep term))
         0 ; we don't look inside quoted constants
       (+ (if (consp (ffn-symb term))
              ;; lambda:
              (let* ((lambda-formals (lambda-formals (ffn-symb term)))
                     (args (fargs term)))
                (if (intersection-eq (non-trivial-formals lambda-formals args) target-term-vars)
                    ;; The lambda changes the meaning of one of the target term's vars, so
                    ;; don't look inside the lambda body.
                    0
                  ;; Do count occs in the lambda-body (where the target-term has the same meaning):
                  (count-occurences-in-term-aux target-term (lambda-body (ffn-symb term)) target-term-vars)))
            ;; not a lambda:
            0)
          ;; count occurrences in args:
          (count-occurences-in-terms-aux target-term (fargs term) target-term-vars)))))

 ;; Count how many times TARGET-TERM appears in TERMS.
 (defun count-occurences-in-terms-aux (target-term terms target-term-vars)
   (declare (xargs :guard (and (pseudo-termp target-term)
                               (pseudo-term-listp terms)
                               (symbol-listp target-term-vars))))
   (if (endp terms)
       0
     (+ (count-occurences-in-term-aux target-term (car terms) target-term-vars)
        (count-occurences-in-terms-aux target-term (cdr terms) target-term-vars)))))

(defund count-occurences-in-term (target-term term)
  (declare (xargs :guard (and (pseudo-termp target-term)
                              (pseudo-termp term))))
  (count-occurences-in-term-aux target-term term (free-vars-in-term target-term)))
