; A utility to replace subterms a given term
;
; Copyright (C) 2014-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "non-trivial-formals")
(include-book "free-vars-in-term")
(include-book "make-lambda-application-simple")

;; Replace occurrences of OLD with NEW in TERM.
;; This could be called "replace-term" but that name seems to already be used elsewhere.
;; Note that it's not clear how term replacement should deal with lambdas/lets, as they change the meaning of variables.
;; This allows replacement of terms that are inside lambda bodies and that don't mention any non-trivially-bound lambda vars.
;;TODO: Optimize by adding a changep flag (don't rebuild the term if nothing changes):
(mutual-recursion
 (defund replace-term-with-term (old new term)
   (declare (xargs :guard (and (pseudo-termp old)
                               (pseudo-termp new)
                               (pseudo-termp term))
                   :verify-guards nil ; done below
                   ))
   (if (equal term old)
       new
     (cond ((variablep term) term)
           ((quotep term) term)
           ((flambda-applicationp term)
            (let* ((lambda-formals (lambda-formals (ffn-symb term)))
                   (non-trivial-formals (non-trivial-formals lambda-formals (fargs term))) ; trivial formals (bound to themselves) don't really cause problems
                   (lambda-body (lambda-body (ffn-symb term))))
              (if (and (not (intersection-eq non-trivial-formals (free-vars-in-term old)))
                       (not (intersection-eq non-trivial-formals (free-vars-in-term new))))
                  ;; Safe to replace within the lambda-body, because the meanining of all vars in the old term
                  ;; and all vars the new term is unchanged by the lambda:
                  (make-lambda-application-simple lambda-formals
                                                  (replace-term-with-term-lst old new (fargs term))
                                                  (replace-term-with-term old new lambda-body))
                ;; Not safe to replace within the lambda-body, so only do it in the args:
                `(,(ffn-symb term) ; the lambda
                  ,@(replace-term-with-term-lst old new (fargs term))))))
           ;; regular function call:
           (t `(,(ffn-symb term) ,@(replace-term-with-term-lst old new (fargs term)))))))
 (defund replace-term-with-term-lst (old new terms)
   (declare (xargs :guard (and (pseudo-termp old)
                               (pseudo-termp new)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       nil
     (cons (replace-term-with-term old new (first terms))
           (replace-term-with-term-lst old new (rest terms))))))

(defthm len-of-replace-term-with-term-lst
  (equal (len (replace-term-with-term-lst old new terms))
         (len terms))
  :hints (("Goal" :in-theory (enable replace-term-with-term-lst))))

(make-flag replace-term-with-term)

(defthm-flag-replace-term-with-term
  (defthm pseudo-termp-of-replace-term-with-term
    (implies (and (pseudo-termp term)
                  (pseudo-termp new))
             (pseudo-termp (replace-term-with-term old new term)))
    :flag replace-term-with-term)
  (defthm pseudo-term-listp-of-replace-term-with-term-lst
    (implies (and (pseudo-term-listp terms)
                  (pseudo-termp new))
             (pseudo-term-listp (replace-term-with-term-lst old new terms)))
    :flag replace-term-with-term-lst)
  :hints (("Goal" :in-theory (enable replace-term-with-term-lst
                                     replace-term-with-term))))

(verify-guards replace-term-with-term)
