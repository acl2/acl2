; An alternative to subst-var that can sometimes go into lambda bodies
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "non-trivial-formals-and-args")
(include-book "free-vars-in-term")
(include-book "make-lambda-application-simple")
(include-book "std/util/bstar" :dir :system)

;; See also the built-in function subst-var.  This handles lambdas differently, not simply
;; substituting in the arguments.  This also avoids introducing unserialized
;; lambdas (ones with multiple non-trivial formals).

;; This books deals with replacement of single vars, but see the sublis-varXXX functions.

;; See tests in subst-var-alt-tests.lisp.

(local (in-theory (disable mv-nth)))

;; maybe replace the name "alt" with "deep"

(mutual-recursion
  ;; Replace VAR with REPLACEMENT in TERM.
  ;; Note the order of the arguments!
 (defund subst-var-alt (var replacement term)
   (declare (xargs :guard (and (symbolp var)
                               (pseudo-termp replacement)
                               (pseudo-termp term))
                   :verify-guards nil ; done below
                   :measure (acl2-count term)))
   (if (variablep term)
       (if (equal term var)
           replacement
         term)
     (if (fquotep term)
         term
       (let ((fn (ffn-symb term)))
         (if (flambdap fn)
             ;; Lambda application:
             (b* ((formals (lambda-formals fn))
                  (body (lambda-body fn))
                  (args (fargs term)) ; we don't subst in these right away in case var is a trivial formal
                  ((mv non-trivial-formals non-trivial-args)
                   (non-trivial-formals-and-args formals args)))
               (if (or (not (member-eq var formals)) ; no need to go into the body
                       (member-eq var non-trivial-formals) ; can't substitute in the body because the var is shadowed there
                       )
                   ;; Replace in the args only:
                   (cons-with-hint fn (subst-var-alt-lst var replacement args) term)
                 ;; Var is a trivial formal.  We could just substitute in its
                 ;; actual, but instead we attempt to go into he lambda-body:
                 (if (or (intersection-eq (free-vars-in-term replacement) non-trivial-formals)
                         (not (mbt (equal (len formals) (len args)))) ; for termination
                         )
                     ;; Possible clash, so be conservative: just wrap a binding of var around the term:
                     ;; TODO: Do we ever want to avoid making this lambda?
                     (make-lambda-application-simple (list var) (list replacement) term)
                   ;; No clash, so we can move into the body:
                   ;; todo: just remove the formal and arg for x and call something simpler here?
                   (make-lambda-application-simple non-trivial-formals
                                                   ;; Fixup all the non-trivial args (trivial args other than var are not affected by the replacement of var)
                                                   (subst-var-alt-lst var replacement non-trivial-args)
                                                   (subst-var-alt var replacement body)))))
           ;; Not a lambda application:
           (cons-with-hint fn (subst-var-alt-lst var replacement (fargs term)) term))))))

 (defund subst-var-alt-lst (var replacement terms)
   (declare (xargs :guard (and (symbolp var)
                               (pseudo-termp replacement)
                               (pseudo-term-listp terms))
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons-with-hint (subst-var-alt var replacement (first terms))
                     (subst-var-alt-lst var replacement (rest terms))
                     terms))))

(make-flag subst-var-alt)

(defthm len-of-subst-var-alt-lst
  (equal (len (subst-var-alt-lst var replacement terms))
         (len terms))
  :hints (("Goal" :in-theory (enable subst-var-alt-lst))))

(defthm car-of-subst-var-alt-lst
  (equal (car (subst-var-alt-lst var replacement terms))
         (if (consp terms)
             (subst-var-alt var replacement (car terms))
           nil))
  :hints (("Goal" :expand (subst-var-alt-lst var replacement terms)
           :in-theory (enable subst-var-alt-lst))))

(defthm cdr-of-subst-var-alt-lst
  (equal (cdr (subst-var-alt-lst var replacement terms))
         (subst-var-alt-lst var replacement (cdr terms)))
  :hints (("Goal" :expand (subst-var-alt-lst var replacement terms)
           :in-theory (enable subst-var-alt-lst))))

;; subst-var-alt preserves pseudo-termp.
(defthm-flag-subst-var-alt
  (defthm pseudo-termp-of-subst-var-alt
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (pseudo-termp term))
             (pseudo-termp (subst-var-alt var replacement term)))
    :flag subst-var-alt)
  (defthm pseudo-term-listp-of-subst-var-alt-lst
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (pseudo-term-listp terms))
             (pseudo-term-listp (subst-var-alt-lst var replacement terms)))
    :flag subst-var-alt-lst)
  :hints (("Goal" :expand (pseudo-termp (cons (car term)
                                              (subst-var-alt-lst var replacement (cdr term))))
           :in-theory (enable subst-var-alt
                              subst-var-alt-lst
                              pseudo-termp))))

(verify-guards subst-var-alt)
