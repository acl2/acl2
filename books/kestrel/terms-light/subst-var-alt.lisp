; An alternative to subst-var.
;
; Copyright (C) 2023 Kestrel Institute
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

(local (in-theory (disable mv-nth)))

;; Can only replace on var at a time.
(mutual-recursion
 ;; Replace VAR with REPLACEMENT in TERM.
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
                  (args (fargs term))
                  ;;(non-trivial-formals (non-trivial-formals formals args))
                  ;;(trivial-formals (trivial-formals formals args))
                  ((mv non-trivial-formals non-trivial-args)
                   (non-trivial-formals-and-args formals args))
                  )
               (if (or (not (member-eq var formals)) ; no need to go into the body
                       (member-eq var non-trivial-formals) ; can't substitute in the body because the var is shadowed there
                       )
                   ;;(not (member-eq var trivial-formals))
                   ;; Replace in the args only:
                   (cons ;try fcons-term
                    fn
                    (subst-var-alt-lst var replacement args))
                 ;; Var is a trivial formal.  Avoid making its formal non-trivial:
                 (if (or (intersection-eq (free-vars-in-term replacement)
                                          non-trivial-formals)
                         (not (mbt (equal (len formals) (len args)))))
                     ;; Possible clash, so be conservative: just wrap a binding of var around the term:
                     (make-lambda-application-simple (list var) (list replacement) term)
                   ;; No clash, so we can move into the body:
                   (make-lambda-application-simple non-trivial-formals
                                                   ;; Fixup all the non-trivial args (trivial args other than var are not affected by the subst)
                                                   (subst-var-alt-lst var replacement non-trivial-args)
                                                   (subst-var-alt var replacement body)))))
           ;; Not a lambda application:
           (cons ;try fcons-term
            fn
            (subst-var-alt-lst var replacement (fargs term))))))))

 (defund subst-var-alt-lst (var replacement terms)
   (declare (xargs :guard (and (symbolp var)
                               (pseudo-termp replacement)
                               (pseudo-term-listp terms))
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (subst-var-alt var replacement (first terms))
           (subst-var-alt-lst var replacement (rest terms))))))

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
