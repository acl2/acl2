; Counting variable occurrences in terms
;
; Copyright (C) 2014-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "non-trivial-formals")

;; TODO: Add tests, especially for lambdas
(mutual-recursion
 ;; Count how many times VAR appears freely in TERM (except look past trivial lambda bindings).
 (defun count-free-occurences-in-term (var term)
   (declare (xargs :guard (and (symbolp var)
                               (pseudo-termp term))))
   (if (variablep term)
       (if (eq term var)
           1
         0)
     (if (fquotep term)
         0
       (if (consp (ffn-symb term))
           ;; lambda:
           (let* ((lambda-formals (lambda-formals (ffn-symb term)))
                  (args (fargs term)))
             (if (member-eq var lambda-formals)
                 (if (member-eq var (non-trivial-formals lambda-formals args))
                     ;; The var is a non-trivial lambda-formal, so count occs
                     ;; in all the args but not in the body (because that var
                     ;; in the body has a different meaning):
                     (count-free-occurences-in-terms var (fargs term))
                   ;; The var is a trivial lambda-formal, so count occs in the
                   ;; other args and occs in the body (where the var has the
                   ;; same meaning):
                   (+ (count-free-occurences-in-terms var (fargs term))
                      -1 ; for the trivial binding
                      (count-free-occurences-in-term var (lambda-body (ffn-symb term)))))
               ;; The var is not a lambda-formal, so count occs in the args
               ;; (the var does not appear in the lambda body):
               (count-free-occurences-in-terms var (fargs term))))
         ;; normal function call: count occurrences in args
         (count-free-occurences-in-terms var (fargs term))))))

 ;; Count how many times VAR appears freely in TERMS.
 (defun count-free-occurences-in-terms (var terms)
   (declare (xargs :guard (and (symbolp var)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       0
     (+ (count-free-occurences-in-term var (car terms))
        (count-free-occurences-in-terms var (cdr terms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the variables in VARS that appear at most once in TERM.
(defund vars-that-appear-only-once (vars term)
   (declare (xargs :guard (and (symbol-listp vars)
                               (pseudo-termp term))))
  (if (endp vars)
      nil
    (let ((var (first vars)))
      (if (<= (count-free-occurences-in-term var term) 1)
          (cons var (vars-that-appear-only-once (rest vars) term))
        (vars-that-appear-only-once (rest vars) term)))))

(defthm symbol-listp-of-vars-that-appear-only-once
  (implies (symbol-listp vars)
           (symbol-listp (vars-that-appear-only-once vars term)))
  :hints (("Goal" :in-theory (enable vars-that-appear-only-once))))

(defthm subsetp-equal-of-vars-that-appear-only-once
  (subsetp-equal (vars-that-appear-only-once vars term) vars)
  :hints (("Goal" :in-theory (enable vars-that-appear-only-once))))

(defthm subsetp-equal-of-vars-that-appear-only-once-gen
  (implies (subsetp-equal vars x)
           (subsetp-equal (vars-that-appear-only-once vars term) x))
  :hints (("Goal" :in-theory (enable vars-that-appear-only-once))))

(defthm not-member-equal--of-vars-that-appear-only-once
  (implies (not (member-equal var vars))
           (not (member-equal var (vars-that-appear-only-once vars term))))
  :hints (("Goal" :in-theory (enable vars-that-appear-only-once))))

(defthm no-duplicatesp-equal-of-vars-that-appear-only-once
  (implies (no-duplicatesp-equal vars)
           (no-duplicatesp-equal (vars-that-appear-only-once vars term)))
  :hints (("Goal" :in-theory (enable vars-that-appear-only-once))))
