; A small untranslation pass for reconstructed/surface forms
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; SIMPLE-UNTRANSLATE-IN-TERM walks a Lisp form and applies two readability
;; passes:
;;
;;   1. Self-quoting constants: (quote v) becomes v whenever v is a number,
;;      character, string, keyword, T, or NIL.
;;
;;   2. Arithmetic aliases:
;;        (BINARY-+ a b)  =>  (+ a b)
;;        (BINARY-* a b)  =>  (* a b)
;;        (UNARY--  a)    =>  (- a)
;;        (UNARY-/  a)    =>  (/ a)
;;
;; Other forms pass through structurally.  In particular, LET, LET*, and
;; MV-LET special forms are recognized so that bindings' values and bodies are
;; untranslated while binding-variable names and DECLARE forms pass through
;; unchanged.
;;
;; The function is most useful as a post-pass after RECONSTRUCT-LETS-IN-TERM
;; (see RECONSTRUCT-AND-UNTRANSLATE-TERM for the combined operation), but it
;; is independent and operates on any well-formed Lisp form containing the
;; recognized shapes.  In general the input is NOT a PSEUDO-TERMP (it may
;; contain LET / LET* / MV-LET / DECLARE forms); the output is also a
;; surface-style form.

;; True iff v is a value such that (quote v) may safely be written unquoted in
;; surface syntax.  The same predicate is inlined in UNTRANSLATE1.
(defund self-quoting-valuep (v)
  (declare (xargs :guard t))
  (or (acl2-numberp v)
      (stringp v)
      (characterp v)
      (eq v nil)
      (eq v t)
      (keywordp v)))

(mutual-recursion
 (defund simple-untranslate-in-term (term)
   (declare (xargs :guard t
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (cond
    ((atom term) term)
    ;; (quote v) -> v when v is self-quoting; otherwise leave alone.
    ((and (eq (car term) 'quote)
          (consp (cdr term))
          (null (cddr term)))
     (if (self-quoting-valuep (cadr term))
         (cadr term)
       term))
    ;; (BINARY-+ a b) -> (+ a b)
    ((and (eq (car term) 'binary-+)
          (true-listp term))
     (cons '+ (simple-untranslate-in-terms (cdr term))))
    ;; (BINARY-* a b) -> (* a b)
    ((and (eq (car term) 'binary-*)
          (true-listp term))
     (cons '* (simple-untranslate-in-terms (cdr term))))
    ;; (UNARY-- a) -> (- a)
    ((and (eq (car term) 'unary--)
          (true-listp term))
     (cons '- (simple-untranslate-in-terms (cdr term))))
    ;; (UNARY-/ a) -> (/ a)
    ((and (eq (car term) 'unary-/)
          (true-listp term))
     (cons '/ (simple-untranslate-in-terms (cdr term))))
    ;; (LET bindings . declare-and-body)
    ;; (LET* bindings . declare-and-body)
    ((and (or (eq (car term) 'let)
              (eq (car term) 'let*))
          (consp (cdr term))
          (consp (cddr term))
          (true-listp (cadr term)))
     (cons (car term)
           (cons (simple-untranslate-let-bindings (cadr term))
                 (simple-untranslate-declare-and-body (cddr term)))))
    ;; (MV-LET vars val-form . declare-and-body)
    ((and (eq (car term) 'mv-let)
          (consp (cdr term))
          (consp (cddr term))
          (consp (cdddr term)))
     (list* 'mv-let
            (cadr term)
            (simple-untranslate-in-term (caddr term))
            (simple-untranslate-declare-and-body (cdddr term))))
    ;; Anything else: treat as a function/macro call and walk the arguments.
    ((true-listp term)
     (cons (car term)
           (simple-untranslate-in-terms (cdr term))))
    ;; Improper list (shouldn't happen on well-formed reconstructed terms):
    ;; leave alone.
    (t term)))

 (defund simple-untranslate-in-terms (terms)
   (declare (xargs :guard t
                   :measure (acl2-count terms)))
   (if (atom terms)
       terms
     (cons (simple-untranslate-in-term (car terms))
           (simple-untranslate-in-terms (cdr terms)))))

 ;; Walks a let-bindings list ((v1 e1) (v2 e2) ...), untranslating each binding's
 ;; value expression while leaving the variable name unchanged.  Tolerates a
 ;; non-list tail.
 (defund simple-untranslate-let-bindings (bindings)
   (declare (xargs :guard t
                   :measure (acl2-count bindings)))
   (if (atom bindings)
       bindings
     (cons (let ((binding (car bindings)))
             (if (and (consp binding) (consp (cdr binding)))
                 (cons (car binding)
                       (cons (simple-untranslate-in-term (cadr binding))
                             (cddr binding)))
               binding))
           (simple-untranslate-let-bindings (cdr bindings)))))

 ;; Walks a list of forms appearing after the bindings of a LET/LET*/MV-LET:
 ;; DECLARE forms pass through verbatim; everything else is untranslated.
 (defund simple-untranslate-declare-and-body (forms)
   (declare (xargs :guard t
                   :measure (acl2-count forms)))
   (if (atom forms)
       forms
     (cons (let ((form (car forms)))
             (if (and (consp form) (eq (car form) 'declare))
                 form
               (simple-untranslate-in-term form)))
           (simple-untranslate-declare-and-body (cdr forms))))))

(verify-guards simple-untranslate-in-term
  :hints (("Goal" :in-theory (enable simple-untranslate-in-term
                                     simple-untranslate-in-terms
                                     simple-untranslate-let-bindings
                                     simple-untranslate-declare-and-body))))
