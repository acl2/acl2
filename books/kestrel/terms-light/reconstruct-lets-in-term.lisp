; A tool to turn lambdas into lets
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Put in ignore declares for LETs and MV-LETS when needed.
;; TODO: Consider combining nested LETs into LET*s.

(include-book "kestrel/utilities/non-trivial-bindings" :dir :system)
(include-book "kestrel/lists-light/prefixp-def" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: move to lists-light

;; Tests whether L1 is a suffix of L2.
(defun list-suffixp (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2))))
  (prefixp (reverse l1) (reverse l2)))

;; (list-suffixp nil '(a b c))
;; (list-suffixp '(c) '(a b c))
;; (list-suffixp '(a b c) '(a b c))
;; (not (list-suffixp '(a b c) '(b c)))
;; (not (list-suffixp '(a) '(a b c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Factor out this mv-let material into a separate book:

;; Check that the TERMS and (mv-nth '0 <core>), (mv-nth '1 <core>), etc.
(defund numbered-mv-nthsp (terms curr core)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (natp curr)
                              (variablep core))))
  (if (endp terms)
      t
    (let ((term (first terms)))
      (and (consp term)
           (eq 'mv-nth (ffn-symb term))
           (= 2 (len (fargs term)))
           (quotep (fargn term 1))
           (equal (unquote (fargn term 1)) curr)
           (equal (fargn term 2) core)
           (numbered-mv-nthsp (rest terms) (+ 1 curr) core)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (mv-let (x y) <term> <body>)
;; translates to:
;; ((lambda (mv ...other-body-vars...)
;;    ((lambda (x y ...other-body-vars...) <translated-body>)
;;     (mv-nth '0 mv)
;;     (mv-nth '1 mv)
;;     ...other-body-vars...))
;;   <translated-term>
;;   ...other-body-vars...)
(defun translated-mv-letp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (and (consp term)
       (flambda-applicationp term)
       (let* ((outer-lambda (ffn-symb term))
              (outer-lambda-args (fargs term))
              (outer-lambda-formals (lambda-formals outer-lambda))
              )
         ;; could check that the <term> is multi-valued, but we'd need a world
         (and (<= 1 (len outer-lambda-formals)) ; a single formal for the mv, followed by any extra vars in the body
              (let ((mv-formal (first outer-lambda-formals)) ;; usually named mv or mv0 or mv1, etc.
                    (extra-body-vars (rest outer-lambda-formals))
                    (outer-lambda-body (lambda-body outer-lambda)))
                (and (list-suffixp extra-body-vars outer-lambda-args)
                     (consp outer-lambda-body)
                     (flambda-applicationp outer-lambda-body)
                     (let* ((inner-lambda (ffn-symb outer-lambda-body))
                            (inner-lambda-args (fargs outer-lambda-body))
                            (inner-lambda-formals (lambda-formals inner-lambda)))
                       (and (list-suffixp extra-body-vars inner-lambda-formals)
                            (<= (+ (len extra-body-vars) 2) (len inner-lambda-formals))
                            (list-suffixp extra-body-vars inner-lambda-args)
                            (numbered-mv-nthsp (take (- (len inner-lambda-args) (len extra-body-vars)) inner-lambda-args)
                                               0
                                               mv-formal)))))))))

;; Extracts the vars from a translated mv-let.
(defun vars-of-translated-mv-let (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (translated-mv-letp term))))
  (let* ((outer-lambda (ffn-symb term))
         (outer-lambda-body (lambda-body outer-lambda))
         (outer-lambda-formals (lambda-formals outer-lambda))
         (extra-body-vars (rest outer-lambda-formals))
         (inner-lambda (ffn-symb outer-lambda-body))
         (inner-lambda-formals (lambda-formals inner-lambda)))
    (take (- (len inner-lambda-formals) (len extra-body-vars))
          inner-lambda-formals)))

;; Extracts the multi-valued term from a translated mv-let.
(defun term-of-translated-mv-let (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (translated-mv-letp term))))
  (first (fargs term)))

;; Extracts the body from a translated mv-let.
(defun body-of-translated-mv-let (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (translated-mv-letp term))))
  (let ((outer-lambda (ffn-symb term)))
    (let ((outer-lambda-body (lambda-body outer-lambda)))
      (let ((inner-lambda (ffn-symb outer-lambda-body)))
        (lambda-body inner-lambda)))))

(mutual-recursion
 ;; Reconstructs LETs and MV-LETs in term.
 ;; Note that the result is no longer a translated term (pseudo-termp).
 (defund reconstruct-lets-in-term-aux (term)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)))
   (if (or (variablep term)
           (fquotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (if (translated-mv-letp term)
         `(mv-let ,(vars-of-translated-mv-let term)
           ,(reconstruct-lets-in-term-aux (term-of-translated-mv-let term))
           ,(reconstruct-lets-in-term-aux (body-of-translated-mv-let term)))
       (let* ((fn (ffn-symb term))
              (new-args (reconstruct-lets-in-terms-aux (fargs term))))
         (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
             `(let ,(alist-to-doublets (non-trivial-bindings (lambda-formals fn) new-args))
                ,(reconstruct-lets-in-term-aux (lambda-body fn)))
           ;; not a lambda application, so just rebuild the function call:
           `(,fn ,@new-args))))))

 (defund reconstruct-lets-in-terms-aux (terms)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-lets-in-term-aux (first terms))
           (reconstruct-lets-in-terms-aux (rest terms))))))

(defund reconstruct-lets-in-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (reconstruct-lets-in-term-aux term))
