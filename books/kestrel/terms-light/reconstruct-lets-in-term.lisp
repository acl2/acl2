; A tool to turn lambdas into lets
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Put in ignore declares for LETs and MV-LETS when needed.
;; TODO: Consider combining nested LETs into LET*s.
;; TODO: Consider having this also do some untranslation.

(include-book "non-trivial-formals")
(include-book "kestrel/utilities/non-trivial-bindings" :dir :system)
(include-book "kestrel/lists-light/prefixp-def" :dir :system)
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(local (in-theory (disable mv-nth)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: move to lists-light

;; Tests whether L1 is a suffix of L2.
(defund list-suffixp (l1 l2)
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

(defund numbered-mv-nthp (term n core)
  (declare (xargs :guard (natp n)))
  (and (consp term)
       (eq 'mv-nth (ffn-symb term))
       (true-listp term)
       (= 2 (len (fargs term)))
       (quotep (fargn term 1))
       (= 1 (len (fargs (fargn term 1)))) ; to allow unquoting
       (equal (unquote (fargn term 1)) n)
       (equal (fargn term 2) core)))

;; Check that the TERMS and (mv-nth '0 <core>), (mv-nth '1 <core>), etc.
;; except allow HIDES to appear around the mv-nths.
;; TODO: Consider allowing gaps in the numbering, for when some values got dropped.
(defund numbered-mv-nthsp (terms curr core)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (natp curr)
                              (variablep core))))
  (if (endp terms)
      t
    (let ((term (first terms)))
      (and (or (numbered-mv-nthp term curr core)
               (and (consp term)
                    (eq 'hide (ffn-symb term))
                    (= 1 (len (fargs term)))
                    (numbered-mv-nthp (fargn term 1) curr core)))
           (numbered-mv-nthsp (rest terms) (+ 1 curr) core)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (mv-let (x y) <term> <body>)
;; translates to:
;; ((lambda (mv ...extra-body-vars...)
;;    ((lambda (x y ...extra-body-vars...) <translated-body>)
;;     (mv-nth '0 mv)
;;     (mv-nth '1 mv)
;;     ...extra-body-vars...))
;;   <translated-term>
;;   ...extra-body-vars...)
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
                (and (equal extra-body-vars (rest outer-lambda-args))
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

;; Extracts the extra body vars (bound to themselves) in a translated mv-let.
(defun extra-body-vars-of-translated-mv-let (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (translated-mv-letp term))))
  (let* ((outer-lambda (ffn-symb term))
         (outer-lambda-formals (lambda-formals outer-lambda))
         (extra-body-vars (rest outer-lambda-formals)))
    extra-body-vars))

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

(defund strip-hides-from-vals-for-keys (keys alist)
  (declare (xargs :guard (and (symbol-listp keys)
                              (alistp alist))))
  (if (endp alist)
      nil
    (let* ((pair (first alist))
           (key (car pair))
           (val (cdr pair)))
      (if (and (member-eq key keys)
               (consp val)
               (eq 'hide (ffn-symb val))
               (consp (fargs val)))
          (acons key (cadr val) (strip-hides-from-vals-for-keys keys (rest alist)))
        (cons pair (strip-hides-from-vals-for-keys keys (rest alist)))))))

(defthm alistp-of-strip-hides-from-vals-for-keys
  (implies (alistp alist)
           (alistp (strip-hides-from-vals-for-keys keys alist)))
  :hints (("Goal" :in-theory (enable strip-hides-from-vals-for-keys))))

;; TODO: Remove hides introduced for ignored vars:
(mutual-recursion
 ;; Reconstructs LETs and MV-LETs in term.
 ;; Returns (mv term free-vars).
 ;; Note that the result is no longer a translated term (pseudo-termp).
 (defund reconstruct-lets-in-term-aux (term)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (if (variablep term)
       (mv term (list term))
     (if (fquotep term)
         (mv term nil)
       (if (translated-mv-letp term)
           ;; It's (the translation of) an MV-LET:
           ;; Apply recursively to the multi-valued term:
           (mv-let (new-mv-term mv-term-vars)
             (reconstruct-lets-in-term-aux (term-of-translated-mv-let term))
             ;; Apply recursively to the MV-LET body:
             (mv-let (new-body-term body-vars)
               (reconstruct-lets-in-term-aux (body-of-translated-mv-let term))
               (let* ((vars (vars-of-translated-mv-let term))
                      (ignored-vars (set-difference-eq vars body-vars)))
                 (mv `(mv-let ,vars
                        ,new-mv-term
                        ;; maybe put in an ignore declare:
                        ,@(and ignored-vars `((declare (ignore ,@ignored-vars))))
                        ,new-body-term)
                     ;; The lambda should be closed, so the free vars are from the args, which are the mv-term and the extra-body-vars:
                     (union-eq mv-term-vars
                               (extra-body-vars-of-translated-mv-let term))))))
         (let* ((fn (ffn-symb term)))
           (mv-let (new-args args-free-vars)
             (reconstruct-lets-in-terms-aux (fargs term))
             (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
                 (mv-let (new-lambda-body lambda-body-vars)
                   (reconstruct-lets-in-term-aux (lambda-body fn))
                   (let* ((lambda-formals (lambda-formals fn))
                          ;; Only need to ignore non-trival formals, as trivial ones won't even show up in the LET:
                          (ignored-vars (set-difference-eq (non-trivial-formals lambda-formals new-args) lambda-body-vars)))
                     (mv `(let ,(alist-to-doublets (strip-hides-from-vals-for-keys ignored-vars (non-trivial-bindings lambda-formals new-args))) ; HIDE is introduced when a let with ignored vars is translated
                            ;; maybe put in an ignore declare:
                            ,@(and ignored-vars `((declare (ignore ,@ignored-vars))))
                            ,new-lambda-body)
                         ;; the lambda should be closed, so we don't include the lambda-body-vars:
                         args-free-vars)))
               ;; not a lambda application, so just rebuild the function call:
               (mv `(,fn ,@new-args)
                   args-free-vars))))))))

 ;; Returns (mv terms all-free-vars).
 (defund reconstruct-lets-in-terms-aux (terms)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :measure (acl2-count terms)))
   (if (endp terms)
       (mv nil nil)
     (mv-let (new-first-term first-term-free-vars)
       (reconstruct-lets-in-term-aux (first terms))
       (mv-let (new-rest-terms rest-terms-free-vars)
         (reconstruct-lets-in-terms-aux (rest terms))
         (mv (cons new-first-term new-rest-terms)
             (union-eq first-term-free-vars rest-terms-free-vars)))))))

(make-flag reconstruct-lets-in-term-aux)

(defthm-flag-reconstruct-lets-in-term-aux
  (defthm symbol-listp-of-mv-nth-1-of-reconstruct-lets-in-term-aux
    (implies (pseudo-termp term)
             (symbol-listp (mv-nth 1 (reconstruct-lets-in-term-aux term))))
    :flag reconstruct-lets-in-term-aux)
  (defthm symbol-listp-of-mv-nth-1-of-reconstruct-lets-in-terms-aux
    (implies (pseudo-term-listp terms)
             (symbol-listp (mv-nth 1 (reconstruct-lets-in-terms-aux terms))))
    :flag reconstruct-lets-in-terms-aux)
  :hints (("Goal" :in-theory (enable reconstruct-lets-in-term-aux
                                     reconstruct-lets-in-terms-aux))))

(defthm-flag-reconstruct-lets-in-term-aux
  (defthm true-listp-of-mv-nth-0-of-reconstruct-lets-in-terms-aux
    (true-listp (mv-nth 0 (reconstruct-lets-in-terms-aux terms)))
    :flag reconstruct-lets-in-terms-aux)
  :skip-others t
  :hints (("Goal" :in-theory (enable reconstruct-lets-in-terms-aux))))

(verify-guards reconstruct-lets-in-term-aux
  :hints (("Goal" :expand ((pseudo-termp term))
           :in-theory (enable true-listp-when-symbol-listp pseudo-termp))))

;; Reconstructs LETs and MV-LETs in term. Returns a term equivalent to TERM.
;; The result is usually not a pseudo-term, because it contains LETs and/or
;; MV-LETs.
(defund reconstruct-lets-in-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (mv-let (term vars)
    (reconstruct-lets-in-term-aux term)
    (declare (ignore vars))
    term))
