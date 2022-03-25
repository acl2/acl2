; A tool to turn 'mv-nth of mv-list' terms into mv-lets
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;(include-book "restore-mv-in-branches")
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/fresh-names" :dir :system)
(include-book "kestrel/utilities/non-trivial-bindings" :dir :system)
(include-book "kestrel/utilities/num-return-values-of-fn" :dir :system)

;; This tool turns terms like (mv-nth '0 (mv-list '2 ..)) into MV-LETs.  To do
;; so, it heuristically chooses names to use to catch the multiple values (by
;; analyzing the called function).

;; This tool also turns lambdas into lets, for readability and since it is
;; easier to do it here (the output of this tool is no longer a pseudo-term).

;; TODO: Consider having this also introduce MVs, since subsequent code to do
;; so would have to handle the MV-LETs (and the LETs) introduced here.  Or
;; reconstruct MVs first, since the result is still a pseudo term...

;; TODO: Also reconstruct lambdas with MV variables, such as the one that
;; results from :trans (mv-let (x y) (mv x y) (< x y)).

;; TODO: Write some tests

(local (in-theory (disable function-symbolp)))

(defund cons-nest-ending-in-nilp (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (not (consp x))
      nil
    (if (equal x *nil*)
        t
      (and (consp x)
           (eq 'cons (ffn-symb x))
           (= 2 (len (fargs x)))
           (cons-nest-ending-in-nilp (farg2 x))))))

(defund elements-of-cons-nest-ending-in-nil (x)
  (declare (xargs :guard (and (pseudo-termp x)
                              (cons-nest-ending-in-nilp x))
                  :hints (("Goal" :in-theory (enable cons-nest-ending-in-nilp)))
                  :guard-hints (("Goal" :in-theory (enable cons-nest-ending-in-nilp)))))
  (if (or (not (mbt (cons-nest-ending-in-nilp x))) ; for termination
          (equal x *nil*))
      nil
    (cons (farg1 x)
          (elements-of-cons-nest-ending-in-nil (farg2 x)))))

;; Analyze TERM, which should return multiple values, to try to determine names
;; to use for those values (e.g., if it has an if-branch that is (mv var1
;; var2), return (list var1 var2).  Returns nil upon failure.
(defund return-names-of-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (or (variablep term)
          (fquotep term))
      ;; TODO: Support multiple constant values that have been computed into a constant list?:
      (er hard? 'return-names-of-term "Expected ~x0 to return multiple values.")
    (if (call-of 'if term)
        (if (call-of 'mbt (farg1 term)) ; for (if (mbt ...) <then-branch> <else-branch>), analyze <then-branch>:
            (return-names-of-term (farg2 term))
          (let ((then-res (return-names-of-term (farg2 term)))
                (else-res (return-names-of-term (farg3 term))))
            ;; If either if branch gives a result, use it:
            (or then-res else-res)))
      (if (flambda-applicationp term)
          (return-names-of-term (lambda-body (ffn-symb term)))
        (if (cons-nest-ending-in-nilp term) ;; a cons nest representing the translation of (mv <var1> ... <varn>)
            (let ((vals (elements-of-cons-nest-ending-in-nil term)))
              (if (and (symbol-listp vals)
                       (no-duplicatesp-eq vals))
                  vals
                nil))
          nil ;fail
          )))))

(defthm symbol-listp-of-return-names-of-term
  (symbol-listp (return-names-of-term term))
  :hints (("Goal" :in-theory (enable return-names-of-term))))

;; Try to determine names for the return values of FN, which should return
;; multiple values.
(defund return-names-of-fn (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (not (member-eq fn *stobjs-out-invalid*))
                              (plist-worldp wrld)
                              (function-symbolp fn wrld))))
  (let ((num-return-values (num-return-values-of-fn fn wrld)))
    (if (not (<= 2 num-return-values))
        (er hard? 'return-names-of-fn "Expected ~x0 to return multiple values, but it returns ~x1 value(s)." fn num-return-values)
      (let* ((body (fn-body fn t wrld))
             ;; Changes cons nests to mv calls:
             ;; (body (restore-mv-in-branches body (num-return-values-of-fn fn wrld) nil wrld))
             (names (return-names-of-term body)))
        (if (not names)
            (prog2$ (cw "WARNING: Could not find names for the return values of ~x0.  Using default names.~%" fn)
                    (fresh-var-names num-return-values 'v nil))
          names)))))

(defthm true-listp-of-return-names-of-fn
  (true-listp (return-names-of-fn fn wrld))
  :hints (("Goal" :in-theory (enable return-names-of-fn))))

;; Apply MV-LET to catch the values returned by TERM, which should return
;; RETURNED-VAL-COUNT values, and have the MV-LET return the value
;; corresponding to RETURNED-VAL-NUM.  Preserve any outer lambdas in TERM to
;; become outer lambdas of the result.  For use when only a single one of the
;; multiple values is returned.  The result is not a translated term, since it
;; may contain mv-let (and let):
(defun apply-mv-let-to-term (term returned-val-num returned-val-count wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (natp returned-val-num)
                              (integerp returned-val-count)
                              (<= 2 returned-val-count)
                              (< returned-val-num returned-val-count)
                              (plist-worldp wrld))))
  (if (or (variablep term)
          (fquotep term))
      ;; TODO: Support multiple constant values that have been computed into a constant list?:
      (er hard? 'apply-mv-let-to-term "Expected ~x0 to return ~x1 values." term returned-val-count)
    (let ((fn (ffn-symb term)))
      ;; reconstruct lambdas outside the "core" term:
      (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
          `(let ,(alist-to-doublets (non-trivial-bindings (lambda-formals fn) (fargs term)))
             ,(apply-mv-let-to-term (lambda-body fn) returned-val-num returned-val-count wrld))
        ;; `((lambda ,(lambda-formals fn) ,(apply-mv-let-to-term (lambda-body fn) returned-val-naum returned-val-count wrld))
        ;;   ,@(fargs term))
        ;; we've reached the core term (TODO: What if it's an mv, or the translation of an mv?)
        (if (member-eq fn *stobjs-out-invalid*)
            (er hard? 'apply-mv-let-to-term "Unsupported term: ~x0." term) ;todo: add support for these?
          (if (not (function-symbolp fn wrld))
              (er hard? 'apply-mv-let-to-term "Undefined function: ~x0." fn)
            (let ((fn-value-count (num-return-values-of-fn fn wrld)))
              (if (not (equal fn-value-count returned-val-count))
                  (er hard? 'apply-mv-let-to-term "Expected ~x0 to return ~x1 values, but it returns ~x2 values." term returned-val-count fn-value-count)
                (let* (;; try to generate nice names to catch the value returned:
                       (return-val-names (return-names-of-fn fn wrld))
                       ;; the one value that gets returned by the whole term:
                       (returned-val-name (nth returned-val-num return-val-names)))
                  `(mv-let ,return-val-names
                     ,term
                     (declare (ignore ,@(remove-equal returned-val-name return-val-names)))
                     ,returned-val-name))))))))))

(defun mv-nth-of-mv-list-termp (term)
  (declare (xargs :guard (and (pseudo-termp term))))
  (and (call-of 'mv-nth term) ; example: (mv-nth '0 (mv-list '2 <multi-valued-term>))
       (quotep (farg1 term))
       (natp (unquote (farg1 term)))
       (call-of 'mv-list (farg2 term))
       (quotep (farg1 (farg2 term)))
       (natp (unquote (farg1 (farg2 term))))
       (<= 2 (unquote (farg1 (farg2 term))))
       (< (unquote (farg1 term)) (unquote (farg1 (farg2 term))))))

(mutual-recursion
 ;; The input term is translated, so there won't be any mv-lets.
 ;; TODO: Should we put back any translated mv-lets that we see?
 ;; Note that the result is no longer a translated term (it contains mv-let and let).
 (defund restore-mv-lets-in-term (term wrld)
   (declare (xargs :guard (and (pseudo-termp term)
                               (plist-worldp wrld))
                   :measure (acl2-count term)))
   (if (or (variablep term)
           (fquotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((fn (ffn-symb term))
            ;; handle the args first:
            (new-args (restore-mv-lets-in-terms (fargs term) wrld)))
       (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           ;; Apply to the body and turn the lambda into a let:
           `(let ,(alist-to-doublets (non-trivial-bindings (lambda-formals fn) new-args))
              ,(restore-mv-lets-in-term (lambda-body fn) wrld))
         ;; `((lambda ,(lambda-formals fn) ,(restore-mv-lets-in-term (lambda-body fn) wrld))
         ;;   ,@new-args)
         (if (mv-nth-of-mv-list-termp term)
             (apply-mv-let-to-term (farg2 (farg2 term))
                                   (unquote (farg1 term))
                                   (unquote (farg1 (farg2 term)))
                                   wrld)
           ;; TODO: Dive into IFs?  Other constructs?
           ;; todo: see what letify does with may terms and must terms and consider doing that here)
           ;; just rebuild the function call:
           `(,fn ,@new-args))))))

 (defund restore-mv-lets-in-terms (terms wrld)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (plist-worldp wrld))
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (restore-mv-lets-in-term (first terms) wrld)
           (restore-mv-lets-in-terms (rest terms) wrld)))))
