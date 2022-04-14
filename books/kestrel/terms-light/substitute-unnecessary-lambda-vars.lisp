; A tool to substitute away vars that are needlessly lambda-bound
;
; Copyright (C) 2014-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; TODO: Prove that this preserves the meaning of terms

(include-book "kestrel/utilities/symbol-term-alistp" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "free-vars-in-term")
(include-book "sublis-var-simple")
(include-book "non-trivial-formals")
(local (include-book "kestrel/utilities/terms" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

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

;walk down the formals and the args in sync
(defun pair-given-formals-with-args (formals args formals-to-pair-with-args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp args)
                              (true-listp formals-to-pair-with-args))))
  (if (endp formals)
      nil
    (let ((formal (first formals)))
      (if (member-eq formal formals-to-pair-with-args)
          (acons formal (first args) (pair-given-formals-with-args (rest formals) (rest args) formals-to-pair-with-args))
        (pair-given-formals-with-args (rest formals) (rest args) formals-to-pair-with-args)))))

(defthm symbol-term-alistp-of-acons
  (equal (symbol-term-alistp (acons key val alist))
         (and (symbolp key)
              (pseudo-termp val)
              (symbol-term-alistp alist)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm symbol-term-alistp-of-pair-given-formals-with-args
  (implies (and (symbol-listp formals)
                (pseudo-term-listp args))
           (symbol-term-alistp (pair-given-formals-with-args formals args formals-to-pair-with-args)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm symbol-alistp-of-pair-given-formals-with-args
  (implies (symbol-listp formals)
           (symbol-alistp (pair-given-formals-with-args formals args formals-to-pair-with-args)))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

(defund keep-args-for-non-dropped-formals (formals args dropped-formals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp args)
                              (true-listp dropped-formals))))
  (if (endp formals)
      nil
    (let ((formal (first formals)))
      (if (member-eq formal dropped-formals)
          (keep-args-for-non-dropped-formals (rest formals) (rest args) dropped-formals)
        (cons (first args) (keep-args-for-non-dropped-formals (rest formals) (rest args) dropped-formals))))))

(defthm pseudo-term-listp-of-keep-args-for-non-dropped-formals
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (keep-args-for-non-dropped-formals formals args dropped-formals)))
  :hints (("Goal" :in-theory (enable keep-args-for-non-dropped-formals))))

(defthm len-of-keep-args-for-non-dropped-formals
  (equal (len (keep-args-for-non-dropped-formals formals args dropped-formals))
         (len (set-difference-equal formals dropped-formals)))
  :hints (("Goal" :in-theory (enable keep-args-for-non-dropped-formals))))

;todo: reorder args
(defun get-args-for-formals (formals args target-formals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp args)
                              (TRUE-LISTP target-formals))))
  (if (endp formals)
      nil
    (let ((formal (first formals)))
      (if (member-eq formal target-formals)
          (cons (first args) (get-args-for-formals (rest formals) (rest args) target-formals))
        (get-args-for-formals (rest formals) (rest args) target-formals)))))

(defthm pseudo-term-listp-of-get-args-for-formals
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (get-args-for-formals formals args target-formals))))

(defun vars-bound-to-themselves (formals actuals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp actuals))))
  (if (endp formals)
      nil
    (let ((formal (first formals))
          (actual (first actuals)))
      (if (eq formal actual)
          (cons formal (vars-bound-to-themselves (rest formals)
                                                 (rest actuals)))
        (vars-bound-to-themselves (rest formals)
                                  (rest actuals))))))

;; Returns the VARS whose corresponding terms in VAR-TERM-ALIST do not mention
;; any of the VARS-TO-AVOID.
(defund vars-expressible-without-clashes (vars var-term-alist vars-to-avoid)
  (declare (xargs :guard (and (symbol-listp vars)
                              (symbol-term-alistp var-term-alist)
                              (symbol-listp vars-to-avoid))))
  (if (endp vars)
      nil
    (let* ((var (first vars))
           (term (lookup-eq-safe var var-term-alist))
           (term-vars (free-vars-in-term term)))
      (if (not (intersection-eq term-vars vars-to-avoid)) ; ensure no clash
          (cons var (vars-expressible-without-clashes (rest vars) var-term-alist vars-to-avoid))
        (vars-expressible-without-clashes (rest vars) var-term-alist vars-to-avoid)))))

;TODO: rename this and similar things to mention lambdas, not lets (later we may handle non-pseudo-terms that still include lets)
(mutual-recursion
 (defun substitute-unnecessary-lambda-vars-in-term (term print)
   (declare (xargs :measure (acl2-count term)
                   :guard (pseudo-termp term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (quotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (substitute-unnecessary-lambda-vars-in-terms args print)) ;process the args first
            (fn (ffn-symb term)))
       (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((vars-in-term (free-vars-in-term term)) ;todo: just get the vars from the (original) args (prove that this function doesn't change free vars)
                  (vars (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ;;apply recursively to the lambda body:
                  (lambda-body (substitute-unnecessary-lambda-vars-in-term lambda-body print))
                  (var-term-alist (pairlis$ vars args))
                  (vars-bound-to-themselves (vars-bound-to-themselves vars args))
                  (vars-not-bound-to-themselves (set-difference-eq vars vars-bound-to-themselves))
                  ;; We substitute for a lambda var if:
                  ;; 1) It appears only once in the lambda-body
                  ;; and
                  ;; 2) It is not bound to itself (vars bound to themselves
                  ;; don't really "count against" us, since lambdas must be closed)
                  ;; and
                  ;; 3) It is bound to a term that does not mention any variables that are bound by
                  ;; the lambda, except variables that are bound to themselves.  This prevents clashes.
                  (vars-to-maybe-drop (vars-that-appear-only-once vars lambda-body))
                  (vars-to-maybe-drop (set-difference-eq vars-to-maybe-drop vars-bound-to-themselves))
                  (vars-to-drop (vars-expressible-without-clashes vars-to-maybe-drop var-term-alist vars-not-bound-to-themselves))

                  ;; OLD:
                  ;; Recall that in ACL2 lambdas are always closed.  A
                  ;; formal to be dropped is any lambda formal that appears
                  ;; only once in the lambda body and whose corresponding arg
                  ;; is anything other than just the formal.  (TODO: Could
                  ;; also drop if the formal is bound to a variable [or
                  ;; constant?].)  We then substitute the actual for the
                  ;; formal in the lambda body.  To maintain closedness of
                  ;; the lambda, any vars mentioned in the arg will need to
                  ;; be added as lambda formals and corresponding args must
                  ;; be added too (unless they are already present).
                  ;; (formals-to-drop (vars-not-bound-to-themselves (vars-that-appear-only-once lambda-formals lambda-body)
                  ;;                                                args))
                  (new-vars (set-difference-eq vars vars-to-drop))
                  ;; We add to the formal list any variables that are mentioned in the actuals for the formals being dropped, since those vars now appear in the lambda body.  We also add corresponding actuals binding those variables to themselves.
                  (args-for-vars-to-drop (get-args-for-formals vars args vars-to-drop))
                  (new-vars-to-add (set-difference-eq (free-vars-in-terms args-for-vars-to-drop)
                                                      new-vars))
                  (new-vars (append new-vars new-vars-to-add))
                  ;; partially beta-reduce (no longer mentions formals-to-drop)
                  (new-lambda-body (sublis-var-simple (pair-given-formals-with-args vars args vars-to-drop) lambda-body))
                  (new-lambda-args (keep-args-for-non-dropped-formals vars args vars-to-drop))
                  (new-lambda-args (append new-lambda-args new-vars-to-add)) ;bind any new formals to themselves
                  (result (if new-vars
                              ;; If there are remaining formals:
                              (if (equal new-vars new-lambda-args)
                                  ;; all formals are bound to themselves, so no need for a lambda:
                                  new-lambda-body
                                `((lambda (,@new-vars) ,new-lambda-body) ,@new-lambda-args))
                            ;; No remaining formals, so don't make a ((lambda nil ...) ...)
                            new-lambda-body))
                  (vars-in-result (free-vars-in-term result)))
             (progn$
              (and print
                   (cw "Removing unnecessary lambda vars: ~x3.~%Lambda vars: ~x0~%Body: ~x1~%Args: ~x2~%Result: ~x4~%~%" vars lambda-body args vars-to-drop result))
              (and (or (not (subsetp-eq vars-in-term vars-in-result))
                       (not (subsetp-eq vars-in-result vars-in-term)))
                   (cw "ERROR: Var mismatch!.  Old term: ~x0.  New term: ~x1.~%" term result))
              result))
         ;;not a lambda application, so just rebuild the function call:
         `(,fn ,@args)))))

 (defun substitute-unnecessary-lambda-vars-in-terms (terms print)
   (declare (xargs :measure (acl2-count terms)
                   :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (substitute-unnecessary-lambda-vars-in-term (first terms) print)
           (substitute-unnecessary-lambda-vars-in-terms (rest terms) print)))))

(make-flag flag-substitute-unnecessary-lambda-vars-in-term substitute-unnecessary-lambda-vars-in-term)

;TODO: Automate some of this?

;; (defthm len-of-substitute-unnecessary-lambda-vars-in-terms
;;   (equal (len (substitute-unnecessary-lambda-vars-in-terms terms print))
;;          (len terms))
;;   :hints (("Goal" :induct (len terms)
;;            :in-theory (enable len substitute-unnecessary-lambda-vars-in-terms))))

;; (defthm consp-of-substitute-unnecessary-lambda-vars-in-terms
;;   (equal (consp (substitute-unnecessary-lambda-vars-in-terms terms print))
;;          (consp terms))
;;   :hints (("Goal" :induct (len terms)
;;            :in-theory (enable len substitute-unnecessary-lambda-vars-in-terms))))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term
  (defthm pseudo-termp-of-substitute-unnecessary-lambda-vars-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (substitute-unnecessary-lambda-vars-in-term term print)))
    :flag substitute-unnecessary-lambda-vars-in-term)
  (defthm pseudo-term-listp-of-substitute-unnecessary-lambda-vars-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (substitute-unnecessary-lambda-vars-in-terms terms print)))
    :flag substitute-unnecessary-lambda-vars-in-terms))

(verify-guards substitute-unnecessary-lambda-vars-in-term)
