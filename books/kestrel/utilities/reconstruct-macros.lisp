; Utilities to reconstruct macro calls (as in untranslate)
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides various functions, and a top-level one that combines them,
; to reconstruct certain kinds of untranslated terms
; from their translated counterparts.
; The functionality provided by this file
; should be subsumed by the built-in UNTRANSLATE function.
; However, the latter is in program mode,
; while the functions in this file are in logic mode.
; For this reason, this file may serve if, in the future,
; we want to build a logic-mode variant of UNTRANSLATE.
; It would be much preferable to put UNTRANSLATE in logic mode instead,
; so if and when that happens, this file should be probably removed.
; However, if putting UNTRANSLATE in logic mode
; turns out to be very difficult or laborious,
; we may consider building a (more limited) version in logic mode.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;; This file contains candidate utilities to untranslate terms,
;;;; reverse certain translations (e.g. macro expansions)
;;;; that ACL2 performs on terms entered by the user.

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "std/lists/sets" :dir :system)
(include-book "std/lists/append" :dir :system)
(include-book "tools/flag" :dir :system)
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

(defund gather-args (op args)
  (declare (xargs :guard (and (symbolp op)
                              (not (eq 'quote op))
                              (pseudo-term-listp args))))
  (if (endp args)
      nil
    (let ((arg (first args)))
      (append (if (call-of op arg)
                  (gather-args op (fargs arg)) ;overkill?
                (list arg))
              (gather-args op (rest args))))))

(defthm pseudo-term-listp-of-gather-args
  (implies (and (pseudo-term-listp args)
                (not (eq 'quote op))
                (symbolp op))
           (pseudo-term-listp (gather-args op args)))
  :hints (("Goal" :in-theory (enable gather-args))))

;;; Reconstruct ORs that may have been lost in macro expansion.
;;; (OR X Y) is expanded to (IF X X Y),
;;; so we look for IF terms of that form and we contract them back.
;;; Also flatten nexted applications,
;;; e.g. (IF X X (IF Y Y Z)) becomes (OR X Y Z).

(mutual-recursion

 (defun reconstruct-or-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil)) ; proved below
   ;; no change if variable or constant:
   (if (or (variablep term)
           (quotep term))
       term
     ;; apply reconstruction to function and arguments:
     (let* ((fn (ffn-symb term))
            (new-args (reconstruct-or-in-terms (fargs term))))
       (if (consp fn)                                ; lambda
           `((lambda ,(second fn)                    ; formals
               ,(reconstruct-or-in-term (third fn))) ; body
             ,@new-args)
         (if (and (eq fn 'if)
                  (equal (first new-args) (second new-args)))
             ;; turn (IF X X Y) into OR:
             `(or ,@(gather-args 'or (list (first new-args) (third new-args))))
           ;; flatten any nested OR:
           (if (eq fn 'or)
               `(or ,@(gather-args 'or new-args))
             (cons fn new-args)))))))

 (defun reconstruct-or-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-or-in-term (car terms))
           (reconstruct-or-in-terms (cdr terms))))))

(make-flag flag-reconstruct-or-in-term
           reconstruct-or-in-term)

(defthm-flag-reconstruct-or-in-term

  (defthm pseudo-termp-reconstruct-or-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (reconstruct-or-in-term term)))
    :flag reconstruct-or-in-term)

  (defthm pseudo-term-listp-reconstruct-or-in-terms
    (implies (pseudo-term-listp terms)
             (and (pseudo-term-listp (reconstruct-or-in-terms terms))
                  (equal (len (reconstruct-or-in-terms terms))
                         (len terms))))
    :flag reconstruct-or-in-terms))

(verify-guards reconstruct-or-in-term)

;;; Reconstruct ANDs that may have been lost in macro expansion.
;;; (AND X Y) is expanded to (IF X Y NIL),
;;; so we look for IF terms of that form and we contract them back.
;;; Also flatten nexted applications,
;;; e.g. (IF X (IF Y Z NIL)) becomes (AND X Y Z).

(mutual-recursion

 (defun reconstruct-and-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil)) ; proved below
   ;; no change if variable or constant:
   (if (or (variablep term)
           (quotep term))
       term
     ;; apply reconstruction to function and arguments:
     (let* ((fn (ffn-symb term))
            (new-args (reconstruct-and-in-terms (fargs term))))
       (if (consp fn)                                 ; lambda
           `((lambda ,(second fn)                     ; formals
               ,(reconstruct-and-in-term (third fn))) ; body
             ,@new-args)
         (if (and (eq fn 'if)
                  (or (equal *nil* (third new-args))
                      ;; in case we had unquoted NIL previously:
                      (equal 'nil (third new-args))))
             ;; turn IF of (IF X Y NIL) into AND:
             `(and ,@(gather-args 'and (list (first new-args) (second new-args))))
           ;; flatten any nested AND:
           (if (eq fn 'and)
               `(and ,@(gather-args 'and new-args))
             (cons fn new-args)))))))

 (defun reconstruct-and-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-and-in-term (car terms))
           (reconstruct-and-in-terms (cdr terms))))))

(make-flag flag-reconstruct-and-in-term
           reconstruct-and-in-term)

(defthm-flag-reconstruct-and-in-term

  (defthm pseudo-termp-reconstruct-and-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (reconstruct-and-in-term term)))
    :flag reconstruct-and-in-term)

  (defthm pseudo-term-listp-reconstruct-and-in-terms
    (implies (pseudo-term-listp terms)
             (and (pseudo-term-listp (reconstruct-and-in-terms terms))
                  (equal (len (reconstruct-and-in-terms terms))
                         (len terms))))
    :flag reconstruct-and-in-terms))

(verify-guards reconstruct-and-in-term)

;;; Reconstruct +s that may have been lost in macro expansion.
;;; (+ X Y) is expanded to (BINARY-+ X Y),
;;; so we look for BINARY-+ terms of that form and we contract them back.
;;; Also flatten nested applications,
;;; e.g. (BINARY-+ X (BINARY-+ Y Z)) becomes (+ X Y Z).

(mutual-recursion

 (defun reconstruct-+-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil)) ; proved below
   ;; no change if variable or constant:
   (if (or (variablep term)
           (quotep term))
       term
     ;; apply reconstruction to function and arguments:
     (let* ((fn (ffn-symb term))
            (new-fn (if (consp fn) ; lambda
                        (list 'lambda
                              (second fn) ; formals
                              (reconstruct-+-in-term (third fn))) ; body
                      ;; turn BINARY-+ into +:
                      (if (eq fn 'binary-+)
                          '+
                        fn)))
            (new-args (reconstruct-+-in-terms (rest term))))
       ;; flatten any nested +:
       (if (eq new-fn '+)
           `(+ ,@(gather-args '+ new-args))
         (cons new-fn new-args)))))

 (defun reconstruct-+-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-+-in-term (car terms))
           (reconstruct-+-in-terms (cdr terms))))))

(make-flag flag-reconstruct-+-in-term
           reconstruct-+-in-term)

(defthm-flag-reconstruct-+-in-term

  (defthm pseudo-termp-reconstruct-+-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (reconstruct-+-in-term term)))
    :flag reconstruct-+-in-term)

  (defthm pseudo-term-listp-reconstruct-+-in-terms
    (implies (pseudo-term-listp terms)
             (and (pseudo-term-listp (reconstruct-+-in-terms terms))
                  (equal (len (reconstruct-+-in-terms terms))
                         (len terms))))
    :flag reconstruct-+-in-terms))

(verify-guards reconstruct-+-in-term)

;;; Reconstruct *s that may have been lost in macro expansion.
;;; (* X Y) is expanded to (BINARY-* X Y),
;;; so we look for BINARY-* terms of that form and we contract them back.
;;; Also flatten nested applications,
;;; e.g. (BINARY-* X (BINARY-* Y Z)) becomes (* X Y Z).

(mutual-recursion

 (defun reconstruct-*-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil)) ; proved below
   ;; no change if variable or constant:
   (if (or (variablep term)
           (quotep term))
       term
     ;; apply reconstruction to function and arguments:
     (let* ((fn (ffn-symb term))
            (new-fn (if (consp fn) ; lambda
                        (list 'lambda
                              (second fn) ; formals
                              (reconstruct-*-in-term (third fn))) ; body
                      ;; turn BINARY-* into *:
                      (if (eq fn 'binary-*)
                          '*
                        fn)))
            (new-args (reconstruct-*-in-terms (rest term))))
       ;; flatten any nested *:
       (if (eq new-fn '*)
           `(* ,@(gather-args '* new-args))
         (cons new-fn new-args)))))

 (defun reconstruct-*-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-*-in-term (car terms))
           (reconstruct-*-in-terms (cdr terms))))))

(make-flag flag-reconstruct-*-in-term
           reconstruct-*-in-term)

(defthm-flag-reconstruct-*-in-term

  (defthm pseudo-termp-reconstruct-*-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (reconstruct-*-in-term term)))
    :flag reconstruct-*-in-term)

  (defthm pseudo-term-listp-reconstruct-*-in-terms
    (implies (pseudo-term-listp terms)
             (and (pseudo-term-listp (reconstruct-*-in-terms terms))
                  (equal (len (reconstruct-*-in-terms terms))
                         (len terms))))
    :flag reconstruct-*-in-terms))

(verify-guards reconstruct-*-in-term)

;;; Reconstruct <=s that may have been lost in macro expansion.
;;; (<= X Y) is expanded to (NOT (< Y X)),
;;; so we look for terms of the form (NOT (< ...)) and we contract them back.
;;; Note that (>= X Y) is expanded to (NOT (< X Y)),
;;; so a term of the form (NOT (< ...)) could result from expanding <= or >=;
;;; we pick <= for this reconstruction.

(mutual-recursion

 (defund reconstruct-<=-in-term (term)
   (declare (xargs :guard (pseudo-termp term)))
   ;; no change if term is variable or constant:
   (if (or (variablep term)
           (quotep term))
       term
     ;; if not variable or constant, term must be function application:
     (let ((fn (ffn-symb term)))
       ;; turn (NOT (< X Y)) into (<= Y X) and reconstruct <=s in X and Y:
       (if (and (eq fn 'not)
                (let ((not-arg (farg1 term)))
                  (and (consp not-arg)
                       (eq (ffn-symb not-arg) '<))))
           (let ((not-arg (farg1 term)))
             (list '<=
                   (reconstruct-*-in-term (farg2 not-arg))
                   (reconstruct-*-in-term (farg1 not-arg))))
         ;; reconstruct <=s in subterms:
         (let* ((new-fn (if (consp fn) ; lambda term
                            (list 'lambda
                                  (second fn) ; formals
                                  (reconstruct-<=-in-term (third fn)))
                          fn)) ; function symbol
                (new-args (reconstruct-<=-in-terms (rest term))))
           (cons new-fn new-args))))))

 (defund reconstruct-<=-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-<=-in-term (car terms))
           (reconstruct-<=-in-terms (cdr terms))))))

(make-flag flag-reconstruct-<=-in-term
           reconstruct-<=-in-term)

(defthm-flag-reconstruct-<=-in-term

  (defthm pseudo-termp-reconstruct-<=-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (reconstruct-<=-in-term term)))
    :flag reconstruct-<=-in-term)

  (defthm pseudo-term-listp-reconstruct-<=-in-terms
    (implies (pseudo-term-listp terms)
             (and (pseudo-term-listp (reconstruct-<=-in-terms terms))
                  (equal (len (reconstruct-<=-in-terms terms))
                         (len terms))))
    :flag reconstruct-<=-in-terms)
  :hints (("Goal" :in-theory (enable reconstruct-<=-in-term reconstruct-<=-in-terms))))

;;; Reconstruct unary -s that may have been lost in macro expansion.
;;; (- X) is expanded to (UNARY-- X),
;;; so we look for terms of the form (UNARY-- ...) and we contract them back.

(mutual-recursion

 (defund reconstruct-unary---in-term (term)
   (declare (xargs :guard (pseudo-termp term)))
   ;; no change if term is variable or constant:
   (if (or (variablep term)
           (quotep term))
       term
     ;; turn UNARY-- into - and apply reconstruction to arguments:
     (let* ((fn (ffn-symb term))
            (new-fn (if (consp fn) ; lambda
                        `(lambda
                           ,(second fn) ; formals
                           ,(reconstruct-unary---in-term (third fn))) ; body
                      fn)) ; function symbol
            (new-fn (if (eq new-fn 'unary--) '- new-fn))
            (new-args (reconstruct-unary---in-terms (rest term))))
       (cons new-fn new-args))))

 (defund reconstruct-unary---in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-unary---in-term (car terms))
           (reconstruct-unary---in-terms (cdr terms))))))

(make-flag flag-reconstruct-unary---in-term
           reconstruct-unary---in-term)

(defthm-flag-reconstruct-unary---in-term

  (defthm pseudo-termp-reconstruct-unary---in-term
    (implies (pseudo-termp term)
             (pseudo-termp (reconstruct-unary---in-term term)))
    :flag reconstruct-unary---in-term)

  (defthm pseudo-term-listp-reconstruct-unary---in-terms
    (implies (pseudo-term-listp terms)
             (and (pseudo-term-listp (reconstruct-unary---in-terms terms))
                  (equal (len (reconstruct-unary---in-terms terms))
                         (len terms))))
    :flag reconstruct-unary---in-terms)
  :hints (("Goal" :in-theory (enable reconstruct-unary---in-term reconstruct-unary---in-terms))))

;;; Unquote numbers, characters, strings, T, and NIL in term.
;;; The result may not be a pseudo-term but is a valid user-level term
;;; that would be converted to a pseudo-term if supplied to ACL2.

(mutual-recursion

 (defun unquote-in-term (term)
   (declare (xargs :guard (pseudo-termp term)))
   ;; no change if term is variable:
   (if (variablep term)
       term
     ;; remove QUOTE if quoted number, character, string, T, or NIL:
     (if (quotep term)
         (if (or (acl2-numberp (farg1 term))
                 (characterp (farg1 term))
                 (stringp (farg1 term))
                 (eq (farg1 term) t)
                 (eq (farg1 term) nil))
             (farg1 term)
           term) ; no change otherwise
       ;; recursively process function application:
       (let* ((fn (ffn-symb term))
              (new-fn (if (consp fn) ; lambda
                          (list 'lambda
                                (second fn) ; formals
                                (unquote-in-term (third fn))) ; body
                        fn)) ; function symbol
              (new-args (unquote-in-terms (rest term))))
         (cons new-fn new-args)))))

 (defun unquote-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (unquote-in-term (first terms))
           (unquote-in-terms (rest terms))))))

;; Reconstruct calls of MBT that were expanded to calls of RETURN-LAST.

(mutual-recursion
 (defun reconstruct-mbt-in-term (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (or (variablep term)
           (fquotep term))
       term
     (let* ((new-args (reconstruct-mbt-in-terms (fargs term)))
            (fn (ffn-symb term))
            (fn (if (consp fn)
                    `(lambda ,(lambda-formals fn) ,(reconstruct-mbt-in-term (lambda-body fn)))
                  fn)))
       (if (and (eq fn 'RETURN-LAST)
                (consp (cddr new-args))
                (equal ''MBE1-RAW (first new-args))
                (equal ''t (second new-args)))
           `(mbt ,(third new-args))
         (cons fn new-args)))))
 (defun reconstruct-mbt-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (reconstruct-mbt-in-term (first terms))
           (reconstruct-mbt-in-terms (rest terms))))))

(make-flag reconstruct-mbt-in-term)

(defthm len-of-reconstruct-mbt-in-terms
  (equal (len (reconstruct-mbt-in-terms terms))
         (len terms)))

(defthm-flag-reconstruct-mbt-in-term
  (defthm pseudo-termp-of-reconstruct-mbt-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (reconstruct-mbt-in-term term)))
    :flag reconstruct-mbt-in-term)
  (defthm pseudo-term-listp-of-reconstruct-mbt-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (reconstruct-mbt-in-terms terms)))
    :flag reconstruct-mbt-in-terms))

;NOTE Keep this up-to-date as more reconstruction functions are added.
;note: an alternative to this would be to use the rewriter
;this should not affect the meaning of the term at all
;note: the result of this may not be suitable for further processing, so perhaps do it only just before writing out the result (e.g., in the body of a defun)
(defun reconstruct-macros-in-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (let* ((term (reconstruct-*-in-term term))
         (term (reconstruct-+-in-term term))
         (term (reconstruct-unary---in-term term))
         (term (reconstruct-<=-in-term term))
         (term (reconstruct-or-in-term term))
         (term (reconstruct-and-in-term term))
         (term (reconstruct-mbt-in-term term))
         (term (unquote-in-term term)))
    term))

(in-theory (disable reconstruct-*-in-term
                    reconstruct-+-in-term
                    reconstruct-unary---in-term
                    reconstruct-<=-in-term
                    reconstruct-or-in-term
                    reconstruct-and-in-term
                    unquote-in-term))
