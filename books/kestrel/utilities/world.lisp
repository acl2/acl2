; Utilities for querying the ACL2 logical world.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2015-2017, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "legal-variable-listp")
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

;; TODO: Change some of these to just take wrld instead of state.

;; TODO: Try to use built-in functions or AC's functions instead of these.

; function-symbolp is built in to ACL2 and tests whether its argument is a
; function in the ACL2 world.
(in-theory (disable function-symbolp))

(defthm alistp-of-getprops
  (alistp (getprops key world-name w))
  :hints (("Goal" :in-theory (enable symbol-<))))

;; TODO: Add a check for a primitive function (using *primitive-formals-and-guards*)

;; Returns the body (as a translated term) of NAME, which should be a function.
;ffixme any time we lookup unnormalized-body (here and elsewhere) consider what happens when we try to lookup the body of a primitive..  fixme and what about a constrained function?
;todo: make a safe version of this whose guard is fn-definedp
;TODO: This doesn't work for :program mode functions like refinementp; consider using cltl-def-from-name.
; Note that this function can return nil if throw-errorp is nil (similarly for
; an earlier version of this function).
(defund fn-body (name throw-errorp wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (let ((body (getprop name 'unnormalized-body nil 'current-acl2-world wrld)))
    (if (not body)
        (if throw-errorp
            (er hard? 'fn-body "No body found for ~x0 !" name)
          nil)
      (if (not (pseudo-termp body))
          (er hard? 'fn-body  "Body of function ~x0 is not a pseudo-term !" name)
        body))))

;; Check whether NAME is a defined function.
(defund fn-definedp (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (let ((body (getpropc name 'unnormalized-body nil wrld)))
    (if (not body)
        nil                         ;; function is not defined
      (if (not (pseudo-termp body)) ;todo: not sure this check is appropriate here
          (er hard? 'fn-definedp "Function ~x0's body is not a pseudo-termp (it's ~x1).~%" name body)
        t))))

(defun all-fn-definedp (names wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp wrld))))
  (if (atom names)
      t
    (and (fn-definedp (first names) wrld)
         (all-fn-definedp (rest names) wrld))))

;Happens to be true even if FN is not defined, because hard-error returns nil, which is a pseudo-term
(defthm pseudo-termp-of-fn-body
  (pseudo-termp (fn-body fn throw-errorp wrld))
  :hints (("Goal" :in-theory (enable fn-body))))

;; Get the formals of a function
(defund fn-formals (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (let ((formals (getpropc name 'formals :none wrld)))
    (if (eq formals :none)
        (er hard? 'fn-formals "No formals for ~x0; maybe it's not a function." name)
      (if (not (symbol-listp formals)) ; to support proofs of guards (should always be true)
          (er hard? 'fn-formals "Formals of ~x0 are not a list of symbols." name)
        (if (not (legal-variable-listp formals)) ; to support proofs of guards (should always be true)
            (er hard? 'fn-formals "Formals of ~x0 are not all legal variables." name)
          formals)))))

(defthm true-listp-of-fn-formals
  (true-listp (fn-formals name wrld))
  :hints (("Goal" :in-theory (enable fn-formals)))
  :rule-classes :type-prescription)

(defthm symbol-listp-of-fn-formals
  (symbol-listp (fn-formals fun wrld))
  :hints (("Goal" :in-theory (enable fn-formals))))

(defthm legal-variable-listp-of-fn-formals
  (legal-variable-listp (fn-formals fun wrld))
  :hints (("Goal" :in-theory (enable fn-formals))))

;dup
(local
 (defthm pseudo-term-listp-when-symbol-listp-cheap
   (implies (symbol-listp x)
            (pseudo-term-listp x))
   :rule-classes ((:rewrite :backchain-limit-lst (0)))))

;dup
(local
 (defthm eqlable-listp-when-symbol-listp-cheap
   (implies (symbol-listp x)
            (eqlable-listp x))
   :rule-classes ((:rewrite :backchain-limit-lst (0)))))

(defthm pseudo-term-listp-of-fn-formals
  (pseudo-term-listp (fn-formals fn wrld)))

(defthm eqlable-listp-of-fn-formals
  (eqlable-listp (fn-formals fun wrld)))

(defun fn-arity (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (len (fn-formals name wrld)))

;returns the guard of the given function (t means either no guard given or an
;explicit guard of t).  Works even on :program mode functions.
(defun fn-guard (name world)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp world))))
  (getprop name 'guard *t* 'current-acl2-world world))

(defund fn-has-measurep (name state)

; This function really just checks (as in a previous version) that there is a
; 'justification property on name.  The "measure" might not exist, in that it
; could be :?.

  (declare (xargs :stobjs (state)
                  :guard (symbolp name)))
  (not (null (getpropc name 'justification))))

;; Only call this on a recursive function.  TODO: Add a guard that checks that.
;; TODO: Improve this to use get-event to get an untranslated version of the
;; measure, if present.  Otherwise, do what this already does.  TODO: Add a
;; flag to suppress the assert(s) that the measure exists.  Then Matt could use
;; this in simplify-defun.
(defund fn-measure (name state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp name)))
  (let ((justification (getpropc name 'justification)))
    (if (not (weak-justification-p justification))
        (er hard? 'fn-measure "Justification property found for ~x0 is bad (~x1)." name justification)
      (let ((measure (access justification justification :measure)))
        (if (not (pseudo-termp measure)) ; to support proofs of guards (should always be true)
            (er hard? 'fn-measure  "Measure expression of ~x0 is not a pseudo-term." name)
          measure)))))

(defthm pseudo-termp-of-fn-measure
  (pseudo-termp (fn-measure fun state))
  :hints (("Goal" :in-theory (enable fn-measure))))

;; Only call this on recursive functions.  TODO: Add a guard that checks that.
(defun fn-measures (names state)
  (declare (xargs :stobjs (state)
                  :guard (symbol-listp names)))
  (if (endp names)
      nil
    (cons (fn-measure (first names) state)
          (fn-measures (rest names) state))))

;;Tests whether NAME is recursive or mutually-recursive, when
;;NAME is a :logic mode function symbol.
; TODO: Generalize to handle :program mode functions. Here is an example where we get the wrong answer:
;; (defun len3 (x) (declare (xargs :mode :program)) (if (endp x) 0 (+ 1 (len3 (cdr x)))))
;; TODO: Or strengthen guard to require a :logic mode function (and similarly for other functions in the file)?
;; Ideas from Matt: If it's a program-mode function, use get-event to
;; get the admitting event EV, return T if it's a mutual-recursion,
;; else translate the body (car (last EV)) and then return (ffnnamep
;; fn body).  If it's a logic-mode function, then
; return (recursivep fn nil wrld).
;; Or perhaps first improve fn-body and just call that.

(defund fn-recursivep (name state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp name)))
  (not (eq (getpropc name 'recursivep t)
           t)))

(defund fn-singly-recursivep (name state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp name)))
  (eql 1 (len (getpropc name 'recursivep))))

(defund fn-mutually-recursivep (name state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp name)))
  (< 1 (len (getpropc name 'recursivep))))

;; Return a list of all recursive / mutually-recursive partners of NAME (including NAME itself).
;; If NAME is non-recursive, return nil.
;; TODO: Use get-clique instead?
;; TODO: Is the order here guaranteed to be the order of functions in the clique?
(defund fn-recursive-partners (name state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp name)))
  (let ((partners (getpropc name 'recursivep)))
    (if (not (symbol-listp partners))
        (er hard? 'fn-recursive-partners "The recursive partners of ~x0 are ill-formed." name)
      partners)))

(defthm symbol-listp-of-fn-recursive-partners
  (symbol-listp (fn-recursive-partners fn state))
  :hints (("Goal" :in-theory (enable fn-recursive-partners))))

;todo: just take wrld
(mutual-recursion
 (defund arities-okayp (term state)
   (declare (xargs :stobjs (state)
                   :guard (pseudo-termp term)))
   (if (variablep term)
       t
     (if (quotep term)
         t
       ;;function call or lambda
       (let ((fn (ffn-symb term)))
         (and (if (consp fn)
                  ;;if it's a lambda application, check the body:
                  (let* ((lambda-body (third fn)))
                    (arities-okayp lambda-body state))
                ;; no lambda body to check:
                t)
              ;; the number of args must be right:
              (let ((num-formals
                     (if (consp fn)
                         ;;if it's a lambda application:
                         (let* ((lambda-formals (lambda-formals fn)))
                           (len lambda-formals))
                       (fn-arity fn (w state)))))
                (equal num-formals (length (fargs term))))
              ;; the args must all be okay:
              (all-arities-okayp (fargs term) state))))))

 (defund all-arities-okayp (term-lst state)
   (declare (xargs :stobjs (state)
                   :guard (pseudo-term-listp term-lst)))
   (if (atom term-lst)
       t
     (and (arities-okayp (first term-lst) state)
          (all-arities-okayp (rest term-lst) state)))))

;; Return term unless its arities are wrong, in which case throw an error
;; TODO: Take wrld instead of state?
;; TODO: Print the actual subterm with the bad arity.
(defun check-arities-fn (term state)
  (declare (xargs :stobjs (state)
                  :guard (pseudo-termp term)))
  (if (arities-okayp term state)
      term ;no errorl just pass through term
    (er hard? 'check-arities "Bad arities for term ~x0." term)))

;; Return term unless its arities are wrong, in which case throw an error
(defmacro check-arities (term)
  `(check-arities-fn ,term state))

;;assumes defthm-name is the name of a theorem in the world. ;todo:
;;make a separate version that checks that
(defund defthm-body (defthm-name wrld)
  (declare (xargs :guard (and (symbolp defthm-name)
                              (plist-worldp wrld))))
  (let ((body (getprop defthm-name 'theorem nil 'current-acl2-world wrld)))
    (if (not body)
        (er hard? 'defthm-body "~x0 does not appear to be a theorem in the current world !" defthm-name)
      (if (not (pseudo-termp body))
          (er hard? 'defthm-body "Bad theorem body found for ~x0 (should be a pseudo-term, but we got ~x1) !" defthm-name body)
        body))))

(defthm pseudo-termp-of-defthm-body
  (pseudo-termp (defthm-body name wrld))
  :hints (("Goal" :in-theory (enable defthm-body))))

;;assumes defthm-name is the name of a theorem in the world. ;todo:
;;make a separate version that checks that
;todo: should we apply any checks to the body?
(defund defthm-body-untranslated (defthm-name wrld)
  (declare (xargs :guard (and (symbolp defthm-name)
                              (plist-worldp wrld))))
  (let ((untranslated-body (getprop defthm-name 'untranslated-theorem nil 'current-acl2-world wrld)))
    (if (not untranslated-body)
        ;; this message assumes every theorem has an 'untranslated-theorem property:
        (er hard? 'defthm-body-untranslated "~x0 does not appear to be a theorem in the current world !" defthm-name)
      untranslated-body)))

(defun defthm-rule-classes (defthm-name wrld)
  (declare (xargs :guard (and (symbolp defthm-name)
                              (plist-worldp wrld))))
  (let ((rule-classes (getprop defthm-name 'classes :default 'current-acl2-world wrld)))
    (if (eq :default rule-classes)
        (er hard? 'defthm-rule-classes "Rule-classes for ~x0 not found." defthm-name)
      (if (not (true-listp rule-classes))
          (er hard? 'defthm-rule-classes "Rule-classes for ~x0 are not a true list." defthm-name)
        rule-classes))))

(defthm true-listp-of-defthm-rule-classes
  (true-listp (defthm-rule-classes name wrld))
  :rule-classes :type-prescription)

;; Check whether NAME is a defined defthm
(defund defined-defthmp (name state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp name)))
  (let ((body (getpropc name 'theorem)))
    (if (not body)
        nil
      (if (not (pseudo-termp body))
          (er hard? 'defined-defthmp "Theorem ~x0's body is not a pseudo-termp (it's ~x1).~%" name body)
        t))))

(defun filter-0ary-fns (fns state)
  (declare (xargs :stobjs state
                  :guard (symbol-listp fns)))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (if (and (fn-definedp fn (w state))
               (null (fn-formals fn (w state))))
          (cons fn (filter-0ary-fns (rest fns) state))
        (filter-0ary-fns (rest fns) state)))))

;(verify-termination EXECUTABLE-COUNTERPART-THEORY-FN)

;dup
(DEFUN ENLIST-ALL (ITEMS)
  (IF (ENDP ITEMS)
      NIL
      (CONS (LIST (CAR ITEMS))
            (ENLIST-ALL (CDR ITEMS)))))

;dup
(DEFUN CONS-ONTO-ALL (ITEM LSTS)
  (declare (xargs :guard (true-listp lsts)))
  (IF (ENDP LSTS)
      NIL
      (CONS (CONS ITEM (CAR LSTS))
            (CONS-ONTO-ALL ITEM (CDR LSTS)))))

(defun 0-ary-executable-counterpart-theory (state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let* ((executable-counterpart-theory (executable-counterpart-theory-fn :here (w state)))
         (fns (strip-cadrs executable-counterpart-theory))
         (fns (filter-0ary-fns fns state))
         (runes (cons-onto-all :executable-counterpart (ENLIST-ALL fns)))
         )
    runes))

;; Helper function for all-functions-in-world.
(defun all-functions-in-world-aux (wrld acc)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (true-listp acc))))
  (if (endp wrld)
      (remove-duplicates-equal acc) ;slow?  consider a version of remove-duplicates that uses fast alists or property worlds?
    (let* ((triple (first wrld))
           (prop (cadr triple)))
      (if (eq 'formals prop)
          (all-functions-in-world-aux (rest wrld) (cons (car triple) acc))
        (all-functions-in-world-aux (rest wrld) acc)))))

(defthm symbol-listp-of-all-functions-in-world-aux
  (implies (and (symbol-listp acc)
                (plist-worldp wrld))
           (symbol-listp (all-functions-in-world-aux wrld acc))))

;; Return a list of all functions currently present in WRLD.
;; Example usage: (all-functions-in-world (w state))
(defun all-functions-in-world (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (all-functions-in-world-aux wrld nil))

(defthm symbol-listp-of-all-functions-in-world
  (implies (plist-worldp wrld)
           (symbol-listp (all-functions-in-world wrld))))

;; throws a hard error if all the NAMES are not theorems or function names
;; (representing their definition rules) in WRLD
(defun ensure-all-theoremsp (names wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp wrld))))
  (if (endp names)
      t
    (and (or (fn-definedp (first names) wrld)
             (defthm-body (first names) wrld))
         (ensure-all-theoremsp (rest names) wrld))))
