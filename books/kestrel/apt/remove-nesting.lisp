; A transformation to avoid nesting of function calls
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Karthik Nukala (nukala@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This tranformation is useful for preparing to call ATC, for example, to
;; avoid nested array writes.

;; TODO: Generalize the set of supported terms.

(include-book "kestrel/apt/utilities/def-equality-transformation" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/fresh-names" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/bound-vars-in-term" :dir :system)
(include-book "kestrel/lists-light/remove-nth" :dir :system)
(include-book "kestrel/typed-lists-light/symbol-listp" :dir :system)
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable symbol-listp mv-nth)))

;; TODO: Add support for IFs, LETs, user-defined functions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library stuff:

;move
(local
 (defthm pseudo-term-listp-of-remove-nth
  (implies (pseudo-term-listp list)
           (pseudo-term-listp (remove-nth n list)))
  :hints (("Goal" :in-theory (enable remove-nth)))))

;move
;; (remove-nth 3 '(0 1 2 3 4 5))

;move
;; Insert ITEM into LIST at position N, shifting existing elements down.
(defun insert-at-position (n item list)
  (declare (xargs :guard (and (natp n)
                              (<= n (len list))
                              (true-listp list))))
  (if (zp n)
      (cons item list)
    (cons (car list) (insert-at-position (+ -1 n) item (cdr list)))))

;move
;; (insert-at-position 2 'blah '(0 1 2 3 4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether TERM is a nest of calls to TARGET-FN terminating in a variable,
;; where the nesting is in t ARGNUMth argument (1-based).
(defun var-terminated-nest-of-writesp (term target-fn argnum)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp target-fn)
                              (posp argnum))))
  (if (variablep term)
      t
    (if (fquotep term)
        nil
      (and (call-of target-fn term)
           (<= argnum (len (fargs term)))
           (var-terminated-nest-of-writesp (nth (+ -1 argnum) (fargs term))
                                           target-fn
                                           argnum)))))

;; Extract the inner variable in a var-terminated-nest-of-writes.
(defund var-of-write-nest (term target-fn argnum)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp target-fn)
                              (posp argnum)
                              (var-terminated-nest-of-writesp term target-fn argnum))))
  (if (variablep term)
      term
    ;; must be a call of target-fn:
    (var-of-write-nest (nth (+ -1 argnum) (fargs term)) target-fn argnum)))

(defthm symbolp-of-var-of-write-nest
  (implies (and (pseudo-termp term)
                (var-terminated-nest-of-writesp term target-fn argnum))
           (symbolp (var-of-write-nest term target-fn argnum)))
  :hints (("Goal" :in-theory (enable var-of-write-nest))))

(defun var-terminated-nest-of-at-least-2-writes (term target-fn argnum)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp target-fn)
                              (posp argnum))))
  (and (var-terminated-nest-of-writesp term target-fn argnum)
       (call-of target-fn term)
       (call-of target-fn (nth (+ -1 argnum) (fargs term)))))

;; For each of the TERMS, if it depends on VAR, make a let
;; binding and return the new let var as the "new term" for that term.
;; Otherwise, the "new term" is just the term.
;; Returns (mv let-bindings new-terms names-to-avoid).
;; TODO: Generalize the terminology here, as the "array" could be a struct.
(defun handle-clashes-in-terms (terms names-to-avoid var)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (symbol-listp names-to-avoid)
                              (symbolp var))))
  (if (endp terms)
      (mv nil nil names-to-avoid)
    (let ((term (first terms)))
      (if (member-eq var (free-vars-in-term term))
          ;; If the term mentions the var, we have to let-bind something (we
          ;; could probably let-bind less than the whole term if we chose):
          (b* ((term-let-var (fresh-symbol 'x names-to-avoid)) ; todo: use a better name, perhaps based on the formal?
               (names-to-avoid (cons term-let-var names-to-avoid))
               ((mv rest-let-bindings rest-new-terms names-to-avoid)
                (handle-clashes-in-terms (rest terms) names-to-avoid var)))
            (mv (cons `(,term-let-var ,term) rest-let-bindings) ; add a let binding for the term
                (cons term-let-var rest-new-terms) ; refer to the term with its new let var
                names-to-avoid))
        ;; The term doesn't mention the var, so it's ok as-is, and we don't have
        ;; to consume a fresh name:
        (b* (((mv rest-let-bindings rest-new-terms names-to-avoid)
              (handle-clashes-in-terms (rest terms) names-to-avoid var)))
          (mv rest-let-bindings          ; don't add a let binding
              (cons term rest-new-terms) ; no change
              names-to-avoid))))))

(local
 (defthm true-listp-of-mv-nth-0-of-handle-clashes-in-terms
   (true-listp (mv-nth 0 (handle-clashes-in-terms terms names-to-avoid var)))))

(local
 (defthm symbol-listp-of-strip-cars-of-mv-nth-0-of-handle-clashes-in-terms
   (symbol-listp (strip-cars (mv-nth 0 (handle-clashes-in-terms terms names-to-avoid var))))))

(local
 (defthm pseudo-term-listp-of-strip-cadrs-of-mv-nth-0-of-handle-clashes-in-terms
   (implies (pseudo-term-listp terms)
            (pseudo-term-listp (strip-cadrs (mv-nth 0 (handle-clashes-in-terms terms names-to-avoid var)))))))

(local
 (defthm true-listp-of-mv-nth-1-of-handle-clashes-in-terms
   (true-listp (mv-nth 1 (handle-clashes-in-terms terms names-to-avoid var)))))

(local
 (defthm pseudo-term-listp-of-mv-nth-1-of-handle-clashes-in-terms
   (implies (pseudo-term-listp terms)
            (pseudo-term-listp (mv-nth 1 (handle-clashes-in-terms terms names-to-avoid var))))))

(local
 (defthm len-of-mv-nth-1-of-handle-clashes-in-terms
   (equal (len (mv-nth 1 (handle-clashes-in-terms terms names-to-avoid var)))
          (len terms))))

(local
 (defthm symbol-listp-of-mv-nth-2-of-handle-clashes-in-terms
   (implies (symbol-listp names-to-avoid)
            (symbol-listp (mv-nth 2 (handle-clashes-in-terms terms names-to-avoid var))))))

;; Returns (mv let-bindings names-to-avoid).
(defun remove-nesting-in-term-aux (term ; a var-terminated-nest-of-writes
                                   array-name
                                   names-to-avoid
                                   target-fn
                                   argnum ; 1-based
                                   )
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp target-fn)
                              (posp argnum)
                              (var-terminated-nest-of-writesp term target-fn argnum)
                              (symbolp array-name)
                              (symbol-listp names-to-avoid))
                  :verify-guards nil ; done below
                  ))
  (if (variablep term)
      (mv nil names-to-avoid) ;  no let bindings
    ;; must be a call to target-fn:
    (b* ((args (fargs term))
         (array-arg (nth (+ -1 argnum) args))
         (non-array-args (remove-nth (+ -1 argnum) (fargs term)))
         ((mv let-bindings-for-non-array-args new-non-array-args names-to-avoid)
          (handle-clashes-in-terms non-array-args names-to-avoid array-name))
         ;; Handle the array argument (innermost write will be listed first in the let):
         ((mv let-bindings-from-array-arg names-to-avoid)
          (remove-nesting-in-term-aux array-arg
                                      array-name ;name of the array
                                      names-to-avoid
                                      target-fn
                                      argnum)))
      (mv (append let-bindings-for-non-array-args
                  let-bindings-from-array-arg
                  (list `(,array-name
                          (,target-fn ,@(insert-at-position (+ -1 argnum)
                                                            array-name
                                                            new-non-array-args)))))
          names-to-avoid))))

(local
 (defthm true-listp-of-mv-nth-0-of-remove-nesting-in-term-aux
   (true-listp (mv-nth 0 (remove-nesting-in-term-aux term array-name names-to-avoid target-fn argnum)))))

(verify-guards remove-nesting-in-term-aux
  :hints (("Goal" :expand (var-terminated-nest-of-writesp term target-fn argnum))))

;; TODO: Serialize lambda bindings if necessary.

(defund at-most-one-non-trivial-bindingp (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args)
                              (= (len formals) (len args)))))
  (if (endp formals)
      t
    (let ((formal (first formals))
          (arg (first args)))
      (if (equal formal arg)
          (at-most-one-non-trivial-bindingp (rest formals) (rest args))
        ;; this binding in non-trivial, so all subsequent bindings must be trivial:
        (equal (rest formals) (rest args))))))

;; Finds the first arg that is a nested write.  Returns (mv foundp formal arg).
(defund find-lambda-formal-and-nested-write-arg (formals args target-fn argnum)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args)
                              (= (len formals) (len args))
                              (symbolp target-fn)
                              (posp argnum))))
  (if (endp formals)
      (mv nil nil nil)
    (let ((formal (first formals))
          (arg (first args)))
      (if (var-terminated-nest-of-at-least-2-writes arg target-fn argnum)
          (mv t formal arg)
        (find-lambda-formal-and-nested-write-arg (rest formals) (rest args) target-fn argnum)))))

(local
 (defthm var-terminated-nest-of-writesp-of-mv-nth-2-of-find-lambda-formal-and-nested-write-arg
   (implies (mv-nth 0 (find-lambda-formal-and-nested-write-arg formals args target-fn argnum))
            (var-terminated-nest-of-writesp (mv-nth 2 (find-lambda-formal-and-nested-write-arg formals args target-fn argnum)) target-fn argnum))
   :hints (("Goal" :in-theory (enable find-lambda-formal-and-nested-write-arg)))))

(local
 (defthm pseudo-termp-of-mv-nth-2-of-find-lambda-formal-and-nested-write-arg
   (implies (pseudo-term-listp args)
            (pseudo-termp (mv-nth 2 (find-lambda-formal-and-nested-write-arg formals args target-fn argnum))))
   :hints (("Goal" :in-theory (enable find-lambda-formal-and-nested-write-arg)))))

(local
 (defthm symbolp-of-mv-nth-1-of-find-lambda-formal-and-nested-write-arg
   (implies (symbol-listp formals)
            (symbolp (mv-nth 1 (find-lambda-formal-and-nested-write-arg formals args target-fn argnum))))
   :hints (("Goal" :in-theory (enable find-lambda-formal-and-nested-write-arg)))))

;; Add LETs to avoid nesting where a call of TARGET-FN has another call of TARGET-FN as its
;; ARGNUMth argument (1-based numbering).  This is useful for making array
;; writes obey single threadedness restrictions.  We currently require TERM to
;; be an IF-nest where each IF branch is a nest of calls of TARGET-FN terminating in a variable.  We call that variable
;; the "array name" and use it for all LET-bindings of calls of TARGET-FN in the given IF branch.  Additional
;; LET-bindings may be created to store the results of computations that use
;; old copies of the array.
;; todo: check inputs
;; It might be nice to untranslate the result, but we can't because we've already put in lets.
;; TODO: Support recursive calls?
;; TODO: Put in LET instead of lambda below.
(defund remove-nesting-in-body (term
                                target-fn ; the function whose calls should be un-nested
                                argnum ; the argument of target-fn that is the array (1-based)
                                )
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp target-fn)
                              (posp argnum))))
  (if (variablep term)
      term
    (let ((fn (ffn-symb term)))
      (if (eq 'quote fn)
          term
        (if (eq 'if fn)
            `(if ,(farg1 term) ; do we want to handle nesting in the test?
                 ,(remove-nesting-in-body (farg2 term) target-fn argnum)
               ,(remove-nesting-in-body (farg3 term) target-fn argnum))
          (if (flambdap fn) ;; test for ((lambda (...formals...) <body>) ...args...)
              (b* ((lambda-body (lambda-body fn))
                   (lambda-formals (lambda-formals fn))
                   (args (fargs term))
                   (new-lambda-body (remove-nesting-in-body lambda-body target-fn argnum))
                   ((mv foundp formal arg) (find-lambda-formal-and-nested-write-arg lambda-formals args target-fn argnum)))
                (if (not foundp)
                    `((lambda ,lambda-formals ,new-lambda-body) ,@args) ;; TODO: Make a let
                  ;; We found a lambda arg that is a nested write:
                  (if (not (at-most-one-non-trivial-bindingp lambda-formals args))
                      ;; TODO: This currently requires only a single changed var in the lambda.  Remove that restriction (but watch for capture).
                      (prog2$ (cw "NOTE: Unsupported lambda bindings (consider calling serialize-lambdas): ~X01.~%" term nil)
                              `((lambda ,lambda-formals ,new-lambda-body) ,@args))
                    ;; we found a single lambda var bound to a nest of writes:
                    (b* ((array-name formal) ;; or we could do (var-of-write-nest term target-fn argnum)
                         ;; todo: use union-eq here?:
                         (names-to-avoid (append (free-vars-in-term lambda-body) ; todo: other vars to avoid?
                                                 (bound-vars-in-term lambda-body)))
                         ((mv let-bindings
                              & ;names-to-avoid
                              )
                          (remove-nesting-in-term-aux arg array-name names-to-avoid target-fn argnum)))
                      ;; the let-bindings replace the old lambda binding of formal:
                      `(let* ,let-bindings ,new-lambda-body)))))
            ;; Regular function call (TODO: Handle nested writes in the args):
            (if (not (var-terminated-nest-of-at-least-2-writes term target-fn argnum))
                (prog2$ (cw "NOTE: No change made to term (consider calling let-bind-formals-in-calls): ~X01~%" term nil)
                        term ; do nothing
                        )
              ;; TERM is a nest of at least 2 writes:
              (let* ((array-name (var-of-write-nest term target-fn argnum))
                     (names-to-avoid (union-eq (free-vars-in-term term)
                                              (bound-vars-in-term term))))
                (mv-let (let-bindings names-to-avoid)
                  (remove-nesting-in-term-aux term array-name names-to-avoid target-fn argnum)
                  (declare (ignore names-to-avoid))
                  (if let-bindings
                      `(let* ,let-bindings ,array-name)
                    ;; todo: can this case happen?:
                    term))))))))))

;; Transforms a function body.  Returns the new body.
;; We call translate-term here and then do the rest of the work in the :logic-mode helper function.
(defun remove-nesting-core-function (fn ; passed in by def-equality-transformation but not used
                                     untranslated-body ; untranslated
                                     state
                                     ;; transformation-specific args:
                                     target-fn ; the function to un-nest (e.g., array write)
                                     argnum ; the argument of target-fn (1-based) that may be a nested call (e.g., an array)
                                     )
  (declare (xargs :mode :program ; because this calls translate-term
                  :guard (and (symbolp fn)
                              (symbolp target-fn)
                              (posp argnum))
                  :stobjs state)
           (ignore fn))
  (let* ((wrld (w state))
         (translated-body (translate-term untranslated-body 'remove-nesting-core-function wrld)) ;todo: can we avoid translating?
         )
    (remove-nesting-in-body translated-body target-fn argnum)))

;; Make the full transformation:
(def-equality-transformation
  remove-nesting ; name of the transformation to create
  remove-nesting-core-function ; core function to transform a function body
  (target-fn argnum) ; transformation-specific required args
  nil                ; transformation-specific keyword args and defaults
  :transform-specific-arg-descriptions
  ((target-fn "The function whose nested calls will be un-nested.") ; todo: allow giving the name of the formal
   (argnum "The argument number of the target-fn in which to look for nested calls (1-based).")))
