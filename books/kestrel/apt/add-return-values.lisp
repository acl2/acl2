; A transformation to add parameters as additional return values
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/apt/utilities/def-equality-transformation" :dir :system)
(include-book "kestrel/terms-light/non-trivial-formals-and-args" :dir :system)
(include-book "kestrel/utilities/fresh-names" :dir :system)

(local (in-theory (disable state-p)))

;; This transformation takes a function that returns a single value and changes
;; it to also return the given parameters, as additional return values using MV.

;; TODO: For now, function must be tail recursive, because we don't fix up non-tail-rec calls properly

;; TODO: What if the function already returns an MV?

;; TODO: What if the given param is already returned on all (or some) branches?

;; Makes a theorem equating an arbitrary call of FN with a call of NEW-FN on the same arguments, suitable wrapped in MV-LET machinery.
;; REC is either nil (function is non-recursive), :single, or :mutual.
;; The BASE-THEORY is often (theory 'minimal-theory).
(defun make-becomes-theorem-for-add-return-values (fn ; name of the old function
                                                   new-fn ; name of the new function (must have the same params)
                                                   rec ; nil (for non-recursive), :single, or :mutual
                                                   thm-enable ;whether the "becomes theorem" should be enabled
                                                   enables ; rules to always enable in the proof ; drop??
                                                   base-theory ; ex: '(theory 'minimal-theory) or '(current-theory :here)
                                                   use-not-normalized-rulesp
                                                   new-return-values ;; the names of additional params being returned in the new function
                                                   state)
  (declare (xargs :guard (and (symbolp fn)
                              (symbolp new-fn)
                              (member-eq rec '(nil :single :mutual))
                              (booleanp thm-enable)
                              (true-listp enables)
                              (symbol-listp new-return-values)
                              (booleanp use-not-normalized-rulesp))
                  :stobjs state))
  (let ((formals (fn-formals fn (w state)))
        (defthm-variant (if thm-enable 'defthm 'defthmd))
        (return-value-name (fresh-symbol 'rv new-return-values))
        (fn-def-rule (if use-not-normalized-rulesp
                         (install-not-normalized-name fn)
                       fn))
        (new-fn-def-rule (if use-not-normalized-rulesp
                             (install-not-normalized-name new-fn)
                           new-fn)))
    `(,defthm-variant ,(becomes-theorem-name fn new-fn)
       (equal (,fn ,@formals)
              (mv-let (,return-value-name ,@new-return-values)
                (,new-fn ,@formals)
                (declare (ignore ,@new-return-values))
                ,return-value-name))
       ,@(if (eq rec :mutual) ;weird format for make-flag hints:
             nil              ; done at the defthm-flag level
           (if (eq rec :single)
               `(:hints (("Goal" :induct (,fn ,@formals) ; should we induct in the new or old function (old, since we know it is recursive?)?
                          :do-not '(generalize eliminate-destructors)
                          :in-theory (append '((:i ,fn)
                                               ,fn-def-rule ,new-fn-def-rule ,@enables)
                                             ,base-theory))))
             ;; non-recursive case:
             `(:hints (("Goal" :in-theory (append '(,fn-def-rule ,new-fn-def-rule ,@enables) ,base-theory)
                        :do-not '(generalize eliminate-destructors)
                        :do-not-induct t)))))
       ;; Put in a flag for defthm-flag-xxx if appropriate:
       ,@(and (eq rec :mutual) (list :flag fn)))))

;; Make the "becomes theorems" for the given FNS, using the FUNCTION-RENAMING to get their new names.
;; TODO: This could wrap the theorems in a call to defthm-flag-xxx.
;; TODO: Assumes the same params are added as return values for each function in the nest.
(defun make-becomes-theorems-for-add-return-values (fns
                                                    ;enables-for-each
                                                    function-renaming
                                                    thm-enable ; whether all the theorems should be enabled
                                                    ;enables
                                                    ;base-theory ; ex: (theory 'minimal-theory) or (current-theory :here)
                                                    use-not-normalized-rulesp
                                                    new-return-values ;; the names of additional params being returned in the new function  (TODO: what if different for each function?)
                                                    state)
  (declare (xargs :guard (and (symbol-listp fns)
                              (booleanp thm-enable)
                              (function-renamingp function-renaming)
                              (symbol-listp new-return-values)
                              (booleanp use-not-normalized-rulesp))
                  :stobjs state))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (cons (make-becomes-theorem-for-add-return-values fn (lookup-eq-safe fn function-renaming) :mutual thm-enable nil nil use-not-normalized-rulesp new-return-values state)
            (make-becomes-theorems-for-add-return-values (rest fns) function-renaming thm-enable use-not-normalized-rulesp new-return-values state)))))

;; todo: assumes the term is single-valued?
(mutual-recursion
 (defund add-return-values-in-term (term old-fn new-return-values)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbolp old-fn)
                               (symbol-listp new-return-values))
                   :verify-guards nil)) ; done below
   (if (or (variablep term)
           (quotep term))
       `(mv ,term ,@new-return-values)
     (let ((fn (ffn-symb term))
           (args (fargs term)))
       (if (and (eq fn 'if)
                (eql 3 (len args)) ;helps us prove that the fargs are pseudo-terms
                )
           `(if ,(farg1 term)
                ,(add-return-values-in-term (farg2 term) old-fn new-return-values)
              ,(add-return-values-in-term (farg3 term) old-fn new-return-values))
         (if (consp fn) ; test for ((lambda (...formals...) body) ...args...)
             (b* ((lambda-formals (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ((mv non-trivial-lambda-formals
                       & ; non-trivial-args
                       )
                   (non-trivial-formals-and-args lambda-formals args))
                  ((when (intersection-eq non-trivial-lambda-formals new-return-values))
                   (er hard? 'add-return-values-in-term "Variable capture between new return values and lambda formals."))
                  ;; apply recursively to the lambda body:
                  (new-lambda-body (add-return-values-in-term lambda-body old-fn new-return-values)))
               `((lambda (,@lambda-formals) ,new-lambda-body) ,@args))
           (if (call-of old-fn term)
               ;; tail-recursive call (will be renamed later):
               term
             ;; anything else (todo: handle this better?  what if it contains recursive calls?):
             `(mv ,term ,@new-return-values)))))))

 (defund add-return-values-in-terms (terms old-fn new-return-values)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbolp old-fn)
                               (symbol-listp new-return-values))))
   (if (endp terms)
       nil
     (cons (add-return-values-in-term (first terms) old-fn new-return-values)
           (add-return-values-in-terms (rest terms) old-fn new-return-values)))))

(verify-guards add-return-values-in-term)

(defund add-return-values-in-defun-body (fn untranslated-body state
                                            ;; transformation-specific args:
                                            new-return-values untranslate)
  (declare (xargs :guard (and (symbolp fn)
                              (symbol-listp new-return-values)
                              (booleanp untranslate))
                  :mode :program ; because of translate-term
                  :stobjs state))
  (let* ((wrld (w state))
         (translated-body (translate-term untranslated-body 'add-return-values-in-defun-body wrld)) ;todo: can we avoid translating?
         (new-body (add-return-values-in-term translated-body fn new-return-values)))
    (if untranslate
        (untranslate new-body nil wrld)
      new-body)))

;; Make the full transformation:
(def-equality-transformation
  add-return-values ; name of the transformation to create
  ;todo: have a default for this, like we do for deftransformation?:
  add-return-values-in-defun-body ; core function to transform a function body
  ;; transform-specific required args:
  (new-return-values ; formals to return
   )
  ;; transform-specific keyword args and defaults:
  ((untranslate 't))
  :make-becomes-theorem-name make-becomes-theorem-for-add-return-values
  :make-becomes-theorems-name make-becomes-theorems-for-add-return-values
  :make-becomes-theorem-extra-args (new-return-values)
  :transform-specific-arg-descriptions
  ((new-return-values "Names of new formals to return.")
   (untranslate "Whether to untranslate the new body.")))
