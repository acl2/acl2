; Tests for def-equality-transformation
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "def-equality-transformation")
(include-book "std/testing/must-be-redundant" :dir :system)

;; Note that def-equality-transformation now generates copy-function, so here
;; we give the expected results of that generation:
(must-be-redundant
 (defun copy-function-in-defun (fn ;the old function (possibly in a mut-rec) to handle
                                fn-event ; the event that introduced FN
                                function-renaming
                                rec
                                function-disabled ; whether to disable the new function
                                measure ; either :auto or an (untranslated) term
                                measure-hints ; either :auto or a list of hints like (("Goal" :in-theory (enable car-cons)))
                                state ; todo: can we avoid taking state?
                                )
   (declare (xargs :stobjs state
                   :guard (and (symbolp fn)
                               (defun-or-mutual-recursion-formp fn-event)
                               (function-renamingp function-renaming)
                               (member-eq rec '(nil :single :mutual))
                               (t/nil/auto-p function-disabled)
                               ;; TODO: Guards for guard-hints, measure, and measure-hints
                               (fn-definedp fn (w state)))
                   :mode :program ; because we call rename-functions-in-untranslated-term
                   ))
   (let* ((body (get-body-from-event fn fn-event)) ; untranslated
          (wrld (w state))
          (formals (fn-formals fn wrld))
          (non-executable (non-executablep fn wrld))
          ;; Chose between defun, defund, defun-nx, etc.:
          (defun-variant (defun-variant fn non-executable function-disabled state))
          ;; TODO: Pull out the handling of declares into a utility:
          (declares (get-declares-from-event fn fn-event)) ;TODO: Think about all the kinds of declares that get passed through.
          ;; Handle the :normalize xarg (we don't need :normalize nil because install-not-normalized solves that issue (TODO: But should we pass it through anyway?)
          (declares (remove-xarg-in-declares :normalize declares))
          ;; Handle the :mode xarg:
          (declares (remove-xarg-in-declares :mode declares)) ;todo: handle this better.  this is needed because the event might have :mode :program even if the function was later lifted to logic.  Obviously we shouldn't do this once we support transforming :program mode functions.
          ;; Deal with the :verify-guards xarg.  We always do :verify-guards nil and then
          ;; do verify-guards later, in case the function appears in its own guard-theorem (todo: is that still necessary?):
          (declares (set-verify-guards-in-declares declares nil))
          (declares (remove-xarg-in-declares :guard-hints declares)) ;we never use the old guard-hints
          (declares (remove-xarg-in-declares :guard-debug declares)) ; verify-guards is done separately
          (declares (remove-xarg-in-declares :guard-simplify declares)) ; verify-guards is done separately
          ;; Handle the :measure xarg:
          (declares (if (not rec)
                        declares ;no :measure needed and one should not already be present
                      (if (eq :auto measure)
                          ;; :auto means try to adapt the previous measure (since we are just copying the function, that
                          ;; means using it with no changes).  Note that it might not already be in the declares if the
                          ;; function was initially in :program mode (the measure could have been provided in the call of
                          ;; verify-termination):
                          (let ((measure (fn-measure fn state)))
                            ;; TODO: Consider omitting the :measure if it's what ACL2 would use by default?
                            (replace-xarg-in-declares :measure measure declares))
                        ;; Use the measure explicitly provided by the user:
                        (if (not (translatable-termp measure wrld))
                            (er hard 'copy-function-in-defun "Measure, ~x0, is not a recognized term." measure)
                          (replace-xarg-in-declares :measure measure declares)))))
          ;; Handle the (termination) :hints xarg:
          (declares (if (not rec)
                        declares ; no termination since not recursive
                      ;; single or mutual recursion:
                      (replace-xarg-in-declares
                       :hints
                       (if (eq :auto measure-hints)
                           `(("Goal" :in-theory '()
                              ;; ACL2 automatically replaces the old functions with the new ones in this:
                              :use (:instance (:termination-theorem ,fn))))
                         measure-hints)
                       declares)))
          ;; Handle the :stobjs xarg:
          (declares (set-stobjs-in-declares-to-match declares fn wrld))
          ;; TODO: What about irrelevant declares?  They need to be handled at a higher level, since they may depend on mut-rec partners.
          ;; We should clear them out here and set them if needed in copy-function-event.
          ;; Here we would change the body if fn is in target-fns, but we are just copying it so there is nothing do:
          (body (copy-function-core-function fn body wrld))
          ;; (new-fns-arity-alist (pairlis$ (strip-cdrs function-renaming)
          ;;                                (fn-arities (strip-cars function-renaming) wrld)))
          ;; ;; New fns from the renaming may appear as recursive calls, but they are not yet in the world:
          ;; (fake-wrld (add-fake-fns-to-world new-fns-arity-alist wrld))
          ;; todo: can we get the arities by analyzing the body?
          ;; Fix up recursive calls:
          (body (if (not rec) ;; no recursive calls to fix up:
                    body
                  ;; We could optimize this a bit by avoiding recomputing the fake-wrld in this:
                  (rename-functions-in-untranslated-term body
                                                         function-renaming
                                                         state)))
          (declares (fixup-ignores2 declares formals body function-renaming wrld))
          (new-fn (lookup-eq-safe fn function-renaming)) ;new name for this function
          )
     `(,defun-variant ,new-fn ,formals
        ,@declares
        ,body)))

 ;; Go through all the functions in the clique. For each, if it is in
 ;; TARGET-FNS, we both transform it and update rec calls in it (yes, for
 ;; copy-function the transform part is a no-op).  Otherwise, we just update rec
 ;; calls.  Returns a list of new defuns.
 (defun copy-function-in-defuns (fns
                                 target-fns ;; the functions to which the transformation is being applied (a no-op for copy-function but not in general)
                                 fn-event ; the mutual-recursion that introduced all the fns
                                 function-renaming ; indicates fixups needed for rec calls
                                 function-disabled ; whether to disable all the new functions
                                 measure-alist ; maps each old function name to the measure/:auto to use for its new version
                                 measure-hints ; will be attached to the first function in the clique
                                 firstp ;whether this is the first function in the clique
                                 state)
   (declare (xargs :stobjs state
                   :guard (and (symbol-listp fns)
                               (symbol-listp target-fns)
                               (all-fn-definedp fns (w state))
                               (function-renamingp function-renaming)
                               (t/nil/auto-p function-disabled)
                               (symbol-alistp measure-alist))
                   :mode :program))
   (if (endp fns)
       nil
     (let ((fn (first fns)))
       (cons (if (member-eq fn target-fns)
                 ;; transform the function:
                 (copy-function-in-defun fn fn-event function-renaming :mutual function-disabled
                                         (lookup-eq fn measure-alist)
                                         (if firstp measure-hints :auto) ; attach measure hints to only the first function
                                         state)
               ;; Just copy the function and update rec calls:
               ;; (For copy-function only, this happens to be the same as the branch above.)
               (copy-function-in-defun fn fn-event function-renaming :mutual function-disabled
                                       (lookup-eq fn measure-alist)
                                       (if firstp measure-hints :auto) ; attach measure hints to only the first function
                                       state))
             (copy-function-in-defuns (rest fns) target-fns fn-event function-renaming function-disabled
                                      measure-alist measure-hints
                                      nil ;no longer the first function
                                      state)))))

 ;; Generates the event that copy-function will submit.
 ;; Returns (mv erp result state), where result is usually an event but in the erp case might contain other useful info.
 ;; TODO: Maybe return the main form and the exported-form(s)
 ;; TODO: Add lots of error checks
 (defun copy-function-event (fn
                             new-name
                             theorem-disabled
                             function-disabled
                             verify-guards
                             guard-hints
                             measure ; may be a call of :map if mut-rec
                             measure-hints
                             verbose ;for now, this is a boolean (corresponding to whether the :print option was :info or higher), but we could support passing in richer information
                             ctx
                             state)
   (declare (xargs :stobjs state
                   ;; :verify-guards nil
                   :mode :program ;because of my-get-event and get-clique
                   :guard t       ;; inputs are checked below
                   ))
   (b* ((- (and verbose (cw "Now in the expansion phase of ~x0 for ~x1.~%" 'copy-function fn)))
        (description (msg "The target function"))
        ;; todo: tweak these messages to make them more consistent:
        ((er &) (ensure-value-is-function-name fn description :bad-input fn ctx state)) ;we pass back fn as the error value to indicate which part of the input as bad.  TODO: Return something more informative?
        ((er &) (ensure-function-is-logic-mode fn description :bad-input fn ctx state))
        ((er &) (ensure-function-is-defined fn description :bad-input fn ctx state))
        (recursivep (fn-recursivep fn state))
        ((er &) (if (and recursivep
                         (eq :auto measure))
                    (ensure-function-known-measure fn description :bad-input fn ctx state)
                  (mv nil nil state)))
        (wrld (w state))
        ;; Get the event that introduced fn:
        (fn-event (my-get-event fn wrld))
        (prologue (transformation-prologue fn wrld)) ;puts in install-not-normalized for fn (and its mutually-recursive partners)
        (verify-guards (if (eq :auto verify-guards) (guard-verified-p fn wrld) verify-guards))
        )
     (if (not recursivep)
         ;; we are operating on a single, non-recursive function:
         (let* ((new-fn (pick-new-name fn new-name state))
                (function-renaming (acons fn new-fn nil))
                (new-defun (copy-function-in-defun fn
                                                   fn-event
                                                   function-renaming
                                                   nil ; rec=nil means non-recursive
                                                   function-disabled
                                                   measure
                                                   measure-hints
                                                   state))
                ;;extra enables needed for the proof (TODO: This is a bit brittle because the original definition also gets enabled):
                (enables (append (list (install-not-normalized-name fn)
                                       (install-not-normalized-name new-fn))
                                 'nil))
                (new-defun-to-export (if verify-guards (ensure-defun-demands-guard-verification new-defun) new-defun))
                (becomes-theorem (make-becomes-theorem fn new-fn nil (not theorem-disabled) enables '(theory 'minimal-theory) state))
                ;; Remove :hints from the theorem before exporting it:
                (becomes-theorem-to-export (clean-up-defthm becomes-theorem)))
           (mv nil
               `(encapsulate ()
                  ,@prologue        ;; contains only local stuff
                  (local ,new-defun) ; has :verify-guards nil
                  (local (install-not-normalized ,new-fn))
                  (local ,becomes-theorem)
                  ,@(and verify-guards `((local ,(verify-guards-for-defun fn function-renaming guard-hints))))
                  ;; export the new defun and the becomes-theorem:
                  ,new-defun-to-export
                  ,becomes-theorem-to-export)
               state))
       (if (fn-singly-recursivep fn state)
           ;;we are operating on a single, recursive function:
           (let* ((new-fn (pick-new-name fn new-name state))
                  (function-renaming (acons fn new-fn nil))
                  (new-defun (copy-function-in-defun fn
                                                     fn-event
                                                     function-renaming
                                                     :single ;rec
                                                     function-disabled
                                                     measure
                                                     measure-hints
                                                     state))
                  (enables (append (list (install-not-normalized-name fn)
                                         (install-not-normalized-name new-fn))
                                   'nil))
                  (new-defun-to-export (if verify-guards (ensure-defun-demands-guard-verification new-defun) new-defun))
                  (new-defun-to-export (remove-hints-from-defun new-defun-to-export))
                  (becomes-theorem (make-becomes-theorem fn new-fn :single (not theorem-disabled) enables '(theory 'minimal-theory) state))
                  ;; Remove :hints from the theorem before exporting it:
                  (becomes-theorem-to-export (clean-up-defthm becomes-theorem))
                  )
             (mv nil ; no error
                 `(encapsulate ()
                    ,@prologue        ;; contains only local stuff
                    (local ,new-defun) ; has :verify-guards nil
                    (local (install-not-normalized ,new-fn))
                    (local ,becomes-theorem)
                    ,@(and verify-guards `((local ,(verify-guards-for-defun fn function-renaming guard-hints))))
                    ;; export the new defun and the becomes theorem:
                    ,new-defun-to-export
                    ,becomes-theorem-to-export)
                 state))
         ;; we are operating on a mutually recursive nest of functions:
         (b* ((ctx (cons 'copy-function fn))
              (fns (get-clique fn wrld))
              ;; Handle the :new-name arg:
              (new-name-alist ;this is an alist, but some values may be :auto
               (elaborate-mut-rec-option2 new-name :new-name fns ctx))
              (function-renaming (pick-new-names new-name-alist state))
              ;; Handle the :measure arg:
              (measure-alist ;this is an alist, but some values may be :auto
               (elaborate-mut-rec-option2 measure :measure fns ctx))
              ;; (new-fns (strip-cdrs function-renaming))
              ;; (new-fn (lookup-eq-safe fn function-renaming))
              (new-defuns (copy-function-in-defuns fns
                                                   fns ;we'll say all the functions in the nest are targets (though for copy-function it doesn't matter)
                                                   fn-event
                                                   function-renaming
                                                   function-disabled ;TODO: Add :map support
                                                   measure-alist
                                                   measure-hints
                                                   t ; first function in the clique
                                                   state))
              (mutual-recursion `(mutual-recursion ,@new-defuns))
              (mutual-recursion-to-export (if verify-guards
                                              (ensure-mutual-recursion-demands-guard-verification mutual-recursion)
                                            mutual-recursion))
              (mutual-recursion-to-export (remove-hints-from-mutual-recursion mutual-recursion-to-export))
              (fn-and-not-normalized-fn-doublets (make-doublets fns (add-not-normalized-suffixes fns)))
              (flag-function-name (pack$ 'flag- fn '-for- 'copy-function)) ;todo: avoid clashes better
              ;; Use as a ruler-extender for the flag function anything used as a ruler-extender for any of the FNS:
              (ruler-extenders (union-ruler-extenders-of-fns fns wrld))
              (ruler-extenders (union-ruler-extenders ruler-extenders '(return-last))) ;make-flag can fail without this (see email to MK)
              ;; TODO: Can my-make-flag-with-name be much slower than make-flag
              ;; TODO: Why doesn't this work?:
              ;; (make-flag-form `(my-make-flag-with-name ,flag-function-name
              ;;                                          ,fn
              ;;                                          :body ,fn-and-not-normalized-fn-doublets))
              (make-flag-form `(my-make-flag ,fn ;TODO: Does my-make-flag slow down the proofs here?
                                             :ruler-extenders ,ruler-extenders
                                             :flag-function-name ,flag-function-name
                                             :body ,fn-and-not-normalized-fn-doublets))
              (becomes-theorems (make-becomes-theorems fns
                                                       function-renaming
                                                       (not theorem-disabled)
                                                       state))
              (becomes-defthm-flag (make-becomes-defthm-flag flag-function-name
                                                             becomes-theorems
                                                             fns
                                                             function-renaming
                                                             ;;TODO: Add the $not-normalized rules for all functions?
                                                             'nil
                                                             '(theory 'minimal-theory)
                                                             wrld))
              (becomes-theorems-to-export (clean-up-defthms becomes-theorems))
              )
           (mv nil
               `(encapsulate ()
                  ,@prologue ;; contains only local stuff
                  (local ,mutual-recursion)
                  (local (install-not-normalized ,(lookup-eq-safe fn function-renaming))) ;TODO: Is there any interaction between this and make-flag?
                  ;; make-flag helps with the proof about mutually recursive functions:
                  (local ,make-flag-form)
                  (local ,becomes-defthm-flag)
                  ,@(and verify-guards
                         `((local ,(verify-guards-for-defun fn function-renaming guard-hints))))
                  ;; Export the new mutual-recursion:
                  ,mutual-recursion-to-export
                  ;; Export the 'becomes' theorems:
                  ,@becomes-theorems-to-export
                  )
               state))))))

 ;; To see what this expands to, see copy-function-expansion.lisp:
 (deftransformation copy-function
   ;;required args:
   (fn ;;the name of a defined function (TODO: :logic mode only?)
    )
   ;; optional args, *not* including :show-only or :verbose (deftransformation puts those in):
   ((new-name ':auto)
    (theorem-disabled 'nil)   ;;TODO:  Call this :disable-theorem?
    (function-disabled ':auto) ;;TODO:  Call this :disable-function?
    ;;(non-executable 'nil) ;todo: just check the existing function? avoid double negative?
    (verify-guards ':auto)
    (guard-hints ':auto)
    (measure ':auto)
    (measure-hints ':auto))
   :pass-print t
   :pass-context t))
