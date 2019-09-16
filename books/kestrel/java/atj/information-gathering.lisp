; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "aij-notions")
(include-book "primitives")

(include-book "kestrel/std/system/pure-raw-p" :dir :system)
(include-book "kestrel/std/system/rawp" :dir :system)
(include-book "kestrel/std/system/remove-mbe" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/system/world-queries" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-information-gathering
  :parents (atj-implementation)
  :short "Information gathering performed by @(tsee atj)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This code gathers the following information:")
   (xdoc::ul
    (xdoc::li
     "The names of all the currently known ACL2 packages.
      These are used to initialize
      the Java representation of the ACL2 environment.")
    (xdoc::li
     "The names of all the ACL2 functions to be translated to Java,
      as determined by @('fn1'), ..., @('fnp').")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fns-to-translate ((targets$ symbol-listp)
                              (deep$ booleanp)
                              (guards$ booleanp)
                              (verbose$ booleanp)
                              ctx
                              state)
  :returns (mv erp
               (fns "A @(tsee symbol-listp).")
               state)
  :mode :program
  :short "Collect the names of all the ACL2 functions to be translated to Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a worklist algorithm, which starts with @('(fn1 ... fnp)').")
   (xdoc::p
    "The iteration ends successfully when the worklist is empty;
     it ends with an error if the next function in the worklist
     either (1) has raw Lisp code and is not in the whitelist,
     or (2) has no @('unnormalized-body') property
     and is not natively implemented in AIJ,
     or (3) has input or output stobjs.
     When the next function in the worklist is natively implemented in AIJ,
     it is just removed from the worklist
     (note that currently the ACL2 functions natively implemented in AIJ
     have no input or output stobjs, because they are all primitive functions).
     When the @(':deep') input is @('nil'),
     the @(':guards') input is @('t'),
     and the next function in the worklist is in @(tsee *atj-primitive-fns*),
     the function is just removed from the worklist
     (note that currently these ACL2 functions have no input or output stobjs).
     In all other cases,
     the next function in the worklist is added to the accumulator
     (unless it is already there),
     and all the functions it calls (in the @('unnormalized-body'))
     are added to the worklist,
     except for those already in the accumulator or worklist.")
   (xdoc::p
    "Before collecting the functions
     called by the next function in the worklist,
     all the calls of @(tsee mbe) in the function's unnormalized body
     are replaced with their @(':logic') or @(':exec') parts,
     based on the @(':guards') input.
     Thus, their @(':exec') or @(':logic') parts are ignored,
     and calls to @(tsee return-last) that result from @(tsee mbe)s
     are accepted.")
   (xdoc::p
    "The returned list of function names should have no duplicates,
     but we double-check that for robustness.
     The list is in no particular order."))
  (b* (((run-when verbose$)
        (cw "~%ACL2 functions to translate to Java:~%"))
       ((er fns) (atj-fns-to-translate-aux targets$
                                           nil
                                           deep$
                                           guards$
                                           verbose$
                                           ctx
                                           state))
       ((unless (no-duplicatesp-eq fns))
        (value (raise "Internal error: ~
                       the list ~x0 of collected function names ~
                       has duplicates."
                      fns))))
    (value fns))

  :prepwork
  ((define atj-fns-to-translate-aux ((worklist symbol-listp)
                                     (acc symbol-listp)
                                     (deep$ booleanp)
                                     (guards$ booleanp)
                                     (verbose$ booleanp)
                                     ctx
                                     state)
     :returns (mv erp ; BOOLEANP
                  fns ; SYMBOL-LISTP
                  state)
     :mode :program
     :parents nil
     (b* (((when (endp worklist)) (value acc))
          ((cons fn worklist) worklist)
          ((when (atj-aij-nativep fn))
           (atj-fns-to-translate-aux
            worklist acc deep$ guards$ verbose$ ctx state))
          ((when (and (eq deep$ nil)
                      (eq guards$ t)
                      (member-eq fn *atj-primitive-fns*)))
           (atj-fns-to-translate-aux
            worklist acc deep$ guards$ verbose$ ctx state))
          ((when (and (rawp fn state)
                      (not (pure-raw-p fn))))
           (er-soft+ ctx t nil "The function ~x0 has raw Lisp code ~
                                and is not in the whitelist; ~
                                therefore, code generation cannot proceed." fn))
          (body (getpropc fn 'unnormalized-body))
          ((unless body)
           (er-soft+ ctx t nil
                     "The function ~x0 has no UNNORMALIZED-BODY property ~
                      and is not implemented natively in AIJ; ~
                      therefore, code generation cannot proceed." fn))
          ((unless (no-stobjs-p fn (w state)))
           (er-soft+ ctx t nil
                     "The function ~x0 has input or output stobjs; ~
                      therefore, code generation cannot proceed." fn))
          ((run-when verbose$)
           (cw "  ~x0~%" fn))
          (acc (add-to-set-eq fn acc))
          (body (if guards$
                    (remove-mbe-logic-from-term body)
                  (remove-mbe-exec-from-term body)))
          (called-fns (all-ffn-symbs body nil))
          (fns-to-add-to-worklist (set-difference-eq called-fns acc))
          (worklist (union-eq fns-to-add-to-worklist worklist)))
       (atj-fns-to-translate-aux
        worklist acc deep$ guards$ verbose$ ctx state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gather-info ((targets$ symbol-listp)
                         (deep$ booleanp)
                         (guards$ booleanp)
                         (verbose$ booleanp)
                         ctx
                         state)
  :returns (mv erp
               (result "A tuple @('(pkgs
                                    fns-to-translate)')
                        satisfying
                        @('(typed-tuplep string-listp
                                         symbol-listp
                                         result)'),
                        where @('pkgs') is the list of names of
                        all known packages in chronological order,
                        and @('fns-to-translate') are
                        the functions to translate to Java.")
               state)
  :mode :program
  :short "Gather the information about the ACL2 environment
          needed to generate Java code."
  (b* ((pkgs (known-packages state))
       ((run-when verbose$)
        (cw "~%Known ACL2 packages:~%")
        (atj-show-pkgs pkgs))
       ((er fns-to-translate)
        (atj-fns-to-translate targets$ deep$ guards$ verbose$ ctx state)))
    (value (list pkgs fns-to-translate)))

  :prepwork
  ((define atj-show-pkgs ((pkgs string-listp))
     :returns (nothing null)
     :parents nil
     (if (endp pkgs)
         nil
       (b* ((- (cw "  ~s0~%" (car pkgs))))
         (atj-show-pkgs (cdr pkgs)))))))
