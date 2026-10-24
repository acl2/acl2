; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")
(include-book "parse-error-printing")
(include-book "validator")
(include-book "utility-transforms")
(include-book "pretty-printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ elaborator
  :parents (validator)
  :short "A prototype elaborator for Remora programs,
          with an entry point for the Haskell implementation of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a prototype for demo purposes.
     @(tsee elaborate-file) infers the omitted type and ispace applications
     in the declarations of a file,
     using the inference performed by the @(see validator).
     The entry point, @(tsee elaborate-program-string),
     parses a string containing a Remora program,
     elaborates it,
     and prints the elaborated program on standard output
     between marker lines.")
   (xdoc::p
    "The Haskell implementation of Remora, on its @('acl2-infer') branch,
     calls @(tsee elaborate-program-string)
     for @('remora interpret --acl2-infer ...')
     and @('remora futhark --acl2-infer ...')
     when type checking fails because of missing type or ispace applications.
     The program is passed as a string
     so that it can be sent to ACL2 over a pipe, e.g. into a container.
     The result is printed as")
   (xdoc::codeblock
    "<<<remora-acl2 elaborated>>>"
    "the elaborated program"
    "<<<remora-acl2 end>>>")
   (xdoc::p
    "or, if the program cannot be elaborated, as")
   (xdoc::codeblock
    "<<<remora-acl2 parse-error>>>"
    "details"
    "<<<remora-acl2 end>>>")
   (xdoc::p
    "with @('type-error') or @('print-error') in place of @('parse-error')
     when that is what went wrong."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; NOTE: Although this works for a demo, it is not how we want to do type
; checking/inference on declarations.  Here's a plan for that.

; * check-decl would take the static environments and one declaration, and
;   return the extended environments plus the elaborated declaration

; * check-file would thread check-decl through the file

; * The existing eval-from-file and the other *-from-file functions
;   would run check-file and work from the elaborated file.
;   (file-to-expr can remain for evaluation, applied to a file that has already
;   been checked.)

; * Prove a theorem that says that check-file succeeds exactly when
;   check-top-expr succeeds on the nested-let form, and both produce the
;   same elaborated bodies.

; * To modularize, separate the pure passes from I/O.
;   Split each *-from-file book into a pure pass and one shared driver
;   that reads a program from a file or a string, runs the passes,
;   and prints the result.
;   elaborate-program-string would then be that driver running elaboration.

; This plan would make it (a) easier to do imports and (b) easier for errors to
; name the declaration they occur in.

; Other TODOs:

; * check that the elaboration is the only one.
;   For now, the elaboration returned is the one that
;   the type checker's inference finds, even if other were possible, so
;  there is currently no indication that the input might have been ambiguous.

; * do type checking on arguments other than the first (a current limitation)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peel-let-binds ((n natp) (expr exprp))
  :returns (mv (binds bind-listp) (body exprp))
  :short "Peel up to @('n') nested single-binding @('let')s off an expression."
  (b* (((when (zp n)) (mv nil (expr-fix expr)))
       ((unless (and (expr-case expr :let)
                     (consp (expr-let->binds expr))
                     (endp (cdr (expr-let->binds expr)))))
        (mv nil (expr-fix expr)))
       ((mv binds body) (peel-let-binds (1- n) (expr-let->body expr))))
    (mv (cons (car (expr-let->binds expr)) binds) body)))

(define elaborate-file ((file filep))
  :returns (new-file file-resultp)
  :short "Elaborate a file object:
          infer the omitted type and ispace applications in its declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declarations are turned into nested @('let')s
     (see @(tsee decl-list-to-binds) and @(tsee nest-let-binds))
     around a placeholder body,
     which @(tsee check-top-expr) checks,
     inferring the omitted applications;
     the checked @('let')s are then turned back into declarations.
     File objects with imports are not supported."))
  (b* (((file file) file)
       ((when (consp file.imports)) (reserrf :imports-not-supported))
       (entry-names (decl-list-entry-names file.decls))
       (binds (decl-list-to-binds file.decls))
       (placeholder (make-expr-atom
                     :atom (make-atom-base :lit (make-base-lit-bool :lit t))))
       ((ok te) (check-top-expr (nest-let-binds binds placeholder)))
       ((mv new-binds &) (peel-let-binds (len binds) (type+expr->expr te)))
       ((unless (= (len new-binds) (len binds)))
        (reserrf :unexpected-checker-result)))
    (make-file :imports nil
               :decls (bind-list-to-decls new-binds entry-names)))
  :guard-hints (("Goal" :in-theory (enable type+expr-p-when-result-not-error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The marker and the entry point.  They are in program mode because that was
; easier for now.

(define elaborator-marker ((kind stringp) state)
  :mode :program
  :short "Print a marker line of the output of
          @(tsee elaborate-program-string)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The line is @('<<<remora-acl2 kind>>>'), preceded by a newline."))
  (pprogn (newline *standard-co* state)
          (princ$ "<<<remora-acl2 " *standard-co* state)
          (princ$ kind *standard-co* state)
          (princ$ ">>>" *standard-co* state)
          (newline *standard-co* state)))

(define elaborate-program-string ((text stringp) state)
  :mode :program
  :short "Parse, elaborate, and print a Remora program given as a string."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the entry point described in @(see elaborator).
     The program is parsed with @(tsee parse-from-string),
     elaborated with @(tsee elaborate-file),
     and printed with @(tsee pretty-print-file),
     between marker lines (see @(tsee elaborator-marker)).")
   (xdoc::p
    "The elaborated program is printed with @('princ$') rather than @('cw'),
     because @('cw') breaks long lines at spaces,
     which could split a string literal in the program.")
   (xdoc::p
    "This returns an error triple whose value says what happened:
     @(':elaborated'), @(':parse-error'), @(':type-error'),
     or @(':print-error')."))
  (b* ((file (parse-from-string text))
       ((when (reserrp file))
        (b* ((state (elaborator-marker "parse-error" state))
             (- (print-parse-error file))
             (state (elaborator-marker "end" state)))
          (mv nil :parse-error state)))
       (elaborated (elaborate-file file))
       ((when (reserrp elaborated))
        (b* ((state (elaborator-marker "type-error" state))
             (- (cw "~x0~%" elaborated))
             (state (elaborator-marker "end" state)))
          (mv nil :type-error state)))
       (printed (pretty-print-file elaborated :width 80))
       ((when (equal printed ""))
        (b* ((state (elaborator-marker "print-error" state))
             (state (elaborator-marker "end" state)))
          (mv nil :print-error state)))
       (state (elaborator-marker "elaborated" state))
       (state (princ$ printed *standard-co* state))
       (state (elaborator-marker "end" state)))
    (mv nil :elaborated state)))
