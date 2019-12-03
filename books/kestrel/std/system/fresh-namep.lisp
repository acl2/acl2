; Standard System Library
;
; Copyright (C) 2019 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc fresh-namep
  :parents (std/system/event-name-queries)
  :short "Utilities to check the freshness of event names.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-namep-msg-weak ((name symbolp) type (wrld plist-worldp))
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (msg/nil "A message (see @(tsee msg)) or @('nil').")
  :mode :program
  :parents (fresh-namep)
  :short "Return either @('nil') or
          a message indicating why the name is not a legal new name."
  :long
  (xdoc::topstring-p
   "This helper function for @(tsee fresh-namep-msg) avoids
    the ``virginity'' check ensuring that the name
    is not already defined in raw Lisp.
    See @(tsee fresh-namep-msg).")
  (flet ((not-new-namep-msg (name wrld)
                            ;; It is tempting to report that the properties
                            ;; 'global-value, 'table-alist, 'table-guard are
                            ;; not relevant for this check.  But that would
                            ;; probably make the message confusing.
                            (let ((old-type (logical-name-type name wrld t)))
                              (cond
                               (old-type
                                (msg "~x0 is already the name for a ~s1."
                                     name
                                     (case old-type
                                       (function "function")
                                       (macro "macro")
                                       (const "constant")
                                       (stobj "stobj")
                                       (constrained-function
                                        "constrained function"))))
                               (t
                                (msg "~x0 has properties in the world; it is ~
                                      not a new name."
                                     name))))))
    (cond
     ((mv-let (ctx msg)
        (chk-all-but-new-name-cmp name 'fresh-namep-msg type wrld)
        (and ctx ; it's an error
             msg)))
     ((not (new-namep name wrld))
      (not-new-namep-msg name wrld))
     (t (case type
          (const
           (and (not (legal-constantp name))
                ;; A somewhat more informative error message is produced by
                ;; chk-legal-defconst-name, but I think the following suffices.
                (msg "~x0 is not a legal constant name."
                     name)))
          (stobj
           (and (not (new-namep (the-live-var name) wrld))
                (not-new-namep-msg (the-live-var name) wrld)))
          (t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-namep-msg ((name symbolp) type (wrld plist-worldp) state)
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (mv (erp "Always @('nil').")
               (msg/nil "A message (see @(tsee msg)) or @('nil').")
               state)
  :mode :program
  :parents (fresh-namep)
  :short "Return either @('nil') or
          a message indicating why the name is not a legal new name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns an <see topic='@(url error-triple)'>error triple</see>
     @('(mv nil msg/nil state)'),
     where @('msg/nil') is either @('nil') or
     a message (see @(tsee msg)) indicating why the given name
     is not legal for a definition of the given type:
     @('function') for @(tsee defun),
     @('macro') for @(tsee defmacro),
     @('const') for @(tsee defconst),
     @('stobj') for @(tsee defstobj),
     @('constrained-function') for @(tsee defchoose),
     and otherwise @('nil') (for other kinds of @(see events),
     for example @(tsee defthm) and @(tsee deflabel)).
     See @(see name).")
   (xdoc::p
    "WARNING: This is an incomplete check in the case of a stobj name,
     because the field names required for a more complete check
     are not supplied as inputs.")
   (xdoc::p
    "Implementation Note.  This function modifies @(see state),
     because the check for legality of new definitions
     (carried out by ACL2 source function @('chk-virgin-msg')) modifies state.
     That modification is necessary because for all we know,
     raw Lisp is adding or removing function definitions
     that we don't know about without our having modified state;
     so logically, we pop the oracle when making this check.
     End of Implementation Note."))
  (let ((msg (fresh-namep-msg-weak name type wrld)))
    (cond (msg (value msg))
          (t (mv-let (msg state)
               (chk-virgin-msg name type wrld state)
               (value msg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chk-fresh-namep ((name symbolp) type ctx (wrld plist-worldp) state)
  :guard (member-eq type
                    '(function macro const stobj constrained-function nil))
  :returns (mv erp val state)
  :mode :program
  :parents (fresh-namep)
  :short "Check whether name is a legal new name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns an <see topic='@(url error-triple)'>error triple</see>
     @('(mv erp val state)')
     where @('erp') is @('nil') if and only if
     name is a legal new name, and @('val') is irrelevant.
     If @('erp') is not nil, then an explanatory error message is printed.")
   (xdoc::p
    "For more information about legality of new names
     see @(tsee fresh-namep-msg),
     which returns an <see topic='@(url error-triple)'>error triple</see>,
     @('(mv nil msg/nil state)').
     When non-@('nil'), the value @('msg/nil') provides
     the message printed by @('chk-fresh-namep')."))
  (er-let* ((msg (fresh-namep-msg name type wrld state))) ; never an error
    (cond (msg (er soft ctx "~@0" msg))
          (t (value nil)))))
