; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-user-term (x (wrld plist-worldp))
  :returns (mv (term/message "A @(tsee pseudo-termp) or @(tsee msgp).")
               (stobjs-out "A @(tsee symbol-listp)."))
  :mode :program
  :parents (std/system/term-queries)
  :short (xdoc::topstring
          "Recognize "
          (xdoc::seetopic "term" "untranslated")
          " terms that are valid for evaluation.")
  :long
  (xdoc::topstring
   (xdoc::p
    "An untranslated @(see term) is a term as entered by the user.
     This function checks @('x') by attempting to translate it.
     If the translation succeeds, the translated term is returned,
     along with the @(tsee stobjs-out) list of the term (see below for details).
     Otherwise, a structured error message is returned (printable with @('~@')),
     along with @('nil') as @(tsee stobjs-out) list.
     These two possible outcomes can be distinguished by the fact that
     the former yields a "
    (xdoc::seetopic "pseudo-termp" "pseudo-term")
    " while the latter does not.")
   (xdoc::p
    "The @(tsee stobjs-out) list of a term is the term analogous
     of the @(tsee stobjs-out) property of a function,
     namely a list of symbols that is like a ``mask'' for the result.
     A @('nil') in the list means that
     the corresponding result is a non-@(see stobj) value,
     while the name of a @(see stobj) in the list means that
     the corresponding result is the named @(see stobj).
     The list is a singleton, unless the term returns "
    (xdoc::seetopic "mv" "multiple values")
    ".")
   (xdoc::p
    "The @(':stobjs-out') and @('((:stobjs-out . :stobjs-out))') arguments
     passed to @('translate1-cmp') as bindings
     mean that the term is checked to be valid for evaluation.
     This is stricter than checking the term to be valid for use in a theorem,
     and weaker than checking the term to be valid
     for use in the body of an executable function;
     these different checks are performed by passing different values
     to the second and third arguments of @('translate1-cmp')
     (see the ACL2 source code for details).
     However, for terms whose functions are all in logic mode,
     validity for evaluation and validity for executable function bodies
     should coincide.")
   (xdoc::p
    "If @('translate1-cmp') is successful,
     it returns updated bindings that associate @(':stobjs-out')
     to the output stobjs of the term.")
   (xdoc::p
    "The @(tsee check-user-term) function does not terminate
     if the translation expands an ill-behaved macro that does not terminate."))
  (mv-let (ctx term/message bindings)
    (translate1-cmp x
                    :stobjs-out
                    '((:stobjs-out . :stobjs-out))
                    t
                    __function__
                    wrld
                    (default-state-vars nil))
    (declare (ignore ctx))
    (if (pseudo-termp term/message)
        (mv term/message
            (cdr (assoc :stobjs-out bindings)))
      (mv term/message nil))))
