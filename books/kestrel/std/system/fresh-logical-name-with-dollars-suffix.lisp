; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "add-suffix-to-fn-or-const")
(include-book "fresh-namep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-logical-name-with-$s-suffix
  ((name symbolp)
   (type (member-eq type '(function
                           macro
                           const
                           stobj
                           constrained-function
                           nil)))
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (fresh-name symbolp :hyp (symbolp name))
               (updated-names-to-avoid symbol-listp
                                       :hyp (and (symbolp name)
                                                 (symbol-listp
                                                  names-to-avoid))))
  :parents (std/system)
  :short "Suffix a name with as many @('$') signs
          as needed to make it a valid new logical name
          that is also not among a given list of names to avoid."
  :long
  (xdoc::topstring
   (xdoc::p
    "The returned name can be used for a new function, macro, constant, etc.,
     based on the @('type') argument passed to this utility;
     for theorems, use @('nil') as the type.
     (These are all " (xdoc::seetopic "logical-name" "logical names") ".)
     When names for multiple new functions, macros, etc. must be generated,
     the list of names to avoid
     can be threaded through multiple calls of this utility,
     starting with the empty list @('nil')
     and extending it with each name returned by this utility.")
   (xdoc::p
    "The resulting name may be the same as the argument,
     with no @('$') signs added,
     if the argument is already a valid fresh logical name of the given type.")
   (xdoc::p
    "We use @(tsee fresh-namep-msg-weak) to check the freshness of names,
     which may miss names of functions in raw Lisp.
     But the more accurate check @(tsee fresh-namep-msg),
     which takes into account names of functions in raw Lisp,
     is state-changing,
     which would therefore force this utility to be state-changing too.
     Thus, for now we use the weaker check,
     and avoid passing and returning state.
     If we encounter problems in the future,
     we will revise this utility, or introduce a new one.")
   (xdoc::p
    "Not that if the logical name is for a constant,
     the @('$') signs are added just before the final @('*'),
     so that the resulting name is still a valid constant name;
     see @(tsee add-suffix-to-fn-or-const).
     If the name is for a function (constrained or not), macro, or stobj,
     and is in the @('\"COMMON-LISP\"') package,
     the call of @(tsee add-suffix-to-fn-or-const),
     which reduces to @(tsee add-suffix-to-fn) in this case,
     will ``move'' the name to the @('\"ACL2\"') package.
     If the name is for a theorem, in which case @('type') is @('nil'),
     then we just use @(tsee add-suffix),
     because theorem names may be in the @('\"COMMON-LISP\"') package.
     This holds for other types of logical names too
     for which @('type') is @('nil'):
     @(tsee fresh-namep-msg-weak) succeeds when called on
     a symbol in the @('\"COMMON-LISP\"') package and with @('nil') as type.")
   (xdoc::p
    "Since the ACL2 world is finite,
     eventually we must find a fresh name,
     with enough @('$')s.
     Turning this into a termination proof requires a bit of work,
     so for now we use a counter that gets decremented at every recursive call,
     making for an easy termination proof.
     We initialize the counter to 1000,
     which is very large for the expected use cases;
     think of a generated logical name with 1000 @('$')s in it.
     Nonetheless, this is a bit inelegant,
     and we should eventually formalize the termination argument above,
     avoiding the counter altogether."))
  (fresh-logical-name-with-$s-suffix-aux name type names-to-avoid wrld 1000)

  :prepwork
  ((define fresh-logical-name-with-$s-suffix-aux
     ((name symbolp)
      (type (member-eq type '(function
                              macro
                              const
                              stobj
                              constrained-function
                              nil)))
      (names-to-avoid symbol-listp)
      (wrld plist-worldp)
      (counter natp))
     :returns (mv (fresh-name symbolp :hyp (symbolp name))
                  (updated-names-to-avoid symbol-listp
                                          :hyp (and (symbolp name)
                                                    (symbol-listp
                                                     names-to-avoid))))
     (b* (((when (zp counter))
           (raise "Internal error: exhausted counter at ~x0." name)
           (mv name names-to-avoid))
          (msg/nil (fresh-namep-msg-weak name type wrld))
          ((when (or msg/nil
                     (member-eq name names-to-avoid)))
           (fresh-logical-name-with-$s-suffix-aux
            (if type
                (add-suffix-to-fn-or-const name "$")
              (add-suffix name "$"))
            type
            names-to-avoid
            wrld
            (1- counter))))
       (mv name (cons name names-to-avoid)))
     :measure (nfix counter))))
