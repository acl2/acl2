; World Queries
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains utilities for querying ACL2 worlds
; that complement the world query utilities in the ACL2 source code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)

(local (set-default-parents world-queries))

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc world-queries
  :parents (kestrel-system-utilities system-utilities)
  :short "Utilities to query <see topic='@(url world)'>worlds</see>."
  :long
  "<p>
  These complement the world query utilities
  in the <see topic='@(url system-utilities)'>built-in system utilities</see>.
  </p>")

(define theorem-symbolp ((sym symbolp) (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the symbol @('sym') names a theorem,
  i.e. it has a @('theorem') property."
  (not (eq t (getpropc sym 'theorem t w))))

(define macro-symbolp ((sym symbolp) (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff the symbol @('sym') names a macro."
  (not (eq (getpropc sym 'macro-args t w) t)))

(define function-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a function."
  (and (symbolp x) (function-symbolp x w)))

(define theorem-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a theorem."
  (and (symbolp x) (theorem-symbolp x w)))

(define macro-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a macro."
  (and (symbolp x) (macro-symbolp x w)))

(define definedp ((fun (function-namep fun w)) (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the function @('fun') is defined,
  i.e. it has an @('unnormalized-body') property."
  (not (eq t (getpropc fun 'unnormalized-body t w))))

(define guard-verified-p ((fun/thm (or (function-namep fun/thm w)
                                       (theorem-namep fun/thm w)))
                          (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the function or theorem @('fun/thm') is @(tsee guard)-verified."
  (eq (symbol-class fun/thm w) :common-lisp-compliant))

(define non-executablep ((fun (and (function-namep fun w)
                                   (definedp fun w)))
                         (w plist-worldp))
  :returns (result (member result '(t nil :program)))
  :short "The @(tsee non-executable) status of the defined function @('fun')."
  (getpropc fun 'non-executablep nil w))

(define unwrapped-nonexec-body ((fun (and (function-namep fun w)
                                          (non-executablep fun w)))
                                (w plist-worldp))
  :returns (unwrapped-body pseudo-termp)
  :short
  "Body of a non-executable function,
  without the &ldquo;non-executable wrapper&rdquo;."
  :long
  "<p>
  @(tsee defun-nx) wraps the body of the function @('fun') being defined
  in a wrapper that has
  the following <see topic='@(url term)'>translated</see> form:
  </p>
  @({
    (return-last 'progn
                 (throw-nonexec-error 'fun
                                      (cons arg1 ... (cons argN 'nil)...))
                 body)
  })
  <p>
  If @(tsee defun) is used with
  <see topic='@(url non-executable)'>@(':non-executable')</see> set to @('t'),
  the submitted body (once translated) must be wrapped like that.
  </p>
  <p>
  @(tsee unwrapped-nonexec-body) returns
  the unwrapped body of the non-executable function @('fun').
  </p>"
  (fourth (body fun nil w)))

(define no-stobjs-p ((fun (function-namep fun w)) (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the function @('fun') has no
  input or output <see topic='@(url stobj)'>stobjs</see>."
  (and (equal (stobjs-in fun w) (repeat (len (stobjs-in fun w)) nil))
       (equal (stobjs-out fun w) (repeat (len (stobjs-out fun w)) nil))))

(define measure ((fun (and (function-namep fun w)
                           (logicalp fun w)
                           (recursivep fun w)))
                 (w plist-worldp))
  :returns (measure pseudo-termp)
  :short "Measure expression of a logic-mode recursive function."
  :long "<p>See @(see xargs) for a discussion of the @(':measure') keyword.</p>"
  (access justification (getpropc fun 'justification nil w) :measure))

(define well-founded-relation ((fun (and (function-namep fun w)
                                         (logicalp fun w)
                                         (recursivep fun w)))
                               (w plist-worldp))
  :returns (well-founded-relation symbolp)
  :short "Well-founded relation of a logic-mode recursive function."
  :long
  "<p>See @(see well-founded-relation-rule)
  for a discussion of well-founded relations in ACL2,
  including the @(':well-founded-relation') rule class.</p>"
  (access justification (getpropc fun 'justification nil w) :rel))

(define ruler-extenders ((fun (and (function-namep fun w)
                                   (logicalp fun w)
                                   (recursivep fun w)))
                         (w plist-worldp))
  :returns (ruler-extenders (or (symbol-listp ruler-extenders)
                                (equal ruler-extenders :all)))
  :short
  "<see topic='@(url rulers)'>Ruler</see> extenders
  of a logic-mode recursive function."
  (access justification (getpropc fun 'justification nil w) :ruler-extenders))

(define macro-required-args ((mac (macro-namep mac w)) (w plist-worldp))
  :returns (required-args symbol-listp)
  :short "Required arguments of the macro @('mac'), in order."
  :long
  "<p>
  The arguments of a macro form a list that
  optionally starts with @('&whole') followed by another symbol,
  continues with zero or more symbols that do not start with @('&')
  which are the required arguments,
  and possibly ends with a symbol starting with @('&') followed by more symbols.
  </p>"
  (let ((all-args (macro-args mac w)))
    (if (null all-args)
        nil
      (if (eq (car all-args) '&whole)
          (macro-required-args-aux (cddr all-args))
        (macro-required-args-aux all-args))))

  :prepwork
  ((define macro-required-args-aux ((args symbol-listp))
     :returns (required-args symbol-listp)
     :parents (macro-required-args)
     :short "Auxiliary function of @(tsee macro-required-args)."
     :long
     "<p>
     After removing @('&whole') and the symbol following it
     (if the list of arguments starts with @('&whole')),
     collect all the arguments until
     either the end of the list is reached
     or a symbol starting with @('&') is encountered.
     </p>"
     (if (endp args)
         nil
       (let ((arg (car args)))
         (if (eql (char (symbol-name arg) 0) #\&)
             nil
           (cons arg (macro-required-args-aux (cdr args)))))))))

(define fundef-enabledp ((fun (function-namep fun (w state))) state)
  :returns (yes/no booleanp)
  :short "True iff the definition of the function @('fun') is enabled."
  (not (member-equal `(:definition ,fun) (disabledp fun))))

(define rune-enabledp ((rune (runep rune (w state))) state)
  :returns (yes/no booleanp)
  :short "True iff the @(see rune) @('rune') is enabled."
  (not (member-equal rune (disabledp (cadr rune)))))

(define included-books ((w plist-worldp))
  :returns (result string-listp)
  :short
  "List of full pathnames of all books currently included
  (directly or indirectly)."
  (strip-cars (global-val 'include-book-alist w)))
