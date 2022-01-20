; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")

(include-book "kestrel/utilities/strings/char-kinds" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-identifier-checking
  :parents (static-semantics)
  :short "Static identifier checking of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a very simple check that
     all the identifiers in Yul code are well-formed.
     This check may go away altogether if we were to
     build these constraints into the definition of identifiers,
     which may do at some point.
     But for now, it is an explicit check.")
   (xdoc::p
    "We only check identifiers at the points in which they are declared.
     The static safey checks ensure that every used identifier is declared,
     so there is no need to check uses of identifiers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-identifier ((iden identifierp))
  :returns (_ resulterr-optionp)
  :short "Check if an identifier is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must consists of only
     letter (lowercase and uppercase),
     (decimal) digits,
     underscores, and
     dollars.
     It must be non-empty and not start with a digit.")
   (xdoc::p
    "We may move these requirements into an invariant of @(tsee identifier),
     but for now we state them as part of the static semantics."))
  (b* ((chars (str::explode (identifier->get iden))))
    (if (and (consp chars)
             (acl2::alpha/uscore/dollar-char-p (car chars))
             (acl2::alpha/digit/uscore/dollar-charlist-p (cdr chars)))
        nil
      (err (list :bad-identifier (identifier-fix iden)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-identifier-list ((idens identifier-listp))
  :returns (_ resulterr-optionp)
  :short "Check if all the identifiers in a list are well-formed."
  (b* (((when (endp idens)) nil)
       ((ok &) (check-identifier (car idens)))
       ((ok &) (check-identifier-list (cdr idens))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-identifiers-statements/blocks/cases/fundefs
  :short "Check the well-formedness of identifiers declared in
          statements, blocks, cases, and function definitions."

  (define check-identifiers-statement ((stmt statementp))
    :returns (_ resulterr-optionp)
    :short "Check the well-formedness of identifiers declared in statements."
    (statement-case
     stmt
     :block (check-identifiers-block stmt.get)
     :variable-single (check-identifier stmt.name)
     :variable-multi (check-identifier-list stmt.names)
     :assign-single nil
     :assign-multi nil
     :funcall nil
     :if (check-identifiers-block stmt.body)
     :for (b* (((ok &) (check-identifiers-block stmt.init))
               ((ok &) (check-identifiers-block stmt.update))
               ((ok &) (check-identifiers-block stmt.body)))
            nil)
     :switch  (b* (((ok &) (check-identifiers-swcase-list stmt.cases))
                   ((ok &) (check-identifiers-block-option stmt.default)))
                nil)
     :leave nil
     :break nil
     :continue nil
     :fundef (check-identifiers-fundef stmt.get))
    :measure (statement-count stmt))

  (define check-identifiers-statement-list ((stmts statement-listp))
    :returns (_ resulterr-optionp)
    :short "Check the well-formedness of identifiers
            declared in a list of statements."
    (b* (((when (endp stmts)) nil)
         ((ok &) (check-identifiers-statement (car stmts)))
         ((ok &) (check-identifiers-statement-list (cdr stmts))))
      nil)
    :measure (statement-list-count stmts))

  (define check-identifiers-block ((block blockp))
    :returns (_ resulterr-optionp)
    :short "Check the well-formedness of identifiers declared in a block."
    (check-identifiers-statement-list (block->statements block))
    :measure (block-count block))

  (define check-identifiers-block-option ((block? block-optionp))
    :returns (_ resulterr-optionp)
    :short "Check the well-formedness of identifiers
            declared in an optional block."
    (block-option-case
     block?
     :none nil
     :some (check-identifiers-block block?.val))
    :measure (block-option-count block?))

  (define check-identifiers-swcase ((case swcasep))
    :returns (_ resulterr-optionp)
    :short "Check the well-formedness of identifiers
            declared in cases of switch statements."
    (check-identifiers-block (swcase->body case))
    :measure (swcase-count case))

  (define check-identifiers-swcase-list ((cases swcase-listp))
    :returns (_ resulterr-optionp)
    :short "Check the well-formedness of identifiers
            declared in lists of cases of switch statements."
    (b* (((when (endp cases)) nil)
         ((ok &) (check-identifiers-swcase (car cases)))
         ((ok &) (check-identifiers-swcase-list (cdr cases))))
      nil)
    :measure (swcase-list-count cases))

  (define check-identifiers-fundef ((fundef fundefp))
    :returns (_ resulterr-optionp)
    :short "Check the well-formedness of identifiers
            declared in function definitions."
    (b* (((ok &) (check-identifier (fundef->name fundef)))
         ((ok &) (check-identifiers-block (fundef->body fundef))))
      nil)
    :measure (fundef-count fundef))

  ///

  (fty::deffixequiv-mutual check-identifiers-statements/blocks/cases/fundefs))
