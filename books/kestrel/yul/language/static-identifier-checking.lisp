; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")

(include-book "std/strings/letter-digit-uscore-dollar-chars" :dir :system)
(include-book "std/strings/letter-uscore-dollar-chars" :dir :system)

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
     which we may do at some point.
     But for now, it is an explicit check.")
   (xdoc::p
    "We only check identifiers at the points in which they are declared.
     The static safey checks ensure that every used identifier is declared,
     so there is no need to check uses of identifiers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-identifier ((iden identifierp))
  :returns (_ reserr-optionp)
  :short "Check if an identifier is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must consists of only
     letters (lowercase and uppercase),
     (decimal) digits,
     underscores, and
     dollars.
     It must be non-empty and not start with a digit.")
   (xdoc::p
    "We may move these requirements into an invariant of @(tsee identifier),
     but for now we state them as part of the static semantics."))
  (b* ((chars (str::explode (identifier->get iden))))
    (if (and (consp chars)
             (str::letter/uscore/dollar-char-p (car chars))
             (str::letter/digit/uscore/dollar-charlist-p (cdr chars)))
        nil
      (reserrf (list :bad-identifier (identifier-fix iden)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-identifier-list ((idens identifier-listp))
  :returns (_ reserr-optionp)
  :short "Check if all the identifiers in a list are well-formed."
  (b* (((when (endp idens)) nil)
       ((okf &) (check-identifier (car idens)))
       ((okf &) (check-identifier-list (cdr idens))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-identifiers-statements/blocks/cases/fundefs
  :short "Check the well-formedness of identifiers declared in
          statements, blocks, cases, and function definitions."

  (define check-identifiers-statement ((stmt statementp))
    :returns (_ reserr-optionp)
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
     :for (b* (((okf &) (check-identifiers-block stmt.init))
               ((okf &) (check-identifiers-block stmt.update))
               ((okf &) (check-identifiers-block stmt.body)))
            nil)
     :switch  (b* (((okf &) (check-identifiers-swcase-list stmt.cases))
                   ((okf &) (check-identifiers-block-option stmt.default)))
                nil)
     :leave nil
     :break nil
     :continue nil
     :fundef (check-identifiers-fundef stmt.get))
    :measure (statement-count stmt))

  (define check-identifiers-statement-list ((stmts statement-listp))
    :returns (_ reserr-optionp)
    :short "Check the well-formedness of identifiers
            declared in a list of statements."
    (b* (((when (endp stmts)) nil)
         ((okf &) (check-identifiers-statement (car stmts)))
         ((okf &) (check-identifiers-statement-list (cdr stmts))))
      nil)
    :measure (statement-list-count stmts))

  (define check-identifiers-block ((block blockp))
    :returns (_ reserr-optionp)
    :short "Check the well-formedness of identifiers declared in a block."
    (check-identifiers-statement-list (block->statements block))
    :measure (block-count block))

  (define check-identifiers-block-option ((block? block-optionp))
    :returns (_ reserr-optionp)
    :short "Check the well-formedness of identifiers
            declared in an optional block."
    (block-option-case
     block?
     :none nil
     :some (check-identifiers-block block?.val))
    :measure (block-option-count block?))

  (define check-identifiers-swcase ((case swcasep))
    :returns (_ reserr-optionp)
    :short "Check the well-formedness of identifiers
            declared in cases of switch statements."
    (check-identifiers-block (swcase->body case))
    :measure (swcase-count case))

  (define check-identifiers-swcase-list ((cases swcase-listp))
    :returns (_ reserr-optionp)
    :short "Check the well-formedness of identifiers
            declared in lists of cases of switch statements."
    (b* (((when (endp cases)) nil)
         ((okf &) (check-identifiers-swcase (car cases)))
         ((okf &) (check-identifiers-swcase-list (cdr cases))))
      nil)
    :measure (swcase-list-count cases))

  (define check-identifiers-fundef ((fundef fundefp))
    :returns (_ reserr-optionp)
    :short "Check the well-formedness of identifiers
            declared in function definitions."
    (b* (((okf &) (check-identifier (fundef->name fundef)))
         ((okf &) (check-identifiers-block (fundef->body fundef))))
      nil)
    :measure (fundef-count fundef))

  ///

  (fty::deffixequiv-mutual check-identifiers-statements/blocks/cases/fundefs))
