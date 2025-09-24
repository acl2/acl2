; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../syntax/validation-information")

(include-book "std/system/constant-value" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-processing
  :parents (transformation-tools)
  :short "Utilities to process inputs of C-to-C transformations."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-const-old (const-old (suppliedp booleanp) (wrld plist-worldp))
  :returns (mv erp (code-old code-ensemblep))
  :short "Process the @(':const-old') input of a transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the input was supplied
     and that it is a constant symbol
     whose value is an unambiguous annotate code ensemble.
     We return the code ensemble if successful."))
  (b* (((reterr) (irr-code-ensemble))
       ((unless suppliedp)
        (reterr (msg "The :CONST-OLD input must be supplied.")))
       ((unless (symbolp const-old))
        (reterr (msg "The :CONST-OLD must be a symbol, ~
                      but it is ~x0 instead."
                     const-old)))
       ((unless (constant-symbolp const-old wrld))
        (reterr (msg "The :CONST-OLD input, ~x0, must be a named constant, ~
                      but it is not."
                     const-old)))
       (code-old (constant-value const-old wrld))
       ((unless (code-ensemblep code-old))
        (reterr (msg "The value of the constant ~x0 ~
                      must be a code ensemble, ~
                      but it is ~x1 instead."
                     const-old code-old)))
       ((unless (code-ensemble-unambp code-old))
        (reterr (msg "The code ensemble ~x0 ~
                      that is the value of the constant ~x1 ~
                      must be unambiguous, ~
                      but it is not."
                     code-old const-old)))
       ((unless (code-ensemble-annop code-old))
        (reterr (msg "The code ensemble ~x0 ~
                      that is the value of the constant ~x1 ~
                      must contains validation information, ~
                      but it does not."
                     code-old const-old))))
    (retok code-old))

  ///

  (defret code-ensemble-unambp-of-process-const-old
    (implies (not erp)
             (code-ensemble-unambp code-old)))

  (defret code-ensemble-annop-of-process-const-old
    (implies (not erp)
             (code-ensemble-annop code-old))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-const-new (const-new (suppliedp booleanp))
  :returns (mv erp (const-new symbolp))
  :short "Process the @(':const-new') input of a transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the input was supplied
     and that it is a symbol.
     For now we do not check that it is a fresh constant name
     not already present in the world,
     but we may extend this function to do that.
     We return the input unchanged if successful,
     but with a stronger type provided by the return theorem."))
  (b* (((reterr) nil)
       ((unless suppliedp)
        (reterr (msg "The :CONST-NEW input must be supplied.")))
       ((unless (symbolp const-new))
        (reterr (msg "The :CONST-NEW must be a symbol, ~
                      but it is ~x0 instead."
                     const-new))))
    (retok const-new)))
