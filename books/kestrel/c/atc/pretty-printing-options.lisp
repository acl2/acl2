; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "centaur/fty/top" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-pretty-printing-options
  :parents (atc-implementation)
  :short "Options for the ATC pretty-printer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide an extensible collection of options
     for how ATC pretty-prints C code.
     Currently we only support one simple options,
     but we may add possibly many more options,
     e.g. to control indentation, maximum line length, and so on."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pprint-options
  :short "Fixtype of pretty-printing options."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we just support a single flag saying whether
     nested conditional (ternary) expressions should be parenthesized.
     The meaning of this is explained in more detail
     in the user documentation and in the pretty-printer."))
  ((parenthesize-nested-conditionals bool)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-pprint-options ()
  :returns (irr pprint-options-p)
  :short "An irrelevant value of pretty-printing options."
  (make-pprint-options :parenthesize-nested-conditionals nil)
  ///
  (in-theory (disable (:e irr-pprint-options))))
