; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "../codepoint-utilities")
(include-book "syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-interface
  :parents (parsing-and-printing)
  :short "Public parsing API for Futhark IR text."
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions wrap the core parser with IR-specific names, so that
     a future ordinary Futhark source parser can add its own public API
     without competing for generic names such as @('parse-program').")
   (xdoc::p
    "The CST entry point returns an ABNF tree result.  The AST entry points
     reject trailing input and then run @(tsee abs-program), so callers see a
     single @(tsee fut-program-resultp) value.")
   (xdoc::p
    "ACL2 strings are treated as UTF-8 byte strings.  The public string entry
     decodes them to Unicode code points before calling the core parser, just
     as the Remora front end does.")
   (xdoc::p
    "The code-point entry point @(tsee parse-ir-from-codepoints) is
     useful when the caller has already decoded input bytes.  The string entry
     point @(tsee parse-ir-from-string) is the usual in-memory API.
     File and directory convenience functions can be added later following the
     Remora parser-interface pattern."))
  :order-subtopics t
  :default-parent t)

(define parse-ir-cst-from-codepoints ((input nat-listp))
  :returns (tree abnf::tree-resultp)
  (b* (((mv tree rest-input) (parse-program input))
       ((when (reserrp tree)) (reserrf-push tree))
       ((when (consp rest-input))
        (reserrf (list :unconsumed-input rest-input))))
    tree))

(define parse-ir-from-codepoints ((input nat-listp))
  :returns (program fut-program-resultp)
  (b* ((tree (parse-ir-cst-from-codepoints input))
       ((when (reserrp tree)) (reserrf-push tree)))
    (abs-program tree)))

(define parse-ir-from-string ((input stringp))
  :returns (program fut-program-resultp)
  (b* ((codepoints (decode-utf8-string input))
       ((when (reserrp codepoints)) codepoints))
    (parse-ir-from-codepoints codepoints)))
