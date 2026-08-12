; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Sarah Johnson

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "deserializer")

(include-book "kestrel/json/top" :dir :system)
(include-book "kestrel/json-parser/parse-json-file" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the file-I/O entry point for deserialization.  It is kept in a
; separate book from deserializer.lisp so that the core deserialization
; logic does not have to depend on (and pay the certification-load cost of)
; the JSON parser.

(define deserialize-expr-from-file ((filename stringp) state)
  :parents (deserializer)
  :returns (mv erp (x exprp) state)
  :short "Parse a JSON file and convert its contents to a @(tsee expr)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads and parses @('filename') as JSON
     (via @('parse-file-as-json')),
     converts the parsed result to a @(tsee json::valuep)
     (via @(tsee json::parsed-to-value)),
     and converts that to an @(tsee expr) via @(tsee expr-fromJSON).
     Returns @('(mv erp x state)'), where @('erp') is non-@('nil')
     (an error message) if any of these steps fails, in which case
     @('x') is an irrelevant placeholder @(tsee expr)."))
  (b* (((mv erp parsed state)
        (acl2::parse-file-as-json filename state))
       ((when erp)
        (b* ((- (cw "Error parsing ~s0 as JSON: ~x1.~%" filename erp)))
          (mv erp (make-expr-var :name "") state)))
       ((mv erp value)
        (json::parsed-to-value parsed))
       ((when erp)
        (b* ((- (cw "The JSON parsed from ~s0 is malformed.~%" filename)))
          (mv erp (make-expr-var :name "") state)))
       ((mv erp exp)
        (expr-fromJSON value))
       ((when erp)
        (b* ((- (cw "Error converting the JSON value from ~s0 ~
                     to a Remora expression: ~@1~%" filename erp)))
          (mv erp (make-expr-var :name "") state))))
    (mv nil exp state)))

(define deserialize-file-from-file ((filename stringp) state)
  :parents (deserializer)
  :returns (mv erp (x filep) state)
  :short "Parse a JSON file and convert its contents to a @(tsee file)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads and parses @('filename') as JSON
     (via @('parse-file-as-json')),
     converts the parsed result to a @(tsee json::valuep)
     (via @(tsee json::parsed-to-value)),
     and converts that to a @(tsee file) via @(tsee file-fromJSON).
     Returns @('(mv erp x state)'), where @('erp') is non-@('nil')
     (an error message) if any of these steps fails, in which case
     @('x') is an irrelevant placeholder @(tsee file)."))
  (b* (((mv erp parsed state)
        (acl2::parse-file-as-json filename state))
       ((when erp)
        (b* ((- (cw "Error parsing ~s0 as JSON: ~x1.~%" filename erp)))
          (mv erp (make-file :imports nil :decls nil) state)))
       ((mv erp value)
        (json::parsed-to-value parsed))
       ((when erp)
        (b* ((- (cw "The JSON parsed from ~s0 is malformed.~%" filename)))
          (mv erp (make-file :imports nil :decls nil) state)))
       ((mv erp exp)
        (file-fromJSON value))
       ((when erp)
        (b* ((- (cw "Error converting the JSON value from ~s0 ~
                     to a Remora file: ~@1~%" filename erp)))
          (mv erp (make-file :imports nil :decls nil) state))))
    (mv nil exp state)))
