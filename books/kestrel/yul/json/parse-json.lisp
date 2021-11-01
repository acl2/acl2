; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/json/parser-output-to-abstract-syntax" :dir :system)
(include-book "kestrel/json/json-bstar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parse-yul-json
  :parents (yul-json)
  :short "Parse JSON file containing Yul IR."
  :long
  (xdoc::topstring
   (xdoc::p
    "We extract Yul IR in surface syntax form from a JSON file produced by the
  Solidity Compiler."))
  :order-subtopics t
  :default-parent t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This section contains some adaptations that were found to be useful in another project.
;; It would be good to work out why and see if there is a better way to handle them.

(in-theory (enable json::value-kind
                   ;; all the light-ast-check functions used by json::pattern
                   json::jnullp json::jtruep json::jfalsep
                   json::jstringp json::jnumberp
                   json::top-jarrayp json::top-jobjectp
                   json::top-jmemberp json::top-jmember-listp))

;; These are disabled for performance.  Can be re-enabled if needed.
;; These were found by accumulated persistence.
;; These are the top 11 that had zero "useful" usages when loading this file.
#||
;; This list is from another project.  Some of these are not in the world
;; when this file is certified, so this list is commented out now.
;; If we need the performance boost then we can reintroduce an
;; appropriately-shortened list.
(local (in-theory (disable ACL2::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP
                           TRUE-LIST-LISTP
                           SET::SETS-ARE-TRUE-LISTS-CHEAP
                           ACL2::TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP
                           DEFAULT-CDR
                           SET::SETP-TYPE
                           SETP-WHEN-TYPE-OPTION-SETP
                           OMAP::SETP-WHEN-MAPP
                           SETP-WHEN-IDENTIFIER-SETP
                           SET::NONEMPTY-MEANS-SET
                           ACL2::TRUE-LIST-LISTP-WHEN-NOT-CONSP)))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This function currently requires that both "ir" and "irOptimized"
;; are in the specific place in the JSON.
;; Also assumes there is only one filename under "contracts".
;; It is easy to adjust this or make it more general if need be.

(define json-to-irs ((yul-object-json json::valuep))
   :returns (mv (erp booleanp) (irs-pair consp))
   :short "Extracts Yul IR surface syntax strings from a JSON fty structure."
   (b* (((unless (and (json::valuep yul-object-json) (json::value-case yul-object-json :object)))
         (mv t '("" . "")))
        ((json::pattern (:object (:member "contracts"
                                          (:object (:member _
                                                            (:object (:member "object"
                                                                              (:object (:member "evm" _)
                                                                                       (:member "ir" (:string ir-string))
                                                                                       (:member "irOptimized" (:string iroptimized-string))))))))
                                 *..))
         yul-object-json)
        ((unless (and json::match?
                      (stringp ir-string)
                      (stringp iroptimized-string)))
         (mv t '("" . ""))))
     (mv nil (cons ir-string iroptimized-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; solc-json-file-to-irs
;; See below for a solc command that uses a "--standard-json" control file
;; and generates a JSON structure with before and after IR in surface syntax form.
;; The surface syntax strings remain in ACL2 strings that are actually arrays of
;; 8-bit bytes in UTF-8.

(define solc-json-file-to-irs ((json-filename stringp) state)
    :returns (mv (erp booleanp)
               (irs-pair consp)
               state)
  :short "Extracts Yul IR surface syntax strings from the file named by @('json-filename')."
  (b* (((mv erp j state) (acl2::parse-file-as-json json-filename state))
       ;; Although acl2::parse-file-as-json parses the bytes rather than
       ;; decoding unicode, that is fine for JSON since the only place nonascii
       ;; chars can occur is in strings.
       ;; This means the s-expression form of j contains strings in the file's
       ;; encoding, usually utf-8.
       ;; NOTE: If the "ir" and "irOptimized" are there but one or both are the
       ;; empty string, the error flag is NOT set.  The caller must handle this
       ;; possibility.
       ((when erp) (mv t '("" . "") state))
       ;; convert s-expression json abstract syntax to fty typed json abstract syntax
       ((mv erp tj) (json::parsed-to-value j))
       ((when erp) (mv t '("" . "") state))
       ;; pick out the ir components
       ((mv erp ir-pair) (json-to-irs tj))
       ((when (or erp (not (consp ir-pair)))) (mv t '("" . "") state)))
    (mv nil ir-pair state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example.

;; Let's say we have an inline Yul file in a Yul Object Notation JSON file
;; called power2.yon with this content:
#||
{
    "language": "Yul",
    "sources": { "pow2.yul": { "content": "{
    function power(base, exponent) -> result
    {
        result := 1
        for { let i := 0 } lt(i, exponent) { i := add(i, 1) }
        {
            result := mul(result, base)
        }
    }
}" } },
    "settings": {
        "outputSelection": { "*": { "*": ["*"], "": [ "*" ] } },
        "optimizer": { "enabled": true,
                        "details": { "yul": true ,
                                     "yulDetails": {"optimizerSteps": "o"} }}
    }
}
||#

;; Then we generate the IR with this command:
;;
;;   solc --standard-json  --pretty-json --input-file power2.yon > power2irs.json

;; We can extract the "ir" and "irOptimized" fields with:
;;
;;   (solc-json-file-to-irs "/path-to/power2irs.json" state)
;;
;; The result is two values, error-flag and a cons pair of (ir . irOptimized)
;; that should look like this:
#||
 ("object \"object\" {
    code {
        function power(base, exponent) -> result
        {
            result := 1
            for { let i := 0 } lt(i, exponent) { i := add(i, 1) }
            { result := mul(result, base) }
        }
    }
}
"
  .
  "object \"object\" {
    code {
        { }
        function power(base, exponent) -> result
        {
            result := 1
            let i := 0
            for { } lt(i, exponent) { i := add(i, 1) }
            { result := mul(result, base) }
        }
    }
}
")
||#
