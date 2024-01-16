;;(load "~/quicklisp/setup.lisp")

(ql:quickload :trivia)
;; We don't want the verbose library to init itself when we load it during the build process.
;; This is because it creates a separate thread, and save-exec does not like this.
(push :verbose-no-init *features*)
(ql:quickload :verbose)
(ql:quickload :fset)
(ql:quickload :cl-ansi-text)
(ql:quickload :xmls)

;; Verbose got rid of the v global nickname around March 2023, so we will work around that here
(rename-package ':org.shirakumo.verbose ':org.shirakumo.verbose (cons 'v (package-nicknames (find-package ':org.shirakumo.verbose))))

(defpackage :util (:use :cl :trivia)
  (:export "ASSOC-=="
           "REPLACE-IN" "REPLACE-IN*"
           "CONCAT-SYMS" "CONCAT-SYMS-IN-PACKAGE" "INTERN-SYM-IN-PACKAGE"
           "APPEND-ALL" "ERRORP" "REM-DUPES" "HAS-DUPLICATES?"
           "READ-FILE-INTO-STRING" "READ-IN-PACKAGE"
           "STR-TRIM" "STR-CONCAT" "STR-ENDS-WITH?"
           "OPTIONAL-NUMBER"))

(defpackage :print (:use :cl)
  (:export "SET-PRINT2-FD" "SET-PRINT3-FD"
           "SET-PRINT2-STREAM" "SET-PRINT3-STREAM"
           "PRINT2" "PRINT3"))

(defpackage :defcond (:use :cl)
  (:export :defcond :defcond-condition :long-report :short-report :add-defcond-post-hook :add-defcond-field-hook)
  (:intern :make-defcond-condition-metadata))

(defpackage :acl2s-high-level-interface (:use :cl :util :acl2 :trivia :defcond)
  (:import-from :acl2s-interface-extras :acl2s-query-error? :thm-query-error? :get-hyps :get-conc :conjunction-terms :guard-obligations-query-res-ok? :cnf-disjunct-to-or :acl2s-untranslate :is-theorem?)
  (:import-from :acl2 :in-theory :union-theories :theory)
  (:import-from :acl2s :contract-theory :min-theory :implies :^ :=> :v :! :-> :<-)
  (:export "ACL2S-QUERY-ERROR" "ACL2S-QUERY-ERROR/DESC" "ACL2S-QUERY-ERROR/QUERY" "ACL2S-QUERY-ERROR/ERR"
           "RGUARD-OBLIGATIONS-ERROR" "RGUARD-OBLIGATIONS-ERROR/EXPR" "RGUARD-OBLIGATIONS-ERROR/ERR"
           "TEST-FOUND-CTREX-ERROR" "TEST-FOUND-CTREX-ERROR/MSG" "TEST-FOUND-CTREX-ERROR/CXS" "TEST-FOUND-CTREX-ERROR/QUERY"
           "FULL-THM-FAILED-ERROR" "FULL-THM-FAILED-ERROR/MSG" "FULL-THM-FAILED-ERROR/QUERY"
           "MIN-THM-FAILED-ERROR" "MIN-THM-FAILED-ERROR/MSG" "MIN-THM-FAILED-ERROR/QUERY"
           "INTERNAL-QUERY-ERROR" "UNEXPECTED-RESPONSE-ERROR"
           "PROVER-WARNING" "PROVER-WARNING/MSG"
           "USED-FULL-THEORY" "USED-FULL-THEORY/QUERY"
           "OBLIGATION-THM-FAILED" "OBLIGATION-THM-FAILED/OBLIGATION" "OBLIGATION-THM-FAILED/DEBUG-INFO"
           "LD-INTERNAL-ERROR" "LD-INTERNAL-ERROR/QUERY"
           "LD-EXECUTION-ERROR" "LD-EXECUTION-ERROR/QUERY"
           "*ACL2S-INTERFACE-FAIL-OK*"
           "IS-OP?" "CONJUNCTION-TO-LIST"
           "ITEST?-QUERY" "CONJUNCTION-TERMS" "GET-HYPS" "GET-CONC"
           "TEST?"
           "THM-MIN-THEORY" "THM-FULL-THEORY" "THM-MIN-THEORY-WITH-CONTRACTS"
           "TEST-THM-MIN" "TEST-THM-FULL" "TEST-THM-MIN-THEN-FULL" "TEST-THM-MIN-WITH-CONTRACTS" "TEST-THEN-THM-MIN-FAILS?"
           "RGUARD-OBLIGATIONS" "RGUARD-OBLIGATIONS-DEBUG"
           "REDEFINE-THEORIES"
           "ACL2S-UNTRANSLATE"
           "FIND-EQUIV-TERM" "FIND-EQUIV-BI-TERM"
           "EVAL-IN-ACL2"
           "INCLUDE-BOOK-EVENT"
           "IS-THEOREM?" "IS-THEOREM-NAMEP" "IS-TYPE-PREDICATE"
           "GET-FREE-VARS" "GET-INDUCTION-OBLIGATIONS"
           "IS-ACL2-MACRO" "IS-RULE-NAME-DESIGNATOR" "IS-FUNCTION" "IS-VAR" "IS-ACL2S-TERM" "IS-ACL2S-TERM-CAPTURE-ERROR"
           "GET-ALIASED-DEFDATA-RECOGNIZER"
           #:implies #:^ #:=> #:v #:! #:-> #:<-))

(defpackage :structs (:use :cl :util)
  (:export "TAGGEDSEXPR" "TAGGEDSEXPR-P" "MAKE-TAGGEDSEXPR" "TAGGEDSEXPR-ID" "TAGGEDSEXPR-EXPR"
           "PROOFSTEP" "PROOFSTEP-P" "MAKE-PROOFSTEP" "PROOFSTEP-REL" "PROOFSTEP-BEFORE" "PROOFSTEP-AFTER" "PROOFSTEP-HINTS" "PROOFSTEP-ID"
           "CTXITEM" "CTXITEM-P" "MAKE-CTXITEM" "CTXITEM-ID" "CTXITEM-NAME" "CTXITEM-STMT" "CTXITEM-HINTS" "CTXITEM-BOUNDS" "CTXITEM-TYPE-PREDICATEP"
           "PROOFSTRATEGY" "PROOFSTRATEGY-P" "MAKE-PROOFSTRATEGY" "PROOFSTRATEGY-ID" "PROOFSTRATEGY-KIND" "PROOFSTRATEGY-PARAMS"
           "PROOF" "PROOF-P" "MAKE-PROOF" "PROOF-ID" "PROOF-KIND" "PROOF-NAME" "PROOF-STMT"
                   "PROOF-EXPORTATION" "PROOF-CONTRACT-COMPLETION" "PROOF-GOAL"
                   "PROOF-STEPS" "PROOF-CTX" "PROOF-DERIVED-CTX" "PROOF-STRATEGY" "PROOF-CASES"
           "PROOFMESSAGE" "PROOFMESSAGE-P" "MAKE-PROOFMESSAGE" "PROOFMESSAGE-ID" "PROOFMESSAGE-SEVERITY" "PROOFMESSAGE-DESCRIPTION"
                   "PROOFMESSAGE-PROOF" "PROOFMESSAGE-KIND" "PROOFMESSAGE-CATEGORY"
                   "OPTIONAL-TAGGEDSEXPR" "OPTIONAL-PROOF"
                   "STATUS"
                   "MAKE-COMPLETEDPROOFDATUM" "COMPLETEDPROOFDATUM-STATUS" "COMPLETEDPROOFDATUM-PROOF" "COMPLETEDPROOFDATUM-GEN-THM"
                   "COMPLETEDPROOFDATA"
                   ))

(defpackage :prover (:use :cl :util :structs :acl2s-high-level-interface :defcond)
  (:import-from :defcond :make-defcond-condition-metadata)
  (:import-from :trivia :match :<>)
  (:import-from :cl-ansi-text :green :yellow :red)
  (:export "CHECK-FILE-PROOFS"))

(defpackage :proof)
