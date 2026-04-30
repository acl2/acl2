; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "post-parsing")
(include-book "syntax-abstraction")

(include-book "kestrel/fty/nat-list-result" :dir :system)

(acl2::controlled-configuration :no-function nil)

(local
 (in-theory (enable abnf::treep-when-result-not-error
                    acl2::nat-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-interface
  :parents (remora)
  :short "API functions for parsing Remora source from a string."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are end-to-end entry points that take an ACL2 string of Remora
     source and return an "
    (xdoc::seetopic "abstract-syntax-trees" "abstract syntax tree (AST)")
    ".  Each is named @('parse-X-from-string'), where @('X') is a Remora
     grammar rule.  Internally each function calls a helper named
     @('parse-X-from-string-to-cst') (string &rarr; CST) and then applies the
     corresponding @(see syntax-abstraction) function to lift the CST to an
     AST.")
   (xdoc::p
    "Eventually the only entry point we expect to expose is
     @('parse-program-from-string') (which we will probably call
     @('parse') &mdash; once the program-level AST and
     its abstractor are in place, all the per-rule entry points below will
     be obsolete.  Until then, each entry point covers one of the largest
     pieces the abstractor can currently handle: @('ispace') (the entire
     dim/shape/ispace cluster), @('base-val'), @('base-type'),
     @('type-var'), and @('ispace-var').")
   (xdoc::p
    "All entry points require the entire string to be consumed by the parse,
     and return a @(see reserr) on any failure (UTF-8 decode, parse, or
     abstraction).  ACL2 strings are sequences of bytes (char-codes 0-255);
     these entry points interpret those bytes as UTF-8 and decode them to
     Unicode code points before parsing, matching the behavior of "
    (xdoc::seetopic "post-parsing" "@('parse-program-from-bytes')")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Supporting definitions that should be moved.

;; Conceptually, this would be nice if this definition were somewhere like
;;   books/unicode/utf8-decode.lisp
;; or in a new file in
;;   books/kestrel/unicode-light/
;; but since it uses define and acl2::string=>nats and acl2::nat-list-resultp
;; probably it would be better to put it in a new file like
;;   books/kestrel/utilities/strings/strings-unicodes.lisp

(define decode-utf8-string ((string stringp))
  :returns (codepoints acl2::nat-list-resultp)
  :short "Decode an ACL2 string interpreted as UTF-8 to a list of
          Unicode code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 strings are sequences of bytes (char-codes 0-255).  This helper
     interprets those bytes as a UTF-8 encoded sequence and decodes them
     to the corresponding Unicode code points.  Returns a @(see reserr)
     if the byte sequence is not valid UTF-8.")
   (xdoc::p
    "This mirrors the bytes-to-code-points step in @(tsee
     parse-program-from-bytes)."))
  (b* ((bytes (acl2::string=>nats (acl2::str-fix string)))
       ((unless (acl2::unsigned-byte-listp 8 bytes))
        (reserrf (cons :invalid-octets bytes)))
       (codepoints (acl2::utf8=>ustring bytes))
       ((unless (nat-listp codepoints))
        (reserrf (cons :invalid-utf-8 bytes))))
    codepoints))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Macros that drive the entry-point definitions.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PARSE-TO-AST-AND-CHECK is an inline expansion of the full pipeline:
;; decode UTF-8, run parse-<rule-name>, check that the entire input was
;; consumed, then run abs-<rule-name>.  RULE-NAME is a symbol naming a
;; grammar rule for which both PARSE-<RULE-NAME> and ABS-<RULE-NAME> are
;; defined; SOURCE-STRING is an expression of type STRINGP.  At any
;; failure the expansion returns a RESERR.
(defmacro parse-to-ast-and-check (rule-name source-string)
  (b* ((parse-fn (acl2::packn-pos (list 'parse- rule-name) rule-name))
       (abs-fn   (acl2::packn-pos (list 'abs-   rule-name) rule-name)))
    `(b* ((codepoints (decode-utf8-string ,source-string))
          ((when (reserrp codepoints)) codepoints)
          ((mv tree rest) (,parse-fn codepoints))
          ((when (reserrp tree)) tree)
          ((unless (null rest))
           (reserrf (cons :remaining-input rest))))
       (,abs-fn tree))))

;; DEFPARSE-FROM-STRING generates two named entry points for a rule:
;;   (parse-<rule-name>-from-string-to-cst string) -> CST tree
;;   (parse-<rule-name>-from-string         string) -> AST result
;; RULE-NAME is the rule's symbol (used to find PARSE-<RULE-NAME> and
;; ABS-<RULE-NAME>); RESULT-PRED is the result predicate the AST entry
;; should advertise (e.g. ISPACE-RESULTP, KINDED-VAR-RESULTP).
(defmacro defparse-from-string (rule-name result-pred)
  (b* ((parse-fn  (acl2::packn-pos (list 'parse- rule-name) rule-name))
       (cst-fn    (acl2::packn-pos
                   (list 'parse- rule-name '-from-string-to-cst) rule-name))
       (ast-fn    (acl2::packn-pos
                   (list 'parse- rule-name '-from-string) rule-name))
       (rule-str  (acl2::string-downcase (symbol-name rule-name))))
    `(progn
       (define ,cst-fn ((string stringp))
         :returns (tree abnf::tree-resultp)
         :short ,(concatenate 'string
                              "Parse a @('" rule-str "') from a string to a CST.")
         (b* ((codepoints (decode-utf8-string string))
              ((when (reserrp codepoints)) codepoints)
              ((mv tree rest) (,parse-fn codepoints))
              ((when (reserrp tree)) tree)
              ((unless (null rest))
               (reserrf (cons :remaining-input rest))))
           tree))
       (define ,ast-fn ((string stringp))
         :returns (ast ,result-pred)
         :short ,(concatenate 'string
                              "Parse a @('" rule-str "') from a string to an AST.")
         (parse-to-ast-and-check ,rule-name string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Per-rule entry points (each generates two functions:
;;   parse-<rule>-from-string-to-cst  :: string -> CST
;;   parse-<rule>-from-string         :: string -> AST)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-from-string ispace      ispace-resultp)
(defparse-from-string base-val    base-value-resultp)
(defparse-from-string base-type   base-type-resultp)
(defparse-from-string type-var    type-var-resultp)
(defparse-from-string ispace-var  ispace-var-resultp)
(defparse-from-string type-exp    type-resultp)
(defparse-from-string char-lit    char-lit-resultp)
(defparse-from-string string-lit  char-lit-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic fragment dispatcher
;; (convenient for testing)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ast-from-fragment ((rule-name stringp) (source-code stringp))
  :returns (ast (or (ispace-resultp ast)
                    (base-value-resultp ast)
                    (base-type-resultp ast)
                    (type-var-resultp ast)
                    (ispace-var-resultp ast)
                    (type-resultp ast)
                    (char-lit-resultp ast)
                    (char-lit-list-resultp ast)))
  :hooks nil
  :short "Parse and abstract a Remora source fragment to an AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Dispatches on @('rule-name'), which must be one of
     @('\"ispace\"'), @('\"base-val\"'), @('\"base-type\"'),
     @('\"type-var\"'), @('\"ispace-var\"'), @('\"type-exp\"'),
     @('\"char-lit\"'), or @('\"string-lit\"').
     Other rule names produce a @(see reserr).")
   (xdoc::p
    "The result type is a disjunction over the AST result predicates of
     the supported rules.  As more rules become abstractable, both the
     dispatch and the result type grow accordingly."))
  (cond ((equal rule-name "ispace")
         (parse-to-ast-and-check ispace     source-code))
        ((equal rule-name "base-val")
         (parse-to-ast-and-check base-val   source-code))
        ((equal rule-name "base-type")
         (parse-to-ast-and-check base-type  source-code))
        ((equal rule-name "type-var")
         (parse-to-ast-and-check type-var   source-code))
        ((equal rule-name "ispace-var")
         (parse-to-ast-and-check ispace-var source-code))
        ((equal rule-name "type-exp")
         (parse-to-ast-and-check type-exp   source-code))
        ((equal rule-name "char-lit")
         (parse-to-ast-and-check char-lit   source-code))
        ((equal rule-name "string-lit")
         (parse-to-ast-and-check string-lit source-code))
        (t (reserrf (cons :unsupported-rule-name rule-name)))))


;; This file is incomplete.
;; When done, there will be top-level parsing functions for Remora
;; programs and files.
