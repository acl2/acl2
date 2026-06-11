; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(include-book "../../syntax/unambiguity")
(include-book "../../syntax/printer")
(include-book "print-to-str")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ context-msg-utilities
  :parents (utilities)
  :short "Utilities for generating context messages about AST nodes."
  :long
  (xdoc::topstring-p
    "These utilities generate context messages about AST nodes,
     for use in error reporting.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (defrule str-fix-of-str-fix
         (equal (acl2::str-fix (acl2::str-fix x))
                (acl2::str-fix x))
         :enable acl2::str-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-expr
  ((expr exprp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an expression."
  :long
  (xdoc::topstring-p
    "Returns a message of the form
     ``[prefix] [expression kind]: [printed expression]'',
     for use in error messages.")
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (expr-case
                   expr
                   :ident     "identifier"
                   :const     "constant"
                   :string    "string"
                   :paren     "parenthesized expression"
                   :gensel    "generic selection"
                   :arrsub    "array subscript expression"
                   :funcall   "function call"
                   :member    "direct member access expression"
                   :memberp   "indirect member access expression"
                   :complit   "compound literal"
                   :unary     "unary operator expression"
                   :sizeof    "sizeof expression"
                   :alignof   "alignof expression"
                   :cast      "cast"
                   :binary    "binary operator expression"
                   :cond      "ternary expression"
                   :comma     "comma expression"
                   :stmt      "statement expression"
                   :offsetof  "offsetof expression"
                   :otherwise "expression"))
       ((unless (and (expr-unambp expr)
                    (expr-aidentp expr dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (expr-fix expr)))
       (expr-str (print-expr-to-str expr dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str expr-str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-stmt
  ((stmt stmtp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a statement."
  (b* ((prefix (acl2::str-fix prefix))
       (stmt (stmt-fix stmt))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (stmt-case
                   stmt
                   :labeled       "labeled statement"
                   :compound      "compound statement"
                   :expr          "expression statement"
                   :null-attrib   "null statement"
                   :if            "if statement"
                   :ifelse        "if-else statement"
                   :switch        "switch statement"
                   :while         "while loop"
                   :dowhile       "do-while loop"
                   :for-expr      "for loop"
                   :for-declon    "for loop"
                   :for-ambig     "for loop"
                   :goto          "goto statement"
                   :gotoe         "goto statement"
                   :continue      "continue statement"
                   :break         "break statement"
                   :return        "return statement"
                   :return-attrib "return statement"
                   :asm           "assembly statement"))
       ((unless (and (stmt-unambp stmt)
                    (stmt-aidentp stmt dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str stmt))
       (stmt-str (print-stmt-to-str stmt dialect :options options :indent t)))
    (msg$ "~s0 ~s1:~%~s2" prefix case-str stmt-str))
  :verbosep t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-declon
  ((declon declonp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a declaration."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (declon-case
                   declon
                   :declon     "declaration"
                   :statassert "static assertion"))
       ((unless (and (declon-unambp declon)
                    (declon-aidentp declon dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (declon-fix declon)))
       (declon-str (print-declon-to-str declon dialect :options options :indent t)))
    (msg$ "~s0 ~s1:~%~s2" prefix case-str declon-str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-fundef
  ((fundef fundefp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a function definition."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (fundef-unambp fundef)
                    (fundef-aidentp fundef dialect)))
        (msg$ "~s1 function definition:~%~_0~x2" indent-size prefix (fundef-fix fundef)))
       (fundef-str (print-fundef-to-str fundef dialect :options options :indent t)))
    (msg$ "~s1 function definition:~%~_0~s2" indent-size prefix fundef-str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-const-expr
  ((cexpr const-exprp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a constant expression."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (const-expr-unambp cexpr)
                    (const-expr-aidentp cexpr dialect)))
        (msg$ "~s1 constant expression:~%~_0~x2"
              indent-size prefix (c$::const-expr-fix cexpr)))
       (str (print-const-expr-to-str cexpr dialect :options options)))
    (msg$ "~s1 constant expression:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-genassoc
  ((genassoc genassocp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a generic association."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (genassoc-case
                   genassoc
                   :type    "generic association with type"
                   :default "default generic association"))
       ((unless (and (genassoc-unambp genassoc)
                    (genassoc-aidentp genassoc dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (genassoc-fix genassoc)))
       (str (print-genassoc-to-str genassoc dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-member-designor
  ((memdes member-designorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a member designator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (member-designor-case
                   memdes
                   :ident "member designator"
                   :dot   "member access designator"
                   :sub   "subscript designator"))
       ((unless (and (member-designor-unambp memdes)
                    (member-designor-aidentp memdes dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3"
              indent-size prefix case-str (member-designor-fix memdes)))
       (str (print-member-designor-to-str memdes dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-type-spec
  ((tyspec type-specp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a type specifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (type-spec-unambp tyspec)
                    (type-spec-aidentp tyspec dialect)))
        (msg$ "~s1 type specifier:~%~_0~x2" indent-size prefix (type-spec-fix tyspec)))
       (str (print-type-spec-to-str tyspec dialect :options options)))
    (msg$ "~s1 type specifier:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-spec/qual
  ((specqual spec/qual-p)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a specifier or qualifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (spec/qual-case
                   specqual
                   :typespec "type specifier"
                   :typequal "type qualifier"
                   :align    "alignment specifier"
                   :attrib   "attribute specifier"))
       ((unless (and (spec/qual-unambp specqual)
                    (spec/qual-aidentp specqual dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (spec/qual-fix specqual)))
       (str (print-spec/qual-to-str specqual dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-align-spec
  ((alignspec align-specp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an alignment specifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (align-spec-case
                   alignspec
                   :alignas-type  "type alignment specifier"
                   :alignas-expr  "expression alignment specifier"
                   :alignas-ambig "alignment specifier"))
       ((unless (and (align-spec-unambp alignspec)
                    (align-spec-aidentp alignspec dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (align-spec-fix alignspec)))
       (str (print-align-spec-to-str alignspec dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-decl-spec
  ((declspec decl-specp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a declaration specifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (decl-spec-case
                   declspec
                   :stoclass "storage class specifier"
                   :typespec "type specifier"
                   :typequal "type qualifier"
                   :function "function specifier"
                   :align    "alignment specifier"
                   :attrib   "attribute specifier"
                   :stdcall  "stdcall specifier"
                   :declspec "declspec attribute"))
       ((unless (and (decl-spec-unambp declspec)
                    (decl-spec-aidentp declspec dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (decl-spec-fix declspec)))
       (str (print-decl-spec-to-str declspec dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-typequal/attribspec
  ((tyqualattrib c$::typequal/attribspec-p)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a type qualifier or attribute specifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (c$::typequal/attribspec-aidentp tyqualattrib dialect))
        (msg$ "~s1 type qualifier or attribute specifier:~%~_0~x2"
              indent-size prefix (c$::typequal/attribspec-fix tyqualattrib)))
       (str (print-typequal/attribspec-to-str tyqualattrib dialect :options options)))
    (msg$ "~s1 type qualifier or attribute specifier:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-initer
  ((initer initerp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an initializer."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (initer-case
                   initer
                   :single "single initializer"
                   :list   "list initializer"))
       ((unless (and (initer-unambp initer)
                    (initer-aidentp initer dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (initer-fix initer)))
       (str (print-initer-to-str initer dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-desiniter
  ((desiniter desiniterp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an initializer with optional designations."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (desiniter-unambp desiniter)
                    (desiniter-aidentp desiniter dialect)))
        (msg$ "~s1 initializer with optional designations:~%~_0~x2"
              indent-size prefix (desiniter-fix desiniter)))
       (str (print-desiniter-to-str desiniter dialect :options options)))
    (msg$ "~s1 initializer with optional designations:~%~_0~s2"
          indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-designor
  ((designor designorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a designator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (designor-case
                   designor
                   :sub "subscript designator"
                   :dot "member designator"))
       ((unless (and (designor-unambp designor)
                    (designor-aidentp designor dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (designor-fix designor)))
       (str (print-designor-to-str designor dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-declor
  ((declor declorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a declarator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (declor-unambp declor)
                    (declor-aidentp declor dialect)))
        (msg$ "~s1 declarator:~%~_0~x2" indent-size prefix (declor-fix declor)))
       (str (print-declor-to-str declor dialect :options options)))
    (msg$ "~s1 declarator:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-dirdeclor
  ((dirdeclor dirdeclorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a direct declarator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (dirdeclor-case
                   dirdeclor
                   :ident           "identifier declarator"
                   :paren           "parenthesized declarator"
                   :array           "array declarator"
                   :array-static1   "array declarator with static"
                   :array-static2   "array declarator with static"
                   :array-star      "variable-length array declarator"
                   :function-params "function declarator"
                   :function-names  "function declarator"))
       ((unless (and (dirdeclor-unambp dirdeclor)
                    (dirdeclor-aidentp dirdeclor dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (dirdeclor-fix dirdeclor)))
       (str (print-dirdeclor-to-str dirdeclor dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-absdeclor
  ((absdeclor absdeclorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an abstract declarator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (absdeclor-unambp absdeclor)
                    (absdeclor-aidentp absdeclor dialect)))
        (msg$ "~s1 abstract declarator:~%~_0~x2"
              indent-size prefix (absdeclor-fix absdeclor)))
       (str (print-absdeclor-to-str absdeclor dialect :options options)))
    (msg$ "~s1 abstract declarator:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-dirabsdeclor
  ((dirabsdeclor dirabsdeclorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a direct abstract declarator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (dirabsdeclor-case
                   dirabsdeclor
                   :dummy-base    "abstract declarator"
                   :paren         "parenthesized abstract declarator"
                   :array         "abstract array declarator"
                   :array-static1 "abstract array declarator with static"
                   :array-static2 "abstract array declarator with static"
                   :array-star    "abstract array declarator with star"
                   :function      "abstract function declarator"))
       ((unless (and (dirabsdeclor-unambp dirabsdeclor)
                    (dirabsdeclor-aidentp dirabsdeclor dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3"
              indent-size prefix case-str (dirabsdeclor-fix dirabsdeclor)))
       (str (print-dirabsdeclor-to-str dirabsdeclor dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-param-declon
  ((param param-declonp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a parameter declaration."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (param-declon-unambp param)
                    (param-declon-aidentp param dialect)))
        (msg$ "~s1 parameter declaration:~%~_0~x2"
              indent-size prefix (param-declon-fix param)))
       (str (print-param-declon-to-str param dialect :options options)))
    (msg$ "~s1 parameter declaration:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-param-declor
  ((paramdeclor param-declorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a parameter declarator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (param-declor-case
                   paramdeclor
                   :nonabstract "parameter declarator"
                   :abstract    "abstract parameter declarator"
                   :none        "empty parameter declarator"
                   :ambig       "ambiguous parameter declarator"))
       ((unless (and (param-declor-unambp paramdeclor)
                    (param-declor-aidentp paramdeclor dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3"
              indent-size prefix case-str (param-declor-fix paramdeclor)))
       (str (print-param-declor-to-str paramdeclor dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-tyname
  ((tyname tynamep)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a type name."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (tyname-unambp tyname)
                    (tyname-aidentp tyname dialect)))
        (msg$ "~s1 type name:~%~_0~x2" indent-size prefix (tyname-fix tyname)))
       (str (print-tyname-to-str tyname dialect :options options)))
    (msg$ "~s1 type name:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-struni-spec
  ((struni-spec struni-specp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a struct or union specifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (struni-spec-unambp struni-spec)
                    (struni-spec-aidentp struni-spec dialect)))
        (msg$ "~s1 struct or union specifier:~%~_0~x2"
              indent-size prefix (struni-spec-fix struni-spec)))
       (str (print-struni-spec-to-str struni-spec dialect :options options :indent t)))
    (msg$ "~s1 struct or union specifier:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-struct-declon
  ((structdeclon struct-declonp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a struct declaration."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (struct-declon-case
                   structdeclon
                   :member     "struct member declaration"
                   :statassert "static assertion"
                   :empty      "empty struct declaration"))
       ((unless (and (struct-declon-unambp structdeclon)
                    (struct-declon-aidentp structdeclon dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3"
              indent-size prefix case-str (struct-declon-fix structdeclon)))
       (str (print-struct-declon-to-str structdeclon dialect :options options :indent t)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-struct-declor
  ((structdeclor struct-declorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a struct declarator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (struct-declor-unambp structdeclor)
                    (struct-declor-aidentp structdeclor dialect)))
        (msg$ "~s1 struct declarator:~%~_0~x2"
              indent-size prefix (struct-declor-fix structdeclor)))
       (str (print-struct-declor-to-str structdeclor dialect :options options)))
    (msg$ "~s1 struct declarator:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-enum-spec
  ((enumspec enum-specp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an enumeration specifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (enum-spec-unambp enumspec)
                    (enum-spec-aidentp enumspec dialect)))
        (msg$ "~s1 enumeration specifier:~%~_0~x2"
              indent-size prefix (enum-spec-fix enumspec)))
       (str (print-enum-spec-to-str enumspec dialect :options options)))
    (msg$ "~s1 enumeration specifier:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-enumer
  ((enumer enumerp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an enumerator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (enumer-unambp enumer)
                    (enumer-aidentp enumer dialect)))
        (msg$ "~s1 enumerator:~%~_0~x2" indent-size prefix (enumer-fix enumer)))
       (str (print-enumer-to-str enumer dialect :options options)))
    (msg$ "~s1 enumerator:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-statassert
  ((statassert statassertp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a static assertion."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (statassert-unambp statassert)
                    (statassert-aidentp statassert dialect)))
        (msg$ "~s1 static assertion:~%~_0~x2"
              indent-size prefix (statassert-fix statassert)))
       (str (print-statassert-to-str statassert dialect :options options)))
    (msg$ "~s1 static assertion:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-attrib
  ((attr c$::attribp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a GCC attribute."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (c$::attrib-aidentp attr dialect))
        (msg$ "~s1 attribute:~%~_0~x2" indent-size prefix (c$::attrib-fix attr)))
       (str (print-attrib-to-str attr dialect :options options)))
    (msg$ "~s1 attribute:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-attrib-spec
  ((attrspec c$::attrib-specp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a GCC attribute specifier."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (c$::attrib-spec-aidentp attrspec dialect))
        (msg$ "~s1 attribute specifier:~%~_0~x2"
              indent-size prefix (c$::attrib-spec-fix attrspec)))
       (str (print-attrib-spec-to-str attrspec dialect :options options)))
    (msg$ "~s1 attribute specifier:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-init-declor
  ((initdeclor init-declorp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an initializer declarator."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (init-declor-unambp initdeclor)
                    (init-declor-aidentp initdeclor dialect)))
        (msg$ "~s1 initializer declarator:~%~_0~x2"
              indent-size prefix (init-declor-fix initdeclor)))
       (str (print-init-declor-to-str initdeclor dialect :options options)))
    (msg$ "~s1 initializer declarator:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-label
  ((label labelp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a label."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (label-case
                   label
                   :name    "named label"
                   :casexpr "case label"
                   :default "default label"))
       ((unless (and (label-unambp label)
                    (label-aidentp label dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (label-fix label)))
       (str (print-label-to-str label dialect :options options)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-asm-output
  ((output c$::asm-outputp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an assembler output operand."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (c$::asm-output-aidentp output dialect))
        (msg$ "~s1 assembler output operand:~%~_0~x2"
              indent-size prefix (c$::asm-output-fix output)))
       (str (print-asm-output-to-str output dialect :options options)))
    (msg$ "~s1 assembler output operand:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-asm-input
  ((input c$::asm-inputp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an assembler input operand."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (c$::asm-input-aidentp input dialect))
        (msg$ "~s1 assembler input operand:~%~_0~x2"
              indent-size prefix (c$::asm-input-fix input)))
       (str (print-asm-input-to-str input dialect :options options)))
    (msg$ "~s1 assembler input operand:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-asm-stmt
  ((asm c$::asm-stmtp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for an assembly statement."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (c$::asm-stmt-aidentp asm dialect))
        (msg$ "~s1 assembly statement:~%~_0~x2"
              indent-size prefix (c$::asm-stmt-fix asm)))
       (str (print-asm-stmt-to-str asm dialect :options options :indent t)))
    (msg$ "~s1 assembly statement:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-comp-stmt
  ((cstmt comp-stmtp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a compound statement."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       ((unless (and (comp-stmt-unambp cstmt)
                    (comp-stmt-aidentp cstmt dialect)))
        (msg$ "~s1 compound statement:~%~_0~x2"
              indent-size prefix (c$::comp-stmt-fix cstmt)))
       (str (print-comp-stmt-to-str cstmt dialect :options options :indent t)))
    (msg$ "~s1 compound statement:~%~_0~s2" indent-size prefix str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-msg-block-item
  ((item block-itemp)
   (dialect c::dialectp)
   &key
   ((prefix stringp) '"This occurred in")
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :returns (msg msgp)
  :hooks nil
  :short "Generate a context message for a block item."
  (b* ((prefix (acl2::str-fix prefix))
       (options (or options (c$::default-priopt)))
       (indent-size (c$::priopt->indent-size options))
       (case-str (block-item-case
                   item
                   :declon "declaration"
                   :stmt   "statement"
                   :ambig  "ambiguous block item"))
       ((unless (and (block-item-unambp item)
                    (block-item-aidentp item dialect)))
        (msg$ "~s1 ~s2:~%~_0~x3" indent-size prefix case-str (block-item-fix item)))
       (str (print-block-item-to-str item dialect :options options :indent t)))
    (msg$ "~s1 ~s2:~%~_0~s3" indent-size prefix case-str str)))
