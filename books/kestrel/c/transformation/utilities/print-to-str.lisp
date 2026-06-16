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

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(include-book "../../syntax/unambiguity")
(include-book "../../syntax/printer")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ print-to-str-utilities
  :parents (utilities)
  :short "Utilities for printing AST nodes to strings."
  :long
  (xdoc::topstring-p
    "These utilities print AST nodes to strings,
     for use in error reporting and other contexts.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defrulel unsigned-byte-listp-8-when-byte-listp
  (implies (acl2::byte-listp x)
           (acl2::unsigned-byte-listp 8 x))
  :induct t
  :enable (acl2::byte-listp acl2::bytep unsigned-byte-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pristate->str ((pstate c$::pristatep))
  :returns (str stringp)
  (acl2::nats=>string (reverse (c$::pristate->bytes-rev pstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-expr-to-str
  ((expr exprp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (expr-unambp expr)
             (expr-aidentp expr dialect))
  :returns (str stringp)
  :short "Print an expression to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-expr expr (c$::expr-priority-expr) pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-const-expr-to-str
  ((cexpr const-exprp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (const-expr-unambp cexpr)
             (const-expr-aidentp cexpr dialect))
  :returns (str stringp)
  :short "Print a constant expression to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-const-expr cexpr pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-genassoc-to-str
  ((genassoc genassocp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (genassoc-unambp genassoc)
             (genassoc-aidentp genassoc dialect))
  :returns (str stringp)
  :short "Print a generic association to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-genassoc genassoc pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-member-designor-to-str
  ((memdes member-designorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (member-designor-unambp memdes)
             (member-designor-aidentp memdes dialect))
  :returns (str stringp)
  :short "Print a member designator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-member-designor memdes pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-type-spec-to-str
  ((tyspec type-specp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (type-spec-unambp tyspec)
             (type-spec-aidentp tyspec dialect))
  :returns (str stringp)
  :short "Print a type specifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-type-spec tyspec t pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-spec/qual-to-str
  ((specqual spec/qual-p)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (spec/qual-unambp specqual)
             (spec/qual-aidentp specqual dialect))
  :returns (str stringp)
  :short "Print a specifier or qualifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-spec/qual specqual pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-align-spec-to-str
  ((alignspec align-specp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (align-spec-unambp alignspec)
             (align-spec-aidentp alignspec dialect))
  :returns (str stringp)
  :short "Print an alignment specifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-align-spec alignspec pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-decl-spec-to-str
  ((declspec decl-specp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (decl-spec-unambp declspec)
             (decl-spec-aidentp declspec dialect))
  :returns (str stringp)
  :short "Print a declaration specifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-decl-spec declspec t pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-typequal/attribspec-to-str
  ((tyqualattrib c$::typequal/attribspec-p)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (c$::typequal/attribspec-aidentp tyqualattrib dialect)
  :returns (str stringp)
  :short "Print a type qualifier or attribute specifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-typequal/attribspec tyqualattrib pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-initer-to-str
  ((initer initerp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (initer-unambp initer)
             (initer-aidentp initer dialect))
  :returns (str stringp)
  :short "Print an initializer to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-initer initer pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-desiniter-to-str
  ((desiniter desiniterp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (desiniter-unambp desiniter)
             (desiniter-aidentp desiniter dialect))
  :returns (str stringp)
  :short "Print an initializer with optional designations to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-desiniter desiniter pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-designor-to-str
  ((designor designorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (designor-unambp designor)
             (designor-aidentp designor dialect))
  :returns (str stringp)
  :short "Print a designator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-designor designor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-declor-to-str
  ((declor declorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (declor-unambp declor)
             (declor-aidentp declor dialect))
  :returns (str stringp)
  :short "Print a declarator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-declor declor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dirdeclor-to-str
  ((dirdeclor dirdeclorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (dirdeclor-unambp dirdeclor)
             (dirdeclor-aidentp dirdeclor dialect))
  :returns (str stringp)
  :short "Print a direct declarator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-dirdeclor dirdeclor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-absdeclor-to-str
  ((absdeclor absdeclorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (absdeclor-unambp absdeclor)
             (absdeclor-aidentp absdeclor dialect))
  :returns (str stringp)
  :short "Print an abstract declarator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-absdeclor absdeclor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dirabsdeclor-to-str
  ((dirabsdeclor dirabsdeclorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (dirabsdeclor-unambp dirabsdeclor)
             (dirabsdeclor-aidentp dirabsdeclor dialect))
  :returns (str stringp)
  :short "Print a direct abstract declarator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-dirabsdeclor dirabsdeclor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-param-declon-to-str
  ((param param-declonp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (param-declon-unambp param)
             (param-declon-aidentp param dialect))
  :returns (str stringp)
  :short "Print a parameter declaration to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-param-declon param pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-param-declor-to-str
  ((paramdeclor param-declorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (param-declor-unambp paramdeclor)
             (param-declor-aidentp paramdeclor dialect))
  :returns (str stringp)
  :short "Print a parameter declarator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-param-declor paramdeclor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-tyname-to-str
  ((tyname tynamep)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (tyname-unambp tyname)
             (tyname-aidentp tyname dialect))
  :returns (str stringp)
  :short "Print a type name to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-tyname tyname pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-struni-spec-to-str
  ((struni-spec struni-specp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (and (struni-spec-unambp struni-spec)
             (struni-spec-aidentp struni-spec dialect))
  :returns (str stringp)
  :short "Print a structure or union specifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-struni-spec struni-spec nil pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-struct-declon-to-str
  ((structdeclon struct-declonp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (and (struct-declon-unambp structdeclon)
             (struct-declon-aidentp structdeclon dialect))
  :returns (str stringp)
  :short "Print a structure declaration to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-struct-declon structdeclon nil pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-struct-declor-to-str
  ((structdeclor struct-declorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (struct-declor-unambp structdeclor)
             (struct-declor-aidentp structdeclor dialect))
  :returns (str stringp)
  :short "Print a structure declarator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-struct-declor structdeclor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-enum-spec-to-str
  ((enumspec enum-specp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (enum-spec-unambp enumspec)
             (enum-spec-aidentp enumspec dialect))
  :returns (str stringp)
  :short "Print an enumeration specifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-enum-spec enumspec pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-enumer-to-str
  ((enumer enumerp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (enumer-unambp enumer)
             (enumer-aidentp enumer dialect))
  :returns (str stringp)
  :short "Print an enumerator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-enumer enumer pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-statassert-to-str
  ((statassert statassertp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (statassert-unambp statassert)
             (statassert-aidentp statassert dialect))
  :returns (str stringp)
  :short "Print a static assertion declaration to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-statassert statassert pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-attrib-to-str
  ((attr c$::attribp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (c$::attrib-aidentp attr dialect)
  :returns (str stringp)
  :short "Print a GCC attribute to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-attrib attr pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-attrib-spec-to-str
  ((attrspec c$::attrib-specp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (c$::attrib-spec-aidentp attrspec dialect)
  :returns (str stringp)
  :short "Print an attribute specifier to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-attrib-spec attrspec pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-init-declor-to-str
  ((initdeclor init-declorp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (init-declor-unambp initdeclor)
             (init-declor-aidentp initdeclor dialect))
  :returns (str stringp)
  :short "Print an initializer declarator to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-init-declor initdeclor pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-declon-to-str
  ((declon declonp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (and (declon-unambp declon)
             (declon-aidentp declon dialect))
  :returns (str stringp)
  :short "Print a declaration to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-declon declon nil pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-label-to-str
  ((label labelp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (and (label-unambp label)
             (label-aidentp label dialect))
  :returns (str stringp)
  :short "Print a label to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-label label pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-output-to-str
  ((output c$::asm-outputp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (c$::asm-output-aidentp output dialect)
  :returns (str stringp)
  :short "Print an assembler output operand to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-asm-output output pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-input-to-str
  ((input c$::asm-inputp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil))
  :guard (c$::asm-input-aidentp input dialect)
  :returns (str stringp)
  :short "Print an assembler input operand to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (c$::print-asm-input input pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-stmt-to-str
  ((asm c$::asm-stmtp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (c$::asm-stmt-aidentp asm dialect)
  :returns (str stringp)
  :short "Print an assembler statement to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-asm-stmt asm pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-stmt-to-str
  ((stmt stmtp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (and (stmt-unambp stmt)
             (stmt-aidentp stmt dialect))
  :returns (str stringp)
  :short "Print a statement to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-stmt stmt pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-comp-stmt-to-str
  ((cstmt comp-stmtp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (and (comp-stmt-unambp cstmt)
             (comp-stmt-aidentp cstmt dialect))
  :returns (str stringp)
  :short "Print a compound statement to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-comp-stmt cstmt pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-block-item-to-str
  ((item block-itemp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (and (block-item-unambp item)
             (block-item-aidentp item dialect))
  :returns (str stringp)
  :short "Print a block item to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-block-item item pstate)))
    (pristate->str pstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fundef-to-str
  ((fundef fundefp)
   (dialect c::dialectp)
   &key
   ((options (or (c$::prioptp options)
                 (not options)))
    'nil)
   ((indent booleanp) 'nil))
  :guard (and (fundef-unambp fundef)
             (fundef-aidentp fundef dialect))
  :returns (str stringp)
  :short "Print a function definition to a string."
  (b* ((options (or options (c$::default-priopt)))
       (pstate (c$::init-pristate options dialect))
       (pstate (if indent (c$::inc-pristate-indent pstate) pstate))
       (pstate (c$::print-fundef fundef pstate)))
    (pristate->str pstate)))
