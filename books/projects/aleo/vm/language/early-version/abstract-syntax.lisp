; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM-EARLY")

(include-book "../../../leo/early-version/definition/addresses")
(include-book "../../../leo/early-version/definition/bit-sizes")
(include-book "../../../leo/early-version/definition/characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (early-version)
  :short "Abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define an abstract syntax,
     based on the ABNF grammar."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod identifier
  :short "Fixtype of identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use ACL2 strings, which suffice to represent identifiers,
     and in fact can represent also more than that.
     This is is not an issue for the abstract syntax
     (it is only an issue for the concrete syntax),
     and provides some potential flexibility,
     e.g. for transforming code."))
  ((name string))
  :tag :identifier
  :pred identifierp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist identifier-list
  :short "Fixtype of lists of identifiers."
  :elt-type identifier
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod programid
  :short "Fixtype of program IDs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A progra ID consists of a name and a network, both identifiers.
     Requirements on the network are expressed elsewhere,
     not in the abstract syntax."))
  ((name identifier)
   (network identifier))
  :tag :programid
  :pred programidp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod locator
  :short "Fixtype of locators."
  :long
  (xdoc::topstring
   (xdoc::p
    "A locator consists of a program ID and an identifier.
     The latter denotes an item in the program denoted by the program ID."))
  ((program programid)
   (name identifier))
  :tag :locator
  :pred locatorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod register
  :short "Fixtype of registers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A register @('rN') is described by a natural number @('N')."))
  ((number nat))
  :tag :register
  :pred registerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod regaccess
  :short "Fixtype of register accesses."
  :long
  (xdoc::topstring
   (xdoc::p
    "A register access consists of a register
     and zero or more identifiers that denote nested components."))
  ((base register)
   (comps identifier-list))
  :tag :regaccess
  :pred regaccessp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum literal
  :short "Fixtype of literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "For arithmetic literals,
     we only capture the numeric value (an integer) and the type
     (which for signed and unsigned literals is captured by the size);
     we do not capture any leading zeros, any underscores,
     and whether 0 is written as @('-0').")
   (xdoc::p
    "For string literals, we do not capture the escapes,
     but only the actual sequence of characters that forms the string.")
   (xdoc::p
    "These abstractions are adequate to the abstract syntax.
     The information omitted is only relevant to the concrete syntax."))
  (:boolean ((value bool)))
  (:unsigned ((value int)
              (size leo-early::bitsize)))
  (:signed ((value int)
            (size leo-early::bitsize)))
  (:field ((value int)))
  (:group ((value int)))
  (:scalar ((value int)))
  (:address ((value leo-early::address)))
  (:string ((value leo-early::char-list)))
  :pred literalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum operand
  :short "Fixtype of operands."
  :long
  (xdoc::topstring
   (xdoc::p
    "An operand is a literal,
     a register access,
     a program ID,
     or @('self.caller')."))
  (:literal ((get literal)))
  (:register ((get regaccess)))
  (:program ((get programid)))
  (:selfcaller ())
  :pred operandp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist operand-list
  :short "Fixtype of lists of operands."
  :elt-type operand
  :true-listp t
  :elementp-of-nil nil
  :pred operand-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum literal-type
  :short "Fixtype of plaintext types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the possible types of literals."))
  (:boolean ())
  (:unsigned ((size leo-early::bitsize)))
  (:signed ((size leo-early::bitsize)))
  (:field ())
  (:group ())
  (:scalar ())
  (:address ())
  (:string ())
  :pred literal-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum plaintext-type
  :short "Fixtype of plaintext types."
  :long
  (xdoc::topstring
   (xdoc::p
    "A plaintext type is a literal type or an interface type.
     The latter is designated by name (an identifier)."))
  (:literal ((get literal-type)))
  (:interface ((name identifier)))
  :pred plaintext-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum visibility
  :short "Fixtype of visibilities."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used to qualify certain types."))
  (:public ())
  (:private ())
  (:constant ())
  :pred visibilityp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum value-type
  :short "Fixtype of value types."
  :long
  (xdoc::topstring
   (xdoc::p
    "A value type is either a plaintext type with a visibility,
     or a reference to a record or an external record."))
  (:plaintext ((type plaintext-type)
               (vis visibility)))
  (:record ((name identifier)))
  (:extrecord ((loc locator)))
  :pred value-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum finalize-type
  :short "Fixtype of finalization types."
  :long
  (xdoc::topstring
   (xdoc::p
    "A finalization type is either a plaintext type (implicitly public),
     or a reference to a record or an external record.
     In effect, finalization types are a subset of value types
     that excludes private and constant plaintext types."))
  (:plaintext ((type plaintext-type)))
  (:record ((name identifier)))
  (:extrecord ((loc locator)))
  :pred finalize-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod entry-type
  :short "Fixtype of entry types."
  :long
  (xdoc::topstring
   (xdoc::p
    "An entry type is a plaintext type with a visibility.
     It is a possible type of a record component,
     which cannot be another record.")
   (xdoc::p
    "In effect, entry types are a subset of value types
     that excludes record types."))
  ((type plaintext-type)
   (vis visibility))
  :tag :entry-type
  :pred entry-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum register-type
  :short "Fixtype of register types."
  :long
  (xdoc::topstring
   (xdoc::p
    "A register type is either a plaintext type (without visibility)
     or a reference to a record or an external record."))
  (:plaintext ((type plaintext-type)))
  (:record ((name identifier)))
  (:extrecord ((loc locator)))
  :pred register-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod import
  :short "Fixtype of imports."
  :long
  (xdoc::topstring
   (xdoc::p
    "An import consists of a program ID."))
  ((program programid))
  :tag :import
  :pred importp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist import-list
  :short "Fixtype of lists of imports."
  :elt-type import
  :true-listp t
  :elementp-of-nil nil
  :pred import-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod mapping
  :short "Fixtype of mappings."
  :long
  (xdoc::topstring
   (xdoc::p
    "A mapping consists of the name of the mapping (an identifier),
     the name of the keys (an identifier),
     the (finalization) type of the keys,
     the name of the values (an identifier),
     and the (finalization) type of the values."))
  ((name identifier)
   (key-name identifier)
   (key-type finalize-type)
   (value-name identifier)
   (value-type finalize-type))
  :tag :mapping
  :pred mappingp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ident+ptype
  :short "Fixtype of pairs consisting of an identifier and a plaintext type."
  :long
  (xdoc::topstring
   (xdoc::p
    "These pairs are used to describe components of interface types.")
   (xdoc::p
    "These are called tuples in the grammar,
     but that name is probably too generic."))
  ((name identifier)
   (type plaintext-type))
  :tag :ident+ptype
  :pred ident+ptype-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ident+ptype-list
  :short "Fixtype of lists of
          pairs consisting of a identifier and a plaintext type."
  :elt-type ident+ptype
  :true-listp t
  :elementp-of-nil nil
  :pred ident+ptype-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod interface-type
  :short "Fixtype of interface types."
  :long
  (xdoc::topstring
   (xdoc::p
    "An interface type consists of a name (identifier)
     and a list of components,
     each consisting of a name and a plaintext type."))
  ((name identifier)
   (comps ident+ptype-list))
  :tag :interface-type
  :pred interface-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ident+etype
  :short "Fixtype of pairs consisting of an identifier and an entry type."
  :long
  (xdoc::topstring
   (xdoc::p
    "These pairs are used to describe components of record types."))
  ((name identifier)
   (type entry-type))
  :tag :ident+etype
  :pred ident+etype-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ident+etype-list
  :short "Fixtype of lists of
          pairs consisting of a identifier and an entry type."
  :elt-type ident+etype
  :true-listp t
  :elementp-of-nil nil
  :pred ident+etype-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod record-type
  :short "Fixtype of record types."
  :long
  (xdoc::topstring
   (xdoc::p
    "A record type consists of a name (identifier)
     and a list of components,
     each consisting of a name and an entry type.")
   (xdoc::p
    "Although the grammar captures the presence of
     the first two required components,
     we do not do that in the abstract syntax here.
     We plan to capture it via an invariant."))
  ((name identifier)
   (comps ident+etype-list))
  :tag :record-type
  :pred record-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum unary-op
  :short "Fixtype of unary operators."
  (:abs ())
  (:abs.w ())
  (:double ())
  (:inv ())
  (:neg ())
  (:not ())
  (:square ())
  (:sqrt ())
  :pred unary-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum binary-op
  :short "Fixtype of binary operators."
  (:add ())
  (:add.w ())
  (:sub ())
  (:sub.w ())
  (:mul ())
  (:mul.w ())
  (:div ())
  (:div.w ())
  (:rem ())
  (:rem.w ())
  (:mod ())
  (:pow ())
  (:pow.w ())
  (:shl ())
  (:shl.w ())
  (:shr ())
  (:shr.w ())
  (:and ())
  (:or ())
  (:xor ())
  (:nand ())
  (:nor ())
  (:gt ())
  (:gte ())
  (:lt ())
  (:lte ())
  :pred binary-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ternary-op
  :short "Fixtype of ternary operators."
  (:ternary ())
  :pred ternary-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum equal-op
  :short "Fixtype of equality operators."
  (:is.eq ())
  (:is.neq ())
  :pred equal-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum assert-op
  :short "Fixtype of assertion operators."
  (:assert.eq ())
  (:assert.neq ())
  :pred assert-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum commit-op
  :short "Fixtype of commitment operators."
  (:commit.bhp256 ())
  (:commit.bhp512 ())
  (:commit.bhp768 ())
  (:commit.bhp1024 ())
  (:commit.ped64 ())
  (:commit.ped128 ())
  :pred commit-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum hash-op
  :short "Fixtype of hashing operators."
  (:hash.bhp256 ())
  (:hash.bhp512 ())
  (:hash.bhp768 ())
  (:hash.bhp1024 ())
  (:hash.ped64 ())
  (:hash.ped128 ())
  (:hash.psd2 ())
  (:hash.psd4 ())
  (:hash.psd8 ())
  :pred hash-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum reference
  :short "Fixtype of references."
  :long
  (xdoc::topstring
   (xdoc::p
    "This notion of reference is currently not in the grammar,
     but perhaps it should be.
     It is either an identiier or a locator,
     which references either an item in the same program
     or an item in an external program."))
  (:internal ((get identifier)))
  (:external ((get locator)))
  :pred referencep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum instruction
  :short "Fixtype of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Instructions consists of
     unary operations,
     binary operations,
     ternary operations,
     equality operations,
     assertion operations,
     commitment operations,
     hashing operations,
     casts, and
     calls (of closures)."))
  (:unary ((op unary-op)
           (arg operand)
           (into register)))
  (:binary ((op binary-op)
            (arg1 operand)
            (arg2 operand)
            (into register)))
  (:ternary ((op ternary-op)
             (arg1 operand)
             (arg2 operand)
             (arg3 operand)
             (into register)))
  (:equal ((op equal-op)
           (arg1 operand)
           (arg2 operand)
           (into register)))
  (:assert ((op assert-op)
            (arg1 operand)
            (arg2 operand)))
  (:commit ((op commit-op)
            (arg1 operand)
            (arg2 operand)
            (into register)))
  (:hash ((op hash-op)
          (arg operand)
          (into register)))
  (:cast ((args operand-list)
          (into register)
          (as register-type)))
  (:call ((ref reference)
          (args operand-list)
          (into register)))
  :pred instructionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist instruction-list
  :short "Fixtype of lists of instructions."
  :elt-type instruction
  :true-listp t
  :elementp-of-nil nil
  :pred instruction-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum command
  :short "Fixtype of commands."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are currently three kinds of commands:
     increments, decrements, and instructions.
     Note that, as in the grammar,
     finalization commands are separate."))
  (:increment ((map identifier)
               (key operand)
               (value operand)))
  (:decrement ((map identifier)
               (key operand)
               (value operand)))
  (:instruction ((get instruction)))
  :pred commandp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist command-list
  :short "Fixtype of lists of commands."
  :elt-type command
  :true-listp t
  :elementp-of-nil nil
  :pred command-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod finalize-command
  :short "Fixtype of finalization commands."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the one that may optionally occur
     at the very end of a function body,
     just before the finalizer."))
  ((args operand-list))
  :tag :finalize-command
  :pred finalize-commandp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod closure-input
  :short "Fixtype of closure inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declared input of a closure consists of
     a register and a register type."))
  ((reg register)
   (type register-type))
  :tag :closure-input
  :pred closure-inputp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist closure-input-list
  :short "Fixtype of lists of closure inputs."
  :elt-type closure-input
  :true-listp t
  :elementp-of-nil nil
  :pred closure-input-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod closure-output
  :short "Fixtype of closure outputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declared output of a closure consists of
     a register access and a register type."))
  ((reg regaccess)
   (type register-type))
  :tag :closure-output
  :pred closure-outputp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist closure-output-list
  :short "Fixtype of lists of closure outputs."
  :elt-type closure-output
  :true-listp t
  :elementp-of-nil nil
  :pred closure-output-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod closure
  :short "Fixtype of closures."
  :long
  (xdoc::topstring
   (xdoc::p
    "A closure consists of a name (identifier),
     inputs, instructions, and outputs.
     Here we do not capture the requirement that
     there is at least an instruction."))
  ((name identifier)
   (inputs closure-input-list)
   (instrs instruction-list)
   (outputs closure-output-list))
  :tag :closure
  :pred closurep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-input
  :short "Fixtype of function inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declared input of a function consists of
     a register and a value type."))
  ((reg register)
   (type value-type))
  :tag :function-input
  :pred function-inputp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist function-input-list
  :short "Fixtype of lists of function inputs."
  :elt-type function-input
  :true-listp t
  :elementp-of-nil nil
  :pred function-input-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-output
  :short "Fixtype of function outputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declared output of a function consists of
     a register access and a value type."))
  ((reg regaccess)
   (type value-type))
  :tag :function-output
  :pred function-outputp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist function-output-list
  :short "Fixtype of lists of function outputs."
  :elt-type function-output
  :true-listp t
  :elementp-of-nil nil
  :pred function-output-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod finalize-input
  :short "Fixtype of finalizer inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declared input of a finalizer consists of
     a register and a finalize type."))
  ((reg register)
   (type finalize-type))
  :tag :finalize-input
  :pred finalize-inputp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist finalize-input-list
  :short "Fixtype of lists of finalizer inputs."
  :elt-type finalize-input
  :true-listp t
  :elementp-of-nil nil
  :pred finalize-input-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod finalize-output
  :short "Fixtype of finalizer outputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declared output of a finalizer consists of
     a register access and a value type."))
  ((reg regaccess)
   (type value-type))
  :tag :finalizer-output
  :pred finalizer-outputp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist finalize-output-list
  :short "Fixtype of lists of finalizer outputs."
  :elt-type finalize-output
  :true-listp t
  :elementp-of-nil nil
  :pred finalize-output-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod finalizer
  :short "Fixtype of finalizers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A finalizer consists of a name (identifier),
     inputs, commands, and outputs."))
  ((name identifier)
   (inputs finalize-input-list)
   (comms command-list)
   (outputs finalize-output-list))
  :tag :finalizer
  :pred finalizerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod finalization
  :short "Fixtype of finalizations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This notion is not explicitly named in the grammar,
     but it is the optional thing that may conclude a function.
     It consists of a finalization command and a finalizer."))
  ((command finalize-command)
   (finalizer finalizer))
  :tag :finalization
  :pred finalizationp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption finalization-option
  finalization
  :short "Fixtype of optional finalizations."
  :pred finalization-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function
  :short "Fixtype of functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function consists of a name (identifier),
     inputs, instructions, outputs,
     and an optional finalization.
     Here we do not capture the requirement that
     there is at least an instruction."))
  ((name identifier)
   (inputs function-input-list)
   (instrs instruction-list)
   (outputs function-output-list)
   (finalize finalization))
  :tag :function
  :pred functionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum programdef
  :short "Fixtype of program definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the kinds of items defined by a program."))
  (:mapping ((get mapping)))
  (:interface ((get interface-type)))
  (:record ((get record-type)))
  (:closure ((get closure)))
  (:function ((get function)))
  :pred programdefp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist programdef-list
  :short "Fixtype of lists of program definitions."
  :elt-type programdef
  :true-listp t
  :elementp-of-nil nil
  :pred programdef-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod program
  :short "Fixtype of programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A program consists of a name, imports, and definitions."))
  ((name identifier)
   (imports import-list)
   (defs programdef-list))
  :tag :program
  :pred programp)
