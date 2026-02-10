; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "implementation-environments")
(include-book "concrete-syntax")
(include-book "abstract-syntax")
(include-book "preprocessing")
(include-book "parsing")
(include-book "disambiguation")
(include-book "validation")
(include-book "printing")
(include-book "builtin")
(include-book "input-files")
(include-book "input-files-doc")
(include-book "output-files")
(include-book "output-files-doc")
(include-book "langdef-mapping")
(include-book "formalized")
(include-book "compilation-db")
(include-book "infer-ienv")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax-for-tools
  :parents (c::c)
  :short "A syntax of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide an abstract syntax of C
     for use by tools that manipulate C code,
     e.g. C code generators and C code transformers.
     This abstract syntax preserves (i.e. does not abstract away)
     much of the information in the concrete syntax,
     in order to afford more control on
     the form of the code produced by those tools.
     It could be also useful to support higher-level code browsing
     in IDE-like tools.")
   (xdoc::p
    "Currently this abstract syntax covers all of C after preprocessing,
     but it also includes some initial forms of preprocessing constructs,
     which we plan to extend.
     Preserving preprocessing constructs from the original concrete syntax
     is also important,
     since preprocessed code can be fairly distant from the original one.
     Supporting all possible forms of preprocessing constructs
     would be challenging in an abstract syntax,
     because preprocessing in C operates at the lexical level.
     Nonetheless, certain constructs are relatively simple,
     such as @('#include') directives at the top level.")
   (xdoc::p
    "This abstract syntax also includes
     some initial support for preserving comments,
     which we plan to extend.
     Supporting all forms of comments may be challenging,
     since they may appear anywhere between tokens.
     But there are cases in which they are easy to support,
     such as comments at the top level,
     or comments clearly associated with certain constructs
     (e.g. just before a function definition).")
   (xdoc::p
    "We include some constructs for GCC/Clang extensions,
     which, as mentioned in "
    (xdoc::seetopic "c::c" "the top-level topic of our library for C")
    ", are prevalent and important extensions
     needed for a practical tool.
     Ideally, eventually we should support all the GCC/Clang extensions,
     but we are adding them piece-wise, as needed.
     Our documentation always distinguishes
     between the C standard and the GCC/Clang extensions.")
   (xdoc::p
    "The idea of this tool-oriented abstract syntax is also discussed in
     @(see c::abstract-syntax) and @(see c::atc-abstract-syntax).
     We plan to have ATC use this new tool-oriented abstract syntax.")
   (xdoc::p
    "Accompanying our abstract syntax,
     we provide a concrete syntax, based on an ABNF grammar.
     This is not a different syntax for C,
     but just a different formulation of the syntax of C,
     motivated by the fact that this tool-oriented syntax
     is neither before nor after preprocessing,
     but incorporates constructs from both forms of the C code;
     the grammar in [C17] is organized differently,
     with preprocessing being a distinguished translation phase
     [C17:5.1.1.2].")
   (xdoc::p
    "We have started defining an "
    (xdoc::seetopic "abstraction-mapping" "abstraction mapping")
    " from the concrete to the abstract syntax.
     This is still very much work in progress,
     but its main purpose is for specification and verification,
     and is not needed to run the tools described below
     (parser, printer, etc.).")
   (xdoc::p
    "We provide a parser that produces this abstract syntax.
     This parser currently operates on preprocessed code,
     but we are extending it to support some preprocessing constructs.
     The syntax of C is notoriously ambiguous,
     requiring some semantic analysis to disambiguate it.
     Instead of performing this semantic analysis during parsing,
     our parser captures ambiguous constructs as such,
     and we provide a separate @(see disambiguator)
     that transforms the abstract syntax, after parsing,
     by disambiguating it via the necessary semantic analysis.")
   (xdoc::p
    "In order to handle typical C code,
     we provide an "
    (xdoc::seetopic "external-preprocessing"
                    "ACL2 tool to invoke an external C preprocessor")
    ". The tool can be run on headers and source files,
     to obtain preprocessed source files,
     which can be then parsed by our parser.")
   (xdoc::p
    "Additionally, we provide our own @(see preprocessor),
     which, unlike typical C preprocessors,
     preserves preprocessing constructs under certain conditions.
     This preprocessor is still in a preliminary stage,
     but our parser will soon be able to parse
     the code produced by our preprocessor,
     including the preprocessing constructs.
     Eventually, we plan to merge our preprocessor and parser
     into one parser that also performs preprocessing.")
   (xdoc::p
    "We provide a @(see validator) on the abstract syntax (after disambiguation)
     that checks the static constraints on C code (i.e. type checking etc.),
     which results in an elaboration of the abstract syntax,
     e.g. enhancing the abstract syntax with types and other information
     after successful validation.")
   (xdoc::p
    "We provide a (pretty-)@(see printer)
     that turns our abstract syntax
     into concrete syntax that is valid C code.
     This printer is working,
     we plan to improve it in various respects,
     in particular by supporting certain printing options
     (e.g. for the right margin position).")
   (xdoc::p
    "We provide a collection of predicates that characterize "
    (xdoc::seetopic "unambiguity" "unambiguous abstract syntax")
    ", i.e. abstract syntax without ambiguous constructs,
     as resulting after disambiguation.")
   (xdoc::p
    "We provide a collection of predicates that characterize "
    (xdoc::seetopic "validation-information" "annotated abstract syntax")
    ", i.e. abstract syntax enhanced with
     the information added by the validator.")
   (xdoc::p
    "We provide a collection of predicates that characterize "
    (xdoc::seetopic "ascii-identifiers"
                    "abstract syntax with ASCII identifiers")
    ", i.e. abstract syntax such that all the identifiers that occur in it
     are ACL2 strings that start with an ASCII letter,
     only contain ASCII letters, digits, and underscores,
     and are distinct from keywords.")
   (xdoc::p
    "We provide a collection of predicates that characterize "
    (xdoc::seetopic "standard"
                    "abstract syntax for standard C")
    ", i.e. that does not use any GCC/Clang extensions.")
   (xdoc::p
    "We provide a collection of predicates that characterize "
    (xdoc::seetopic "purity" "pure abstract syntax")
    ", i.e. without side effects.")
   (xdoc::p
    "We provide various "
    (xdoc::seetopic "abstract-syntax-operations"
                    "other operations on the abstract syntax")
    ".")
   (xdoc::p
    "We provide event macros @(tsee input-files) and @(tsee output-files)
     to read, preprocess, parse, disambiguate, print, and write files.
     We also provide programmatic interfaces to both,
     via the (non-event) macros
     @(tsee input-files-prog) and @(tsee output-files-prog).")
   (xdoc::p
    "We plan to prove theorems connecting this tool-oriented syntax
     with the formal language definition in @(see c::language).
     We already provide a "
    (xdoc::seetopic "mapping-to-language-definition" "(partial) mapping")
    " from the tool-oriented abstract syntax
     to the abstract syntax of the formal language definition,
     along with "
    (xdoc::seetopic "formalized-subset" "predicates")
    " to identify which subset of the abstract syntax
     not only maps to the language definition's abstract syntax,
     but is also covered by the formal semantics we have so far.")
   (xdoc::p
    "All the items described above form a sub-library of our ACL2 library for C,
     in the directory @('[books]/kestrel/c/syntax').
     For this sub-library, we use a different package from @('C'),
     in particular to separate otherwise possibly homonymous types and functions
     in this tool-oriented abstract syntax
     from the abstract syntax used for the language formalization
     under @('[books]/kestrel/c/language').
     We pick the name @('C$') for this sub-library,
     where the @('$') conveys the idea of `syntax'.
     This package naming pattern could be used for
     ACL2 libraries (and sub-libraries) for other programming languages."))
  :order-subtopics (implementation-environments
                    concrete-syntax
                    abstract-syntax
                    preprocessing
                    parsing
                    disambiguation
                    validation
                    printing
                    input-files
                    output-files
                    mapping-to-language-definition
                    formalized-subset))
