; ACL2 Community Books Release Notes
; Copyright (C) 2013-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
; Contributing author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "ACL2")

; Matt K. mod: Moved to cert.acl2 to support running defxdoc forms below
; without LDing this file.
; (include-book "xdoc/constructors" :dir :system)

;; These books aren't really necessary, but are harmless enough and are useful
;; when debugging the release note markup.
(include-book "centaur/nrev/portcullis" :dir :system)
(include-book "centaur/vl/portcullis" :dir :system)
(include-book "centaur/ipasir/portcullis" :dir :system)
(include-book "centaur/sv/portcullis" :dir :system)
(include-book "centaur/gl/portcullis" :dir :system)
(include-book "centaur/bed/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "build/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)
(include-book "kestrel/apt/portcullis" :dir :system)
(include-book "kestrel/soft/portcullis" :dir :system)
(include-book "kestrel/abnf/portcullis" :dir :system)
(include-book "kestrel/java/portcullis" :dir :system)
(include-book "kestrel/ethereum/portcullis" :dir :system)
(include-book "kestrel/bitcoin/portcullis" :dir :system)
(include-book "kestrel/utilities/omaps/portcullis" :dir :system)
(include-book "kestrel/yul/portcullis" :dir :system)

; Book release notes are sometimes disorganized.
; They are often cleaned up before a release.

; Starting with Version 7.3, we no longer maintain release notes
; note-x-x-books.  Instead, we hope that the ACL2 Community will track
; changes to the books by maintaining note-x-x-books as they go.

(defxdoc release-notes-books

; This is a parent for the note-x-x-books topics, so they're all visible in one
; place.

  :parents (release-notes)
  :short "Pointers to what has changed in the community books"
  :long "<p>This section of the online @(see documentation) contains notes on
 the changes in the community books between successive released versions of
 ACL2.</p>

 <p>Each topic @('note-x-y-books') is a note describing what in the community
 books distributed with ACL2 version X.Y was new in comparison to the community
 books distributed with the preceding version of ACL2.</p>

 <p>The current version of ACL2 is the value of the constant @('(@
 acl2-version)').</p>")

(defxdoc note-8-5-books

; Please add information about your library in the appropriate
; category below --- the category title is enclosed in (xdoc::h3 ...)
; (of course, feel free to add a new category if needed).  To
; ensure consistency with the style of previous book release doc
; topics, please follow the following convention:

;  (xdoc::h4 "Your Library Title")
;  (xdoc::p "Details go here.")

; Please put the h4's in alphabetical order, each preceded by 40 semicolons.
; You can also use (xdoc::h5 ...) under each h4, e.g. for sub-libraries:
; There is no need to order the h5's alphabetically,
; but please precede each h5 by 20 semicolons.
; If you are stuck, see the entries about other libraries.

  :parents (note-8-5 release-notes-books)

  :short "Release notes for the ACL2 Community Books for ACL2 8.5"

  :long

  (xdoc::topstring

   (xdoc::p
    "The following is a brief summary of
     changes made to the @(see community-books)
     between the releases of ACL2 8.4 and 8.5.")

   (xdoc::p
    "See also @(see note-8-5) for the changes made to ACL2 itself.
     For additional details,
     you may also see the raw "
    (xdoc::ahref "https://github.com/acl2/acl2/commits/master" "commit log")
    ".")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "New Libraries")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Changes to Existing Libraries")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "apt::apt" "APT Library"))

   (xdoc::p
    "The @(tsee apt::simplify) transformation now does a better job of
     preserving @(tsee mbt) calls.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "kestrel-utilities" "Kestrel Utilities Library"))

   (xdoc::p
    "Special handling of @(tsee mbt) by @(tsee directed-untranslate) has been
     removed, as it is no longer necessary or appropriate because of the change
     to the @(tsee apt::simplify) transformation for @(tsee mbt) noted above.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "quicklisp" "Quicklisp Library"))

   (xdoc::p
    "The @(see quicklisp) library is now ignored for regressions of ACL2 built
     on LispWorks, due to an asdf version incompatibility with the asdf.lisp
     provided by LispWorks Version 8.0.  That problem may become a problem for
     future versions of other host Lisps, as they too update their asdf
     versions.  Perhaps this will be fixed by someone in the ACL2 community;
     see GitHub Issue #1332.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std::std/util" "Standard Utilities Library"))

   (xdoc::p
    "The @(tsee defret) utility could malfunction when including an uncertified
     book.  This has been fixed by tweaking a @(tsee defsection) utility to set
     the ``most recent function'' non-locally.  This fixes GitHub Issue
     #1302.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Tools")

   (xdoc::p
    "When the tool @(tsee prove$) is interrupted (with @('Control-C')), control
     now returns to the top level.  Formerly, that `abort' merely caused
     @('prove$') to return @('(mv nil nil state)').  Also if the given term and
     (if supplied) hints have illegal syntax, an error now occurs.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Licensing Changes")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Build System Updates")

   (xdoc::p
    "As discussed in topic @(see note-8-5), essentially all support for
     building ACL2 without the @(see hons-enabled) features has been removed.
     The build system has been similarly updated, in particular by eliminating
     the @('hons-only') value for @('cert_param') and the exported variable
     @('ACL2_HAS_HONS').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Testing")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Miscellaneous")

   ))

(defxdoc note-8-4-books

; Please add information about your library in the appropriate
; category below --- the category title is enclosed in (xdoc::h3 ...)
; (of course, feel free to add a new category if needed).  To
; ensure consistency with the style of previous book release doc
; topics, please follow the following convention:

;  (xdoc::h4 "Your Library Title")
;  (xdoc::p "Details go here.")

; Please put the h4's in alphabetical order, each preceded by 40 semicolons.
; You can also use (xdoc::h5 ...) under each h4, e.g. for sub-libraries:
; There is no need to order the h5's alphabetically,
; but please precede each h5 by 20 semicolons.
; If you are stuck, see the entries about other libraries.

  :parents (note-8-4 release-notes-books)

  :short "Release notes for the ACL2 Community Books for ACL2 8.4"

  :long

  (xdoc::topstring

   (xdoc::p
    "The following is a brief summary of
     changes made to the @(see community-books)
     between the releases of ACL2 8.3 and 8.4.")

   (xdoc::p
    "See also @(see note-8-4) for the changes made to ACL2 itself.
     For additional details,
     you may also see the raw "
    (xdoc::ahref "https://github.com/acl2/acl2/commits/master" "commit log")
    ".")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "New Libraries")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "ACL2 Arrays Library")

   (xdoc::p "A library to support reasoning about programs that use ACL2
   arrays (e.g., those satisfying @(tsee array1p)).  Includes operations that make
   such arrays exapandable.  Includes a tool for defining typed ACL2 arrays.  See
   @('[books]/kestrel/acl2-arrays/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "acl2pl::acl2-programming-language"
                             "ACL2 Programming Language Library"))

   (xdoc::p
    "This is a library about the ACL2 programming language.
     It includes a formalization of its evaluation semantics.
     (This is just the work of this library's author,
     not an official semantics of the ACL2 programming language;
     see @(see evaluation) for an official description
     of the ACL2 evaluation semantics.)")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Algorithm Theories Library")

   (xdoc::p "A library has been started to collect algorithm schemes, starting
   with a scheme for a generic tail recursive function. See
   @('[books]/kestrel/algorithm-theories/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Arrays-2D Library")

   (xdoc::p "A formalization of two-dimensional arrays as lists of lists (both
   with arbitrary elements and with elements that are known to be bit-
   vectors).  See @('[books]/kestrel/arrays-2d/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "bigmem::bigmem" "Bigmem"))

   (xdoc::p
    "A library that defines a @('2^64')-byte memory model that is
  logically a record but provides array-like performance during
  execution.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "c::c" "C Library"))

   (xdoc::p
    "This is a library about the C language.
     It contains a formalization of (some aspects of) the C language
     and ATC (`ACL2 To C'), a C code generator for ACL2.")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "c::atc" "ATC, the C Code Generator for ACL2"))

   (xdoc::p
    "This is a proof-generating C code generator for ACL2.
     Besides the C code, it also generates proofs (i.e. ACL2 theorems)
     asserting the correctness of the C code.")

   (xdoc::p
    "This currently covers a relatively limited subset of ACL2 and C.
     The coverage is being extended.")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "c::language" "C Language Formalization"))

   (xdoc::p
    "This currently covers just
     character sets, bytes, and keywords.
     The coverage is being extended.")

   (xdoc::p
    "A preliminary formalization of
     the static and dynamic semantics of a subset of C
     can be found as part of "
    (xdoc::seetopic "c::atc" "ATC")
    ". Some of that material may be moved here in the future.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "isar::isar" "Isar Library"))

   (xdoc::p
    "This is a library to support proofs in the style of Isabelle's
     Isar (Intelligent Semi-Automated Reasoning) language.
     It is just a small step in that direction for now.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "json::json" "JSON Library"))

   (xdoc::p
    "This is a library about " (xdoc::ahref "json.org" "JSON") ".
     It currently contains an initial abstract syntax of JSON,
     consisting of " (xdoc::seetopic "fty" "fixtypes") ";
     it also contains some initial operations on this abstract syntax,
     as well as a translator from the output of the parser at
     @('[books]/kestrel/json-parser/') to the abstract syntax.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "JSON Parser")

   (xdoc::p "A JSON parser implemented in ACL2, including Unicode support.  See
   @('[books]/kestrel/json-parser/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "JVM Library")

   (xdoc::p "Kestrel's model of the Java Virtual Machine, including support for
   code proofs and lifting.  Works with Kestrel's Axe toolkit.  Also includes a
   class file parser.  See @('[books]/kestrel/jvm/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Number Theory Library")

   (xdoc::p "A library about number theory, dealing with notions like
   primality, divisibility, quadratic residues, etc.  Includes the defprime and
   defprime-alias tools to introduce standard reasoning machinery about
   primes.  Includes a proof of the Tonelli-Shanks Modular Square Root Algorithm.
   See @('[books]/kestrel/number-theory/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "obag::obags" "Ordered Bags Library"))

   (xdoc::p
    "This is a library that represents bags (a.k.a. multisets)
     as non-strictly-ordered lists.
     Thus, they capture (up to isomorphism) the mathematical notion of bag;
     in particular, bag equality is @(tsee equal).")

   (xdoc::p
    "This is analogous to "
    (xdoc::seetopic "set::std/osets" "the library of ordered sets")
    " and to "
    (xdoc::seetopic "omap::omaps" "the library of ordered maps")
    ".")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "mimc::mimc" "MiMC Library"))

   (xdoc::p
    "This is a library that formally specifies and implements
     the Minimal Multiplicative Complexity (MiMC) hash function
     as used by "
    (xdoc::seetopic "zksemaphore::semaphore" "Ethereum's Semaphore")
     ". "
     "This is currently under the "
    (xdoc::seetopic "crypto::cryptography" "cryptographic library")
    ".")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "pfcs::prime-field-constraint-systems"
                             "PFCS (Prime Field Constraint System) Library"))

   (xdoc::p
    "This is a library that introduces and formalizes
     the notion of PFCS (Prime Field Constraint Systems),
     which generalize R1CS and possibly other constraint systems
     for zero-knowledge proofs.
     This is currently under the "
    (xdoc::seetopic "crypto::cryptography" "cryptographic library")
    ".")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Random Library")

   (xdoc::p "A lightweight library containing some simple random number
   generators.  See @('[books]/kestrel/random/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "exld::execloader"
                             "Read and Parse ELF/Mach-O Binary Files"))

   (xdoc::p
    "This library can be used to read in sections of ELF/Mach-O files into ACL2.
     An older version of these books used to live in the @(tsee x86isa::x86isa)
     library.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Sequences Library")

   (xdoc::p "A library for defining higher-order operations over lists (defforall,
   defexists, defmap, and deffilter).  See @('[books]/kestrel/sequences/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "simpl-imp::imp-language"
                             "Simple Programming Language Imp"))

   (xdoc::p
    "This is a library about a simple programming language, called Imp,
     found (with small variations) in a variety of didactic resources.
     This library formalizes syntax and semantics of this language,
     and provides a program-mode interpreter of Imp programs.
     This library may be extended with examples of
     formal verification of Imp programs in ACL2.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "solidity::solidity" "Solidity Library"))

   (xdoc::p
    "This is a library about
     the Solidity language for Ethereum smart contracts.
     It includes a formalization of some aspects of the language.
     There are plans to extend this to cover more aspects.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Strings-Light Library")

   (xdoc::p "A lightweight library about strings, including changing case,
   splitting strings and character lists, etc.  See
   @('[books]/kestrel/strings-light/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Terms-Light Library")

   (xdoc::p "A lightweight library of operations on terms (e.g., finding free
   and bound vars and applying variable substitutions).  See
   @('[books]/kestrel/terms-light/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Typed-Lists-Light Library")

   (xdoc::p "A lightweight library dealing with lists of objects of particular
   types (rather than lists in general).  For example, lists of integers, of
   symbols, of pseudo-terms, etc.  See
   @('[books]/kestrel/typed-lists-light/').")

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Unicode-Light Library")

   (xdoc::p "A lightweight library about Unicode, dealing with UTF-8 encoding and
   UTF-16 surrogate code points.  See @('[books]/kestrel/unicode-light/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Untranslated Term Library")

   (xdoc::p "A new library for manipulating untranslated terms, which allows
   structure to be maintained that would be lost by translation.  See
   @('[books]/kestrel/untranslated-terms/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "X86 Library (Kestrel)")

   (xdoc::p
    "This library contains Kestrel's x86 proof machinery, which complements the
   X86ISA model.  This library focuses on readability of proof terms and
   supporting the lifting of x86 code into logic with the Axe toolkit.  It also
   includes parsers for PE and Mach-O executables.  See
   @('[books]/kestrel/x86/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "yul::yul" "Yul Library"))

   (xdoc::p
    "This is a library about the Yul intermediate language,
     currently used in the Ethereum Solidity compiler
     but designed for more general use.
     This library includes a formalization of some aspects of the language.
     There are plans to extend this to cover more aspects.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "zcash::zcash" "Zcash Library"))

   (xdoc::p
    "This is a library about the Zcash blockchain currency,
     which is based on zero-knowledge proofs.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Changes to Existing Libraries")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "abnf::abnf" "ABNF Library"))

   (xdoc::p
    "The proofs of correctness of the grammar parser
     have been moved to a separate file,
     so that including the parser
     does not necessarily also includes the proofs,
     and so that book certification can be faster.")

   (xdoc::p
    "A new file and XDOC topic has been started
     to collect parsing primitives,
     i.e. parsing functions from the ABNF grammar parser
     that are more generally useful than that parser.
     These parsing primitives may be useful to write parsers
     for other languages specified by ABNF grammars
     (besides ABNF itself, which is what the grammar parser does).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Alists-Light Library")

   (xdoc::p "New rules and books have been added, including books on
   @('alistp'), @('clear-key'), and @('keep-pairs'). See
   @('[books]/kestrel/alists-light/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "apt::apt" "APT Library"))

   (xdoc::p
    "An " (xdoc::seetopic "apt::defaults-table" "APT defaults table")
    " has been added, analogous to the "
    (xdoc::seetopic "acl2-defaults-table" "ACL2 defaults table")
    " but specific to APT.
     Utilities to set and retrieve a number of defaults have also been added.")

   (xdoc::p
    "Some XDOC constructors have been added, and others have been improved.
     See @(see xdoc::apt-constructors).")

   (xdoc::p
    "Some input processors have been added, and others have been improved.
     See @(see apt::input-processors).")

   (xdoc::p
    "A new transformation has been added:
     @(tsee apt::schemalg), the `schematic algorithm transformation'.
     This transformation applies algorithm schemas
     to non-executable specifications:
     given a functional specification
     (e.g. consisting of an input/output relation,
     possibly as a precondition and postcondition),
     this transformation partially determines the solution
     and generates sub-specifications that, once recursively solve,
     provide a solution to the initial specification.
     In particular, divide-and-conquer algorithm schemas are supported:
     the schema is a recursive function that
     decompose the input,
     solve the sub-input(s),
     and composes the sub-output(s) to obtain an output.
     This schematic algorithm transformation is currently realized
     using " (xdoc::seetopic "soft::soft" "SOFT") " to represent
     specifications and algorithm schemas,
     with specifications as second-order functions
     and refinement as backward implication,
     as described in the ACL2-2015 Workshop paper on SOFT.
     In the future, this transformation may be extended to represent
     specifications and algorithm schemas via the built-in @(tsee apply$).")

   (xdoc::p
    "A new transformation has been added:
     @(tsee apt::solve), the `solving transformation'.
     This attempts to directly solve a program synthesis problem,
     expressed as a constraint problem,
     via inference methods like rewriting, SMT solving, SAT solving, etc.
     Currently two rewriting methods are supported,
     along with a manual method in which the solution is supplied
     (which still automates some event and proof generation);
     support for more methods will be added.")

   (xdoc::p
    "A new transformation has been added:
     @(tsee apt::expdata), the `expanded data transformation'.
     This can realize data type refinements where
     each instance of the old data may be represented by
     multiple instances of the new data,
     according to a surjective mapping from the new to the old data.
     These are more general data type refinements than @(tsee apt::isodata),
     but the transformation is not inherently reversible
     (e.g. for raising the level of abstraction in program analysis).")

   (xdoc::p
    "The @(tsee apt::propagate-iso) transformation has been added.")

   (xdoc::p
    "A new transformation has been added: @(tsee apt::simplify), the
     `simplification transformation'.  It transforms a given definition or
     @(see term) using ACL2 reasoning, in particular by applying the
     currently (or specified) @(see enable)d @(see rewrite) rules.  The result
     is generally simpler than the input but logically equivalent to it.")

   (xdoc::p
    "The @(tsee apt::isodata) transformation has been improved as follows:")
   (xdoc::ul
    (xdoc::li
     "The @(':thm-name') input has been replaced
      with a new @(':old-to-new-name') input,
      which, when absent, is taken from the APT defaults table.")
    (xdoc::li
     "The @(':thm-enable') input has been replaced
      with a new @(':old-to-new-enable') input,
      which, when absent, is taken from the APT defaults table.")
    (xdoc::li
     "A new @(':new-to-old-name') input has been added
      to specify the name of the theorem @('new-to-old')
      that rewrites calls of the new functions
      to terms involving calls of the old function.
      This theorem is now generated along with the converse one.
      If the @(':new-to-old-name') input is absent,
      it is taken from the APT defaults table.")
    (xdoc::li
     "A new @(':new-to-old-enable') input has been added
      to specify whether the @('new-to-old') theorem is enabled or not.
      If this input is absent, it is taken from the APT defaults table.")
    (xdoc::li
     "The @('newp-of-new') theorem,
      which asserts that the new function maps
      arguments in the new representation to results in the new representation,
      is now generated not only locally to support some generated proofs,
      but also non-locally, so that it remains in the ACL2 history.
      This theorem is only generated if some result is being transformed.")
    (xdoc::li
     "A new @(':newp-of-new-name') input has been added
      to specify the name of the @('newp-of-new') theorem.
      This input is allowed only if some result is being transformed,
      because otherwise no @('newp-of-new') theorems is generated.")
    (xdoc::li
     "A new @(':newp-of-new-enable') input has been added
      to specify whether the @('newp-of-new') theorem is enabled or not.
      This input is allowed only if some result is being transformed,
      because otherwise no @('newp-of-new') theorems is generated."))

   (xdoc::p
    "The @(tsee apt::restrict) transformation has been improved as follows:")
   (xdoc::ul
    (xdoc::li
     "The transformation has been simplified
      by removing the @(':non-executable') option,
      which does not seem necessary or useful.
      The new function is marked non-executable
      if and only if the target function is.")
    (xdoc::li
     "The transformation has been made more widely or readily applicable
      by removing the applicability condition that required
      the restriction predicate to be boolean-valued.
      The new function now uses @(tsee mbt$) instead of @(tsee mbt),
      thus obviating the need for the removed applicability condition.")
    (xdoc::li
     "The @(':thm-name') and @(':thm-enable') inputs have been renamed to
      @(':old-to-new-name') and @(':old-to-new-enable'),
      in line with other transformations.
      Besides the name change, these two inputs now support
      the APT defaults table.")
    (xdoc::li
     "A new @(':new-to-old-name') input has been added
      to specify the name of the theorem @('new-to-old')
      that rewrites calls of the new functions
      to terms calls of the old function.
      This theorem is now generated along with the converse one.
      If the @(':new-to-old-name') input is absent,
      it is taken from the APT defaults table.")
    (xdoc::li
     "A new @(':new-to-old-enable') input has been added
      to specify whether the @('new-to-old') theorem is enabled or not.
      If this input is absent, it is taken from the APT defaults table."))

   (xdoc::p
    "The @(tsee apt::tailrec) transformation has been improved as follows:")
   (xdoc::ul
    (xdoc::li
     "The transformation has been extended with a new variant,
      @(':assoc-alt'), which is an alternative associative variant.")
    (xdoc::li
     "The transformation has been simplified
      by removing the @(':non-executable') option,
      which does not seem necessary or useful.
      The new function is marked non-executable
      if and only if the target function is;
      the wrapper is never marked non-executable.")
    (xdoc::li
     "The generated names for the new and wrapper functions,
      when @(':new-name') is @(':auto')
      and/or @(':wrapper-name') is @(':auto'),
      have been improved.
      If the target function is @('f{i}') (where we view @('f') as @('f{0}')),
      now the new function is @('f{j}') if no wrapper is generated;
      otherwise, the new function is @('f-aux{j}')
      and the wrapper is @('f{j}').
      Here @('j') is the smallest integer above @('i')
      that results in fresh function names.
      Note that, in this way, these automatically generated names
      are always numbered names,
      which facilitates the application of further transformations.")
    (xdoc::li
     "The default of the @(':wrapper') input
      has been changed from @('t') to @('nil').
      The rationale is that not generating the wrapper is expected to be
      more frequent than generating it.")
    (xdoc::li
     "Now the @(':wrapper-enable') input, if absent, is taken from the "
     (xdoc::seetopic "apt::defaults-table" "APT defaults table")
     ".")
    (xdoc::li
     "An @(':accumulator') input has been added to optinally specify
      the name of the accumulator argument of the new function.")
    (xdoc::li
     "The theorem that rewrites the target function
      in terms of the new function
      is now always generated, regardless of the @(':wrapper') input.
      If @(':wrapper') is @('t'),
      the theorem that rewrites the target function
      in terms of the wrapper function
      is also generated.")
    (xdoc::li
     "The @(':thm-name') input has been replaced with
      two new inputs @(':old-to-new-name') and @(':old-to-wrapper-name'),
      which individually control the names of the theorems that rewrite
      the target function in terms of the new or wrapper function.
      These new inputs, if absent, take their values from the "
     (xdoc::seetopic "apt::defaults-table" "APT defaults table")
     ".")
    (xdoc::li
     "The @(':thm-enable') input has been replaced with
      two new inputs @(':old-to-new-enable') and @(':old-to-wrapper-enable'),
      which individually control the enablement of the theorems that rewrites
      the target function in terms of the new or wrapper function.
      These new inputs, if absent, take their values from the "
     (xdoc::seetopic "apt::defaults-table" "APT defaults table")
     ".")
    (xdoc::li
     "Now the transformation also generates a theorem
      that rewrites the new function in terms of the old function.
      The name and enablement of this theorem are controlled
      by two new inputs @(':new-to-old-name') and @(':new-to-old-enable').
      These new inputs, if absent, take their values from the "
     (xdoc::seetopic "apt::defaults-table" "APT defaults table")
     ".")
    (xdoc::li
     "Now the transformation also generates a theorem
      that rewrites the wrapper function in terms of the old function
      (when the @(':wrapper') input is @('t')).
      The name and enablement of this theorem are controlled
      by two new inputs
      @(':wrapper-to-old-name') and @(':wrapper-to-old-enable').
      These new inputs, if absent, take their values from the "
     (xdoc::seetopic "apt::defaults-table" "APT defaults table")
     ".")
    (xdoc::li
     "The heuristics for inferring the domain of the binary operator
      (when the @(':domain') input is, generally by default, @(':auto'))
      have been extended to infer more cases automatically.")
    (xdoc::li
     "The target function's @(tsee if) body,
      after translation and @(tsee let) expansion,
      can now have a recursive `then' branch and a non-recursive `else' branch.
      Before, the `then' branch had to be the non-recursive one
      and the `else' branch had to be the recursive one.
      This makes the transformation more widely applicable."))

   (xdoc::p
    "A file @('[books]/kestrel/apt/tailrec-examples.lisp') has been added.
     It contains examples of uses of @(tsee apt::tailrec),
     with explanatory comments.
     This could serve as a preliminary tutorial.")

   (xdoc::p
    "New design notes about specifications and refinements have been added,
     along with a manual page that describes various forms of specifications.")

   (xdoc::p
    "A variety of APT-related utilities have been added, including @('deftransformation'), which
     can be used to generate transformations (taking care of much of the boilerplate code).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Arithmetic-Light Library")

   (xdoc::p "Many new rules and books have been added, including books on
   @('integer-length') @('ceiling-of-lg'), evenness and oddness, @('truncate'),
   @('rem'), @('ash'), @('min'), @('max'), @('<='), @('abs'), and @('natp').
   Commonly used rules about arithmetic types have been collected, and a
   utility has been added to prevent calls of @('expt') on huge exponents.  See
   @('[books]/kestrel/arithmetic-light/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Axe Toolkit")

   (xdoc::p "Major additions have been made to the open-source Axe toolkit,
   which now includes most of Axe.  The library now includes Axe's connection
   to the STP solver as well as machinery to make customized Axe rewriters and
   provers.  A basic (general-purpose) prover and rewriter are included, as are
   a legacy prover and rewriter.  Utilities to unroll specifications through
   rewriting are included, as is the Axe Tactic Prover.  Many rules that have
   been useful in Axe proofs are also included.  See @('[books]/kestrel/axe/').")

   (xdoc::p "A toolkit for using Axe to reason about JVM code has been added.
   It includes utilities to lift JVM code into logic.  A Formal Unit Tester
   tool is also included, to support small solver-backed proofs about bounded
   executions of programs.  See @('[books]/kestrel/axe/jvm/').")

   (xdoc::p "A toolkit for using Axe to reason about x86 code has been added.
   It includes utilities to lift x86 code into logic. See
   @('[books]/kestrel/axe/x86/').")

   (xdoc::p "A toolkit for using Axe to reason about R1CSes has been added.  It
   includes utilities to lift R1CSes into logic and verify them.  See
   @('[books]/kestrel/crypto/r1cs/tools/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Booleans Library")

   (xdoc::p "New rules and defcongs have been added.  See
   @('[books]/kestrel/booleans/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "BV Library")

   (xdoc::p
    "Extensive additions have been made, including over 1000 new rules.  Books
    have been added covering many more BV operations, including subtraction,
    arithmetic negation, multiplicaton, shifts, bitwise @('OR') and @('AND'),
    logical negation, signed and unsigned comparisons, signed and unsigned
    division and remainder, trimming, sign extension, various single-bit
    operations, bit-vector-valued conditionals, converting between bits and
    booleans, recognizing bits and (signed and unsigned) bytes, repeating a
    bit, and counting the number of 1 bits.  Rules have been added to
    characterize signed addition overflow and underflow and to turn BV ops into
    more common or more idiomatic operations.  A formalization of one's
    complement numbers and addition has been added.  Various syntactic
    functions have been added for BV-valued terms.  See
    @('[books]/kestrel/bv/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "BV-Lists Library")

   (xdoc::p "Many new rules and books have been added.  New books
   include ones about @('bv-arrayp'), @('bv-array-read'), @('bv-array-write'),
   @('all-all-unsigned-byte-p'), @('width-of-widest-int'), @('bvnot-list'),
   @('getbit-list'), @('map-slice'), @('bvplus-list'), @('logext-list'),
   @('bv-nth'), @('map-packbv'), @('all-signed-byte-p'), conversions between
   lists and bv-arrays, @('packbv-little'), and @('byte-listp').  Utilities
   have been added that deal with about patterns in the elements of BV lists.
   See @('[books]/kestrel/bv-lists/')")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "crypto::cryptography" "Cryptographic Library"))

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 "BLAKE Library")

   (xdoc::p "Formal specifications of the BLAKE2s, BLAKE2s-extended, and
   BLAKE-256 hash functions have been added. See
   @('[books]/kestrel/crypto/blake/').")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "ecurve::elliptic-curves"
                             "Elliptic Curve Library"))

   (xdoc::p
    "The formalization of "
    (xdoc::seetopic "ecurve::short-weierstrass-curves"
                    "short Weierstrass curves")
    " has been extended and improved.")

   (xdoc::p
    "A formalization of "
    (xdoc::seetopic "ecurve::twisted-edwards" "twisted Edwards curves")
    " has been added.")

   (xdoc::p
    "A formalization of "
    (xdoc::seetopic "ecurve::montgomery" "Montgomery curves")
    " has been added.")

   (xdoc::p
    "A formalization of the "
    (xdoc::seetopic "ecurve::birational-montgomery-twisted-edwards"
                    "birational equivalence between
                     Montgomery and twisted Edwards curves")
    " has been added.")

   (xdoc::p
    "The file
     @('[books]/kestrel/crypto/ecurve/bls12-377-domain-parameters.lisp')
     has been added.
     It introduced some parameters of the BLS12-377 elliptic curve.")

   (xdoc::p
    "A formalization of the "
    (xdoc::seetopic "ecurve::edwards-bls12" "Edwards BLS12 elliptic curve")
    " has been added.")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "r1cs::r1cs" "Rank-1 Constraint Systems (R1CS)"))

   (xdoc::p "A formal semantics for rank-1 constraint systems (R1CSes) has been
   added.  These are often used by zero-knowledge proofs.  Extensive reasoning
   support for reasoning about R1CSes has also been added, including verified R1CS
   gadgets and support for applying the Axe toolkit.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "error-checking" "Error Checking Library"))

   (xdoc::p
    "This library is being moved
     from @('[books]/kestrel/utilities/error-checking/')
     to @('[books]/kestrel/error-checking/').
     It is also being refactored and improved in the process.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "ethereum::ethereum" "Ethereum Library"))

   (xdoc::p
    "Some theorems about hex-prefix encoding have been added.")

   (xdoc::p
    "A sub-library for the Semaphore gadget has been added.  This includes
    various specifications and proofs of Semaphore-related R1CSes, including a
    mixing function from BLAKE2s and 3 variants of the MiMC hash function.  It
    also includes Semaphore-specialized Axe tools to lift R1CSes into logic and
    verify them.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "event-macros" "Event Macros Library"))

   (xdoc::p
    "The utilities
     @(tsee cw-event),
     @(tsee fail-event),
     @(tsee make-event-terse), and
     @(tsee try-event)
     have been moved here
     from @('[books]/kestrel/utilities/user-interface.lisp').")

   (xdoc::p
    "The XDOC constructor @('xdoc::evmac-section-form-auto') has been removed.
     Not being able to use this XDOC constructor avoids
     additional inter-dependencies among books
     that do not seem worth the small savings in writing user documentation,
     whose general form section should be normally a small fraction.")

   (xdoc::p
    "The XDOC constructor @(tsee xdoc::evmac-topic-event-generation)
     has been extended with an additional option.")

   (xdoc::p
    "New XDOC constructors have been added
     and some XDOC constructors have been improve.")

   (xdoc::p
    "A utility @(tsee evmac-prepare-proofs) has been added,
     to improve the robustness of proofs generated by event macros.")

   (xdoc::p
    "Utilities have been added to generate various kinds of event forms
     from attributes of the event forms.")

   (xdoc::p
    "Some general XDOC topics about event macros have been added,
     which can be referenced by the user documentation of event macros.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "exld::execloader"
                             "Read and Parse ELF/Mach-O Binary Files"))

   (xdoc::p
    "ELF reader now gets the contents of all the sections listed in
    the headers of a given ELF binary. Also, the package name has been
    changed from @('EL') to @('EXLD').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "file-io-light" "File-Io-Light Library"))

   (xdoc::p
    "Various lightweight utilities have been added to read and write files (of
    bytes, characters, and objects).  These include a utility to read the bytes
    of a file into a stobj array.  Reasoning support has also been added for
    various built-in I/O functions.  Related utilities have been added, such as
    to check whether a file exists or is newer than a given date.  See
    @('[books]/kestrel/file-io-light/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "fty" "Fixtype Definition Library"))

   (xdoc::p
    "A new macro @(tsee fty::defbyte-ihs-theorems) has been added
     to generate theorems about fixtypes introduced via @(tsee fty::defbyte)
     and functions in the " (xdoc::seetopic "ihs" "IHS") " library.
     This macro has been used to generate, and make available,
     these theorems for some of the "
     (xdoc::seetopic "fty::defbyte-standard-instances"
                     "@('fty::defbyte') standard instances")
     ".")

   (xdoc::p
    "More "
    (xdoc::seetopic "fty::defbyte-standard-instances"
                    "@('fty::defbyte') standard instances")
    " have been added.")

   (xdoc::p
    "The macro @(tsee fty::defset) has been improved
     to generate additional theorems.")

   (xdoc::p
    "The macro @(tsee fty::defomap) has been improved
     to generate additional theorems.")

   (xdoc::p
    "A fixtype @(tsee nat-set) of osets of natural numbers has been added.")

   (xdoc::p
    "@(tsee fty::deflist) has been extended to generate a theorem
     about the list fixer applied to @(tsee repeat).")

   (xdoc::p
    "A macro @(tsee fty::defsubtype) has been added.")

   (xdoc::p
    "A macro @(tsee fty::defunit) has been added.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "java::java" "Java Library"))

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "java::aij"
                             "AIJ, the Deep Embedding of ACL2 into Java"))

   (xdoc::p
    "More " (xdoc::ahref "https://junit.org" "JUnit")
    " unit tests have been added,
     integrated with the IntelliJ IDEA project.")

   (xdoc::p
    "The Java implementations of some natively implemented ACL2 functions
     have been optimized.")

   (xdoc::p
    "Variant Java implementations of some natively implemented ACL2 functions
     have been added,
     in support of the automatic mapping, in the shallow embedding with guards,
     of ACL2 booleans and characters to Java booleans and characters.")

   (xdoc::p
    "A native implementation has been added
     of the @(tsee char) ACL2 built-in function.
     As with other native implementations,
     this consists of a few variants for different input and output types.
     This native Java implementation is faster than
     the Java code obtained from the unnormalized body of @(tsee char),
     which converts the string to a list of characters
     and then calls @(tsee nth);
     the native Java implementation accesses the string directly.")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "java::atj"
                             "ATJ, the Java Code Generator for ACL2"))

   (xdoc::p
    "The model of Java primitive arrays has been extended
     with functions to convert between arrays and corresponding ACL2 lists.
     The model has been made much more compact
     by defining and using a macro that captures the structure
     common to the eight Java primitive array types.")

   (xdoc::p
    "Support has been added to recognize ACL2 functions
     that convert between Java primitive arrays and ACL2 lists,
     and translate them to Java code that converts between arrays and lists.
     This applies to the shallow embedding with guards.")

   (xdoc::p
    "In the shallow embedding with guards,
     now ACL2 booleans are mapped to Java booleans when possible.
     The generated Java code takes care of converting, as needed,
     between the Java booleans
     and the @('Acl2Symbol') objects for @('t') and @('nil').
     This new mapping happens automatically;
     it is separate from the explicit targeting of Java booleans
     via the ACL2 model of Java boolean values.")

   (xdoc::p
    "In the shallow embedding with guards,
     now ACL2 characters are mapped to Java characters when possible.
     The generated Java code takes care of converting, as needed,
     between the Java characters
     and the @('Acl2Character') objects.
     This new mapping happens automatically;
     it is separate from the explicit targeting of Java characters
     via the ACL2 model of Java character values.")

   (xdoc::p
    "In the shallow embedding with guards,
     now ACL2 strings are mapped to Java strings when possible.
     The generated Java code takes care of converting, as needed,
     between the Java strings (i.e. @('java.lang.String') objects)
     and the @('Acl2String') objects.")

   (xdoc::p
    "Some of the generated Java code in the shallow embedding with guards
     has been made more idiomatic.
     Calls of the Java method corresponding to @(tsee not)
     are now avoided in favor of using Java's @('!') operator
     or Java's @('==') operator with the symbol @('nil').
     Calls of ACL2's @(tsee and) are translated
     to Java's @('&&') operator when possible.
     Calls of ACL2's @(tsee or) are translated
     to Java's @('||') operator when possible.")

   (xdoc::p
    "A new post-translation step has been added
     to ``inline'' (in a suitable sense) the calls of the array write methods
     that are generated by the translation step.
     This makes the generated Java code more idiomatic.
     This applies to the shallow embedding with guards.")

   (xdoc::p
    "A new post-translation step has been added
     to simplify generated Java conditional expressions
     whose test is a boolean literal.")

   (xdoc::p
    "The Java code to build the ACL2 environment is now generated
     in a separate Java class in a separate Java file.
     This class's name is obtained by adding @('Environment')
     after the main class's name.
     This way, the main class is free of the extensive and boilerplate code
     to build the ACL2 environment,
     making it easier to find and see the ``interesting'' generated Java code.")

   (xdoc::p
    "The Java abstract syntax used by the code generator is now more precise,
     in the sense that it captures more syntactic aspects of Java.")

   (xdoc::p
    "ATJ function types have been verified and recorded
     for more built-in functions,
     thus avoiding certain type casts and other conversions
     in the generated Java code.
     ATJ function types have also been verified and recorded
     for certain library functions, for the same reason;
     these files can be included as needed.")

   (xdoc::p
    "The macros @(tsee java::atj-main-function-type)
     and @(tsee java::atj-other-function-type)
     have been extended with an option to provide hints
     for the theorems they prove internally.")

   (xdoc::p
    "An option @(':ignore-whitelist') has been added
     to ignore the whitelist of ACL2 functions with raw Lisp code,
     i.e. to translate them to Java (so long as they have an unnormalized body).
     This must be used by caution: side effects in the raw Lisp code
     will not be replicated in Java,
     e.g. @(tsee hard-error) will just return @('nil').
     This could be useful when the functions in question
     are unreachable under guard verification, for instance.
     The default is @('nil'), i.e. do not ignore the whitelist,
     so the user must explicitly write @(':ignore-whitelist t')
     to ignore the whitelist.")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "java::language" "Java Language Formalization"))

   (xdoc::p
    "Some functions and theorems related to integer literals have been added.
     These are part of the formalized abstract syntax of Java.")

   (xdoc::p
    "Some theorems about the Java primitive operations have been added.")

   (xdoc::p
    "More aspects of the Java syntax have been formalized, including:
     the ISO 8851-1 subset of Unicode characters;
     type identifiers;
     unqualified method identifiers;
     package names;
     reference types; and
     all types.")

   (xdoc::p
    "The formalization, including the ABNF grammar,
     have been updated to Java 14.
     In particular, this involved updating of the ABNF grammar with
     @('switch') expressions and @('yield') statements.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Library Wrappers")

   (xdoc::p
    "A library wrapper for @('sublistp') has been added, as has a robust variant of
    @('make-flag').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Lists-Light Library")

   (xdoc::p
    "Many rules, congruences, and new books have been added.  New books cover
   the functions @('subsequencep'), @('subsequencep-equal'), @('last-elem'),
   @('subrange'), @('update-subrange'), @('finalcdr'), @('all-equal$'),
   @('all-eql$'), @('all-same'), @('all-same-eql'), @('add-to-end'),
   @('first-non-member'), @('group')/@('ungroup') (for splitting and
   flattening), @('count-occs'), @('prefixp'), @('len-at-least'),
   @('remove-equal'), @('remove-duplicates-equal'), @('find-index'), and
   @('remove-nth'). See @('[books]/kestrel/prime-fields/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "omap::omaps" "Ordered Maps (Omaps) Library"))

   (xdoc::p
    "Added an operation to create an omap
     from a list of keys and a corresponding list of values.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Prime-Fields")

   (xdoc::p
    "Many new rules have been added, and existing rules have been improved.
    These include many rules for recogizing R1CS gadgets.  The library is more
    organized, and some proofs have been made faster.  @('bind-free') rules
    have been added for canceling addends and moving negations.  Utilities have
    been added for naming and printing special constants. See
   @('[books]/kestrel/prime-fields/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "rstobj2::defrstobj"
                             "Record-like Stobjs"))

   (xdoc::p
    "Add support for defining fields based off child stobjs.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "soft::soft" "SOFT Library"))

   (xdoc::p
    "A new macro @(tsee soft::defsoft) has been added,
     to record a function as second-order
     after the function has been introduced via a non-SOFT event.
     The SOFT macros
     @(tsee soft::defun2),
     @(tsee soft::defchoose2), and
     @(tsee soft::defun-sk2)
     have been simplified to be abbreviations of
     @(tsee defun), @(tsee defchoose), and @(tsee defun-sk)
     followed by @(tsee soft::defsoft).")

   (xdoc::p
    "New macros
     @('defund2'),
     @(tsee soft::define2),
     @(tsee soft::defund-sk2), and
     @(tsee soft::define-sk2)
     have been added.
     These abbreviate
     @(tsee defund),
     @(tsee define),
     @(tsee defund-sk), and
     @(tsee std::define-sk)
     followed by @(tsee soft::defsoft),
     analogously to other macros as described above.")

   (xdoc::p
    "A new macro @(tsee soft::defequal),
     to define second-order equalities between functions
     and provide some reasoning support for them.")

   (xdoc::p
    "An option @(':enable') has been added to @(tsee soft::defun-inst),
     to control the enablement of the generated function
     (and, for quantifier functions, also of the associated rewrite rule).")

   (xdoc::p
    "An option @(':enable') has been added to @(tsee soft::defthm-inst),
     to control the enablement of the generated theorem.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/basic" "Standard Basic Library"))

   (xdoc::p
    "A new utility @(tsee good-valuep) has been added,
     which checks whether a value is either a good atom
     or a @(tsee cons) pair whose components are recursively good values.
     That is, the value must not be a bad arom
     or contains (directly or indirectly) bad atoms.")

   (xdoc::p
    "A new utility @(tsee good-pseudo-termp) has been added,
     which checks whether a pseudo-term only contains good values
     (see @(tsee good-valuep)) in its quoted constants.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/io" "Standard IO Library"))

   (xdoc::p
    "Modified the raw-Lisp implementation of @(tsee read-string) to catch
     errors successfully, as intended.  This could fail in SBCL
     2.0.5 (implementation note: because the error message referenced a string
     stream that was already closed).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/system" "Standard System Library"))

   (xdoc::p
    "A new utility @(tsee check-if-call) has been added,
     to check if a term is a call of @(tsee if)
     and to return its three arguments if that is the case.")

   (xdoc::p
    "A new utility @(tsee check-and-call) has been added,
     to check if a term is a (translated) call of @(tsee and)
     and to return its two conjuncts if that is the case.")

   (xdoc::p
    "A new utility @(tsee check-or-call) has been added,
     to check if a term is a (translated) call of @(tsee or)
     and to return its two disjuncts if that is the case.")

   (xdoc::p
    "A new utility @(tsee check-mbt-call) has been added,
     to check if a term is a (translated) call of @(tsee mbt)
     and to return its argument if that is the case.")

   (xdoc::p
    "A new utility @(tsee check-mbt$-call) has been added,
     to check if a term is a (translated) call of @(tsee mbt$)
     and to return its argument if that is the case.")

   (xdoc::p
    "A theorem about the built-in @('flatten-ands-in-lit') has been added,
     in @('[books]/kestrel/std/system/flatten-ands-in-lit').")

   (xdoc::p
    "A new utility @(tsee fresh-name-listp-msg-weak) has been added,
     which lifts @(tsee fresh-namep-msg-weak) to lists.")

   (xdoc::p
    "The utility @(tsee check-mv-let-call) has been generalized
     to check for the presence of @(tsee hide) wrappers
     introduced when @(tsee mv-let) has @(tsee ignore) declarations,
     and to return information about their presence or absence.")

   (xdoc::p
    "The utilities
     @(tsee install-not-normalized-event) and
     @(tsee install-not-normalized-event-lst)
     have been improved to return an additional result,
     namely the updated list of names to avoid.
     This helps making the calling code more concise and less error-prone.")

   (xdoc::p
    "The utility @(tsee install-not-normalized) now uses the untranslated
     version of the original body in the generated definition.")

   (xdoc::p
    "A new utility @(tsee if-tree-leaf-terms) has been added,
     to collect the leaf sub-terms of a term
     according to the @(tsee if) tree structure of the term.")

   (xdoc::p
    "The utility @('acceptable-rewrite-rulep') has been moved
     from @('[books]/kestrel/utilities/') to @('[books]/std/system/').")

   (xdoc::p
    "New utilities @(tsee irrelevant-formals-info) and @(tsee
     chk-irrelevant-formals-ok) have been added, to perform an @(see
     irrelevant-formals) check on a given definition or list of definitions.")

   (xdoc::p
    "New utilities have been added to find the sources of @(see invariant-risk)
     for given functions.  See @('[books]/std/system/invariant-risk.lisp').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/testing" "Standard Testing Library"))

   (xdoc::p
    "The contents of the file @('[books]/misc/assert-tests.lisp')
     have been moved to new separate files under Std/testing.
     That file has been removed.")

   (xdoc::p
    "The relocation stub @('[books]/misc/assert.lisp')
     for books that are now in Std/testing
     has been removed.")

   (xdoc::p
    "The event macros @(tsee assert!) and @(tsee assert!-stobj) no longer
     invoke @(tsee make-event), but rather, create direct calls of @(tsee
     assert-event).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/typed-alists"
                             "Standard Typed Alists Library"))

   (xdoc::p
    "A type @(tsee symbol-symbollist-alistp) has been added for alists
     from symbols to true lists of symbols.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std::std/util" "Standard Utilities Library"))

   (xdoc::p
    "A new event macro @(tsee defund-sk) has been added,
     which is like @(tsee defun-sk) but it disables
     (1) the function definition (if @(':constrain') is @('nil'))
     or the definition rule (if @(':constrain') is non-@('nil'))
     and (2) the rewrite rule
     if the @(':thm-enable') input is @('nil') (which is the default).")

   (xdoc::p
    "A new event macro @(tsee defmacro+) has been added,
     with is like @(tsee defmacro) but with "
    (xdoc::seetopic "xdoc" "XDOC")
    "integration.")

   (xdoc::p
    "Like @(see defun-nx), now @(see define) also disables the executable
     counterpart of a non-executable function.")

   (xdoc::p
    "A new event macro @(tsee defmapping) has been added,
     to verify and record mappings that must be (based on supplied options)
     injective, surjective, or bijective.")

   (xdoc::p
    "The @(tsee defiso) event macro is now
     a specialization of @(tsee defmapping),
     implemented as a thin wrapper of @(tsee defmapping).")

   (xdoc::p
    "A new event macro @(tsee definj) has been added
     to verify and record injective mappings.
     It is a specialization of @(tsee defmapping),
     implemented as a thin wrapper of @(tsee defmapping).")

   (xdoc::p
    "A new event macro @(tsee defsurj) has been added
     to verify and record surjective mappings.
     It is a specialization of @(tsee defmapping),
     implemented as a thin wrapper of @(tsee defmapping).")

   (xdoc::p
    "A new event macro @(tsee defthm-commutative) has been added,
     to generate commutativity theorems for binary operations
     more concisely.")

   (xdoc::p
    "Support for @(':prepwork') has been added to @(tsee std::deflist).")

   (xdoc::p
    "Support for @(tsee defun-sk)'s option @(':constrain')
     has been added to @(tsee std::define-sk).")

   (xdoc::p
    "A macro @(tsee std::tuple) has been added,
     to mimic the @(tsee mv) return specifier notation
     for tuple (i.e. list) results, useful inside error triples.")

   (xdoc::p
    "The macro @(tsee std::define-sk) has been moved
     from @('[books]/kestrel/utilities/') to @('[books]/std/util/').")

   (xdoc::p
    "A new event macro @(tsee add-io-pairs) has been added, to speed
     up a function using verified input-output pairs.  Related
     utilities include @(tsee add-io-pair), @(tsee remove-io-pairs),
     @(tsee show-io-pairs), and @(tsee get-io-pairs).")

   (xdoc::p
    "A new event macro @(tsee defmin-int) has been added,
     to declarative define the minimum of
     a (possibly infinite) set of integers.
     This is similar to @(tsee defmax-nat).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Utilities Library (Kestrel)")

   (xdoc::p
    "A large number of utilities have been added, covering a wide range of
     topics.  These include dealing with event forms, making fresh names,
     manipulating hints, dealing with untranslated terms, building simple list
     structures, dealing with quoted entities, building strings, checking
     whether a symbol has properties, dealing with runes, parsing options,
     processing keyword args, and recognizing legal variable names.

     New utilities also deal with importing and legal variable names, format
     strings, printing, translation, manipulating terms, invariant risk,
     submitting events to ACL2, creating temp dirs, process IDs, usernames,
     calling scripts, macroexpansion and translation, asserts,
     untranslated-terms, redundant events, guard-holders, ruler-extenders,
     lets/lambdas, fake worlds, clause identifiers, @('progn'), unification,
     dependencies, ensuring rules are known, quieting @('make-event'), checking
     for closed lambdas, processing @('defun') and @('defthm') forms, processing
     declares, the ACL2 state, @('system-books-dir'), fixing functions,
     @('acl2-count'), @('make-ord'), @('coerce'), @('map-symbol-name'), tuples,
     @('myif'), and @'(mv-nth').")

   (xdoc::p "Various improvements have been made to @('defopeners') and
   @('defopeners-mut-rec').")

   (xdoc::p "New utilities support computing a constant using @('make-event'),
   reading a value from a file into a @('defconst'), and printing constants
   nicely.")

   (xdoc::p "A new ACL2 Lint tool can detect common ACL2 errors.")

   (xdoc::p "Reasoning about I/O channels has been improved.")

   (xdoc::p "A new tool, @('bind-from-rules') can bind free variables in rules
   by searching existing rules.")

   (xdoc::p "A new data structure, string trees, can efficiently represent a
   sequence of strings (e.g., for writing to a file).")

   (xdoc::p "A new tool supports polarity-based rewriting, whereby a term can be
   either strengthened or weakened depending on whether it is an assumption or
   a conclusion.")

   (xdoc::p "Sorting utilities have been added, including @('split-list-fast'),
   @('merge-sort-generic'), and @('defmergesort').")

   (xdoc::p "Various xdoc-related utilities have been added, including new xdoc
   constructors (such as one that creates paragraphs from blocks of text
   separated by blank lines).  A new tool, @('gen-xdoc-for-file') can generate
   xdoc topics for the events (defuns, defthms, etc.) in a file by extracting
   the actual relevant text (the definition and any immediately preceding or
   following comment lines) from the file.  Helpful wrappers for xdoc
   archiving utilities have also been added; these can help speed up manual
   building.")

   (xdoc::p "See @('[books]/kestrel/utilities/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Xdoc Library")

   (xdoc::p
    "The web-based manual now includes a clickable link to GitHub at the top of
    each documentation topic from the Community Books.  The link lets you view
    the contents of the source file that introduced that topic.")

   (xdoc::p
    "The file @('[books]/doc/top-slow.lisp') no longer actually builds a manual.
    Instead, it serves as a top-level book to detect name conflicts between
    community books.  Manual building is now taken care of by
    @('[books]/doc/top.lisp').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Licensing Changes")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Build System Updates")

   (xdoc::p
    "By default, @('make') commands for certifying ACL2 books take advantage of
     files @('*@useless-runes.lsp').  See @(see useless-runes).")

   (xdoc::p
    "One line of file @('Makefile-generic') has been tweaked to avoid the
     @('+make') construct, which may help avoid errors in FreeBSD systems.")

   (xdoc::p
    "Building of the combined ACL2+Books manual (by certifying
     @('doc/top.lisp')) has been made more efficient (more than 20% reduction
     measured when such changes were made).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Testing")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Miscellaneous")

   (xdoc::p
    "The line containing @('#!/bin/bash') at the top of various shell scripts
     has been replaced by a line containing @('#!/usr/bin/env bash'), for
     increased portability.")

   (xdoc::p
    "The book @('tools/defttag-muffled.lisp') provides a way, using a trust
     tag, to turn off all subsequent ``TTAG NOTE'' messages.  Use with care!!")

   (xdoc::p
    "See @(see rewrite$) for a flexible, convenient interface to the ACL2
     rewriter that can be called programmatically.  See @(see rewrite$-hyps)
     for a related utility that rewrites a list of hypotheses.")

   (xdoc::p
    "See @(see open-trace-file!) for a variant of @(tsee open-trace-file)
     suitable for use within @(tsee make-event).")

   (xdoc::p
    "There are some changes in the utility @(tsee make-flag) (descibed in more
     detail in its documentation).  (1) The value for keyword argument
     @(':flag-mapping') is now expected to be a list of doublets, @('(old
     new)').  The use of a list of cons pairs @('(old . new')) is still
     permitted for now, but is deprecated and will likely be unsupported with a
     future ACL2 release.  (2) The keyword argument, @(':last-body'), has been
     replaced by @(':body'), where: value @('nil') has the same meaning as
     before; the value @('t') that was supplied to @(':last-body') is supplied
     as @(':last') to the new keyword, @(':body'); and a new form, a list of
     doublets, is permitted for specifying which @(see definition) rules to
     use.  (3) The tool is more robust when @(see xargs) declaration
     @(':normalize nil') is involved.")

   (xdoc::p
    "The utility @(tsee install-not-normalized) now takes an additional keyword
     argument, @(':enable'), specifying whether the generated @(tsee defthm)
     event is enabled.  In addition to Boolean values, it allows the default
     value, @(':auto'), specifying that the new rule is enabled if and only if
     the original defintion is enabled.  This is a change in default behavior,
     since before, the new rule was always enabled.")

   ))

(defxdoc note-8-3-books

; Please add information about your library in the appropriate
; category below --- the category title is enclosed in <h3>..</h3>
; tags (of course, feel free to add a new category if needed).  To
; ensure consistency with the style of previous book release doc
; topics, please follow the following convention:

;  (xdoc::h4 "Your Library Title")
;  (xdoc::p "Details go here.")

; Please put the h4's in alphabetical order, each preceded by 40 semicolons.
; If you are stuck, see the entries about other libraries.

; Note (probably too low level to mention in the :doc string): modified
; defxdoc-raw so that the :from field is a string rather than nil, which can be
; important for avoiding errors when building the "fast" documentation.  This
; change has avoided an error using SBCL.

  :parents (note-8-3 release-notes-books)

  :short "Release notes for the ACL2 Community Books for ACL2 8.3"

  :long

  (xdoc::topstring

   (xdoc::p
    "The following is a brief summary of
     changes made to the @(see community-books)
     between the releases of ACL2 8.2 and 8.3.")

   (xdoc::p
    "See also @(see note-8-3) for the changes made to ACL2 itself.
     For additional details,
     you may also see the raw "
    (xdoc::a :href "https://github.com/acl2/acl2/commits/master"
      "commit log")
    ".")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "New Libraries")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Alists-light library")

   (xdoc::p "A new library, @('alists-light') has been added.  It aims to
   provide basic reasoning about alists while being as lightweight as possible.
   See the directory @('[books]/kestrel/alists-light').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Arithmetic-light library")

   (xdoc::p "A new library, @('arithmetic-light') has been added.  It aims to
   provide basic arithmetic reasoning while being as lightweight as possible.  See
   the directory @('[books]/kestrel/arithmetic-light').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Axe")

   (xdoc::p "A directory has been started to contain the implementation of
   Kestrel's Axe tool.  This will be populated over time as we open source Axe.
   See the directory @('[books]/kestrel/axe').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Booleans library")

   (xdoc::p "A new library, @('booleans') has been added.  It provides
   definitions and rules about operations on booleans.  See the directory
   @('[books]/kestrel/booleans').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "BV (bit vector) library")

   (xdoc::p "A new library, @('bv'), has been added.  It contains a
   formalization of bit vectors as natural numbers.  The library underlies
   several tools developed by Kestrel researchers. See the directory
   @('[books]/kestrel/bv').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "BV-Lists library")

   (xdoc::p "A new library, @('bv-lists'), has been added. It formalizes
   notions related to lists of bit vectors from the @('bv') library, including
   packing, unpacking, and conversions between lists of bits and lists of
   bytes. See the directory @('[books]/kestrel/bv-lists').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Centaur meta-reasoning library")

   (xdoc::p "The @('centaur/meta') directory contains various new books focused
     on meta-reasoning, differing from previous efforts in their use of
     @('clause-processors/pseudo-term-fty.lisp') to treat pseudo-terms as a
     sum-of-products type.  Among other things, this directory contains an
     unconditional rewriter, a let-abstraction clause processor, and a clause
     processor that quickly removes irrelevant parts of a clause during mutual
     inductions using @('tools/flag.lisp').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "hdwallet::crypto-hdwallet"
                           "Cryptocurrency Hierarchical Deterministic Wallet"))

   (xdoc::p
    "This is a simple proof of concept of
     a hierarchical deterministic wallet for cryptocurrencies,
     which makes use of the "
    (xdoc::seetopic "crypto::cryptography" "cryptographic") ", "
    (xdoc::seetopic "bitcoin::bitcoin" "Bitcoin") ", and "
    (xdoc::seetopic "ethereum::ethereum" "Ethereum") " libraries.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "File-io-light library")

   (xdoc::p "A new library, @('file-io-light') has been added.  It aims to
   provide rules about basic input/output operations on files, while being as
   lightweight as possible.  See the directory
   @('[books]/kestrel/file-io-light').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Library-wrappers library")

   (xdoc::p "A new library, @('library-wrappers'), has been added. It contains
   books that aim to improve other libraries by including them and then
   disabling or replacing rules that may be problematic. See the directory
   @('[books]/kestrel/library-wrappers').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Lists-light library")

   (xdoc::p "A new library, @('lists-light') has been added.  It aims to
   provide basic reasoning about lists while being as lightweight as possible.  See
   the directory @('[books]/kestrel/lists-light').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Prime-fields library")

   (xdoc::p "A new library, @('prime-fields') has been added.  It contains a
   formalization of prime fields and associated operations.  A prime field is a
   finite field consisting of the integers modulo some prime. See the directory
   @('[books]/kestrel/prime-fields').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/system" "Standard System Library"))

   (xdoc::p
    "A new library for standard system utilities has been started.
     This is currently mostly under the Kestrel books,
     but it will be gradually moved directly under @('[books]/std/system').
     This new library is being populated
     with existing utilities factored out of
     some Kestrel Books with system utilities,
     as well as with some new utilities.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/testing" "Standard Testing Library"))

   (xdoc::p
    "A new library for standard testing utilities has been started.  The
     contents of the files @('[books]/misc/assert.lisp') and
     @('[books]/misc/eval.lisp') have been moved here (with the same names),
     while the two files under @('[books]/misc/') have been turned into
     relocation stubs.  The utilities in those two files have been moved to new
     individual files for greater modularity.  Some new testing utilities have
     been added to this new library as well.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/typed-alists"
                             "Standard Typed Alists Library"))

   (xdoc::p
    "A new library has been added,
     to collect recognizers and theorems for typed alists,
     i.e. alists whose keys and values have specified types.
     This is analogous to @(csee std/typed-lists).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Changes to Existing Libraries")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "abnf::abnf" "ABNF Library"))

   (xdoc::p
    "Some functions have been improved slightly.")

   (xdoc::p
    "Some theorems have been added.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "aignet" "Aignet Library"))

   (xdoc::p
    "Added @('centaur/aignet/cube-sat.lisp'), containing utilities for checking
     satisfiability using @(see satlink) of a cube of aignet literals, possibly
     after applying combinational-equivalence-preserving transformations.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "apply$" "Apply$") " Books")

; The timings discussed below were reported as follows, before and after the
; change, respectively, on Matt Kaufmann's Mac.

; 1662.81 seconds realtime, 1660.71 seconds runtime
; (234,962,012,832 bytes allocated).

; 178.47 seconds realtime, 174.30 seconds runtime
; (47,399,184,272 bytes allocated).

   (xdoc::p
    "The proof of lemma @('apply$-prim-meta-fn-correct') is much faster in the
    @('\"apply-prim\"') books in directories @('\"system/apply/\"'),
    @('\"projects/apply-model/\"'), and @('\"projects/apply-model-2/\"').  In
    particular, the time for proving that lemma in
    @('\"projects/apply-model-2/apply-prim.lisp\"') has been measured (on a
    Mac) at just under 3 minutes after the change but at 27.7 minutes before
    the change.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "apt::apt" "APT"))

   (xdoc::p
    "A new transformation, @(tsee apt::casesplit),
     has been added to rephrase a function by cases.")

   (xdoc::p
    "A new transformation, @(tsee apt::isodata),
     has been added to transform data between isomorphic representations.")

   (xdoc::p
    "@(tsee apt::parteval) now provides better support
     for recursive functions whose static arguments
     do not change across recursive calls.
     @(tsee apt::parteval) has also been extended to support "
    (xdoc::seetopic "apt::untranslate-specifier" "untranslate specifiers")
    ".")

   (xdoc::p
    "@(tsee apt::restrict) now supports reflexive functions,
     i.e. functions that occur in their termination theorem.")

   (xdoc::p
    "An input has been added to @(tsee apt::tailrec) to control whether
     the wrapper function is generated or not.")

   (xdoc::p
    "A table of APT defaults has been started.
     See @('[books]/kestrel/apt/utilities/defaults-table.lisp').")

   (xdoc::p
    "New APT-specific XDOC constructors have been added.
     Some APT-specific XDOC constructors have been extended and improved.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Arithmetic-3")

   (xdoc::p "The inclusion of @('arithmetic-3/floor-mod/mod-expt-fast') in
   @('arithmetic-3/top') has been commented out to prevent clashes with
   @('arithmetic-5').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Arithmetic-5")

   (xdoc::p "The inclusion of @('arithmetic-5/lib/floor-mod/mod-expt-fast') in
   @('arithmetic-5/lib/floor-mod/top'), which is in turn included by
   @('arithmetic-5/top'), has been commented out to prevent clashes with
   @('arithmetic-3').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "bitcoin::bitcoin" "Bitcoin Library"))

   (xdoc::p
    "Some theorems have been added.")

   (xdoc::p
    "Verified executable attachments have been added
     for some of the non-executable functions in the BIP 32 formalization.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "crypto::cryptography" "Cryptographic Library"))

   (xdoc::p
    "A " (xdoc::seetopic "ecurve::elliptic-curves" "sub-library for elliptic curves")
    " has been added,
     which currently contains all the secp256k1 domain parameters,
     and fixtypes for secp256k1 field elements, points, and keys.
     The parameters and the fixtypes that were previously part of the "
    (xdoc::seetopic "ecurve::secp256k1-interface"
                  "elliptic curve secp256k1 interface")
    " have been removed from that interface,
     which now includes the domain parameters and the fixtypes
     from the new sub-library.")

   (xdoc::p
    "A " (xdoc::seetopic "ecdsa::elliptic-curve-digital-signature-algorithm"
		       "sub-library for ECDSA")
    " (Elliptic Curve Digital Signature Algorithm)
     has been added, which now contains the secp256k1 signing interface,
     which was previously part of the "
    (xdoc::seetopic "ecurve::secp256k1-interface"
                  "elliptic curve secp256k1 interface") ".")

   (xdoc::p
    "A sub-library has been added that includes formal specifications for the
    SHA-2 hash functions: SHA-224, SHA-256, SHA-384, and SHA-512.  The new
    sub-library is in @('[books]/kestrel/crypto/sha-2/').")

   (xdoc::p
    "A " (xdoc::seetopic "keccak::keccak" "sub-library for KECCAK / SHA-3 hash functions")
     " has been added.")

   (xdoc::p
    "A sub-library has been added that includes formal specifications for
    HMAC-SHA-256 and HMAC-SHA-512, i.e., for the HMAC keyed-hash message
    authentication code, using either SHA-256 or SHA-512 as the underlying hash
    function.  The new sub-library is in @('[books]/kestrel/crypto/hmac/').")

   (xdoc::p
    "A sub-library for Password-Based Key Derivation Function 2 (PBKDF2)
     as specified by RFC 8018, and specialized to use HMAC SHA-512,
     has been added.
     See @(tsee kdf::pbkdf2-hmac-sha-512).")

   (xdoc::p
    "A sub-library has been added that includes formal specifications for
    several common padding operations used in cryptography.  The new
    sub-library is in @('[books]/kestrel/crypto/padding/').")

   (xdoc::p
    "A macro @(tsee crypto::definterface-hash) has been added
     to introduce interfaces of hash functions.")

   (xdoc::p
    "A macro @(tsee crypto::definterface-hmac) has been added
     to introduce interfaces of HMAC functions.")

   (xdoc::p
    "A macro @(tsee crypto::definterface-pbkdf2) has been added
     to introduce interfaces of PBKDF2 functions.")

   (xdoc::p
    "A macro @(tsee crypto::definterface-encrypt-block) has been added
     to introduce interfaces of block encryption/decryption functions.")

   (xdoc::p
    "A macro @(tsee crypto::definterface-encrypt-init) has been added
     to introduce interfaces of encryption/decryption functions
     that use initialization vectors
     (as in certain block cipher modes of operation).")

   (xdoc::p
    "Interfaces have been introduced (via @(tsee crypto::definterface-hash))
     for the hash functions
     Keccak-256, Keccak-512, RIPEMD-160, SHA-256, and SHA-512.
     These supersede the previously existing placeholders
     for Keccak-256, RIPEMD-160, and SHA-256, which have been removed.")

   (xdoc::p
    "Interfaces have been introduced (via @(tsee crypto::definterface-hmac))
     for the HMAC functions HMAC-SHA-256 and HMAC-SHA-512.
     These supersede the previously existing placeholder
     for HMAC-SHA-512, which has been removed.")

   (xdoc::p
    "Interfaces have been introduced (via @(tsee crypto::definterface-pbkdf2))
     for the PBKDF2 functions HMAC-SHA-256 and PBKDF2 HMAC-SHA-512.
     These supersede the previously existing placeholder
     for PBKDF2 HMAC-SHA-512, which has been removed.")

   (xdoc::p
    "Interfaces have been introduced
     (via @(tsee crypto::definterface-encrypt-block))
     for the AES-128, AES-192, and AES-256 block ciphers.")

   (xdoc::p
    "Interfaces have been introduced
     (via @(tsee crypto::definterface-encrypt-init))
     for the AES-128 CBC PKCS7, AES-192 CBC PKCS7, and AES-256 CBC PKCS7
     ciphers (CBC mode, PKCS7 padding).")

   (xdoc::p
    "The `placeholder' for elliptic curve secp256k1
     has been turned into an `interface' for elliptic curve secp256k1,
     consistently with the changes above.
     There are no more cryptographic `placeholders',
     but `interfaces' instead.
     Their structure is quite similar,
     but the nomenclature indicates a more permanent status.")

   (xdoc::p
    "The "
    (xdoc::seetopic "ecurve::secp256k1-interface"
                  "elliptic curve secp256k1 interface")
    " has been extended with an (abstract) signing operation.")

   (xdoc::p
    "Executable attachments have been added for
     the Keccak-256 interface that operates on bytes,
     the SHA-256 interface that operates on bytes,
     the HMAC-SHA-512 interface,
     the PBKDF2 HMAC-SHA-512 interface,
     the secp256k1 interface, and
     the secp256k1 ECDSA interface.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "ethereum::ethereum" "Ethereum Library"))

   (xdoc::p
    "A function to construct signed transactions has been added.")

   (xdoc::p
    "Functions to calculate an account address
     from a public key and from a private key (via its public key)
     have been added.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "event-macros" "Event Macros Library"))

   (xdoc::p
    "Utilities for applicability conditions have been added.")

   (xdoc::p
    "XDOC constructors for documenting the implementation of event macros
     have been added.")

   (xdoc::p
    "More XDOC constructors for documenting event macros at the user level
     have been added.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "fty" "Fixtype Definition Library"))

   (xdoc::p
    "The @(tsee fty::defbyte) macro has been improved
     to generate additional theorems.")

   (xdoc::p
    "The @(tsee fty::defbytelist) macro has been improved
     to generate additional theorems.")

   (xdoc::p
    "The @(tsee fty::defset) macro has been improved
     to generate additional theorems.
     It has also been extended with an option @(':elementp-of-nil'),
     similar to @(tsee std::deflist),
     which results in some better theorems when supplied.")

   (xdoc::p
    "A new macro @(tsee fty::deffixequiv-sk) has been added
     to automate the proof of @(tsee fty::deffixequiv) theorems
     for @(tsee defun-sk) (including @(tsee std::define-sk)) functions.")

   (xdoc::p
    "A new macro @(tsee fty::defflatsum) has been added
     to introduce ``flat'' (i.e. not tagged) sums of disjoint types.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "gl::gl" "GL"))

   (xdoc::p
    "Changed accumulated-persistence-style profiling so that it doesn't count
     the frames contained in nested applications of a rule multiple times
     toward that rule's frame count.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "java::java" "Java Library"))

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "java::atj" "ATJ, the Java Code Generator for ACL2"))

   (xdoc::p
    "The implementation of ATJ has been improved
     to use a more general abstract syntax and pretty-printer for Java
     (which are currently part of the implementation of ATJ),
     instead of writing directly to the output channel piecewise.
     This provides more flexibility, and the ability to have more code
     in logic mode and guard-verified.")

   (xdoc::p
    "ATJ has been extended with an option to generate Java code
     according to a shallow embedding approach,
     besides the previous deep embedding approach.")

   (xdoc::p
    "ATJ has been extended with an option to generate Java code
     under the assumption that the guards are always satisfied.
     This option should be used only with guard-verified ACL2 code
     and with external Java code that calls the generated Java code
     always with values that satisfy the guards.")

   (xdoc::p
    "ATJ has been extended with the ability to generate Java code
     that operates on narrower types than the one for all ACL2 values.
     This ability is available in the shallow embedding approach,
     when guards are assumed satisfied.")

   (xdoc::p
    "ATJ has been extended with the ability to generate Java code
     that uses Java primitive values and operations.
     This ability is available in the shallow embedding approach,
     when guards are assumed satisfied.")

   (xdoc::p
    "ATJ has been extended with the ability to generate Java code
     that uses Java primitive arrays and operations,
     and to destructively update arrays.
     This ability is available in the shallow embedding approach,
     when guards are assumed satisfied.")

   (xdoc::p
    "ATJ has been extended with the ability to generate Java loops
     from tail-recursive ACL2 functions.
     This ability is available in the shallow embedding approach,
     when guards are assumed satisfied.")

   (xdoc::p
    "A comprehensive tutorial on ATJ has been started.
     It is available at @(tsee java::atj-tutorial).")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "java::aij"
                             "AIJ, the Deep Embedding of ACL2 into Java"))

   (xdoc::p
    "The return types of some of the methods that provide
     native Java implementation of the ACL2 primitive functions
     have been made more precise than the general type @('Acl2Value').
     For instance, the method for @(tsee equal)
     now returns @('Acl2Symbol').")

   (xdoc::p
    "Some of the native Java implementations of the ACL2 primitive functions
     have been optimized.")

   (xdoc::p
    "Variant native Java implementations of the ACL2 primitive functions
     have been added that operate
     on narrower types than the one for all ACL2 values.
     These are used by ATJ-generated code that operates on narrower types
     (see release notes about ATJ).")

   (xdoc::p
    "Native Java implementations of a few more ACL2 built-in functions
     have been added.")

   (xdoc::p
    "The documentation of AIJ has been extended and improved.
     In particular, explicit preconditions have been added for public methods,
     and explicit invariants have been added for non-public fields
     and for arguments and results of non-public methods.")

   (xdoc::p
    "A number of JUnit unit tests have been added
     for some of the AIJ Java code.
     More unit tests are planned.")

   ;;;;;;;;;;;;;;;;;;;;

   (xdoc::h5 (xdoc::seetopic "java::language" "Java Language Formalization"))

   (xdoc::p
    "An ABNF grammar has been added for the whole Java language,
     consisting of the lexical and syntactic sub-grammars
     from the Java language specification.
     The grammar files have been parsed with "
    (xdoc::seetopic "abnf::grammar-parser" "the verified ABNF grammar parser")
    ", obtaining a formal representation of the grammar of Java,
     which can be used to formally specify. at a very high and assured level,
     the concrete syntax of Java.
     Various properties of the thus-obtained grammar representation (e.g. "
    (xdoc::seetopic "abnf::closure" "closure")
    ") have been proved, for validation.")

   (xdoc::p
    "A model of Java Unicode characters has been added,
     along with a model of their ASCII subset.")

   (xdoc::p
    "Models have been added
     of the null and boolean literals,
     of (non-restricted and restricted) keywords,
     and of identifiers.
     The consistency of these models with the grammar (see above)
     has been proved.")

   (xdoc::p
    "Models have been added
     of the decimal, hexadecimal, octal, and binary integer literals.
     Abstract models have been added
     of the floating-point literals.
     Models have been added
     of the character and string literals.")

   (xdoc::p
    "A model of the processing of Unicode escapes has been added.
     This is Java's first lexical translation steps.")

   (xdoc::p
    "Models have been added of all the boolean and integer operations,
     as well as of all the primitive conversions on integral values.
     Abstract models have also been added of all the floating-point operations,
     as well as of all the primitive conversions
     involving floating-point values.")

   (xdoc::p
    "A model of (opaque) pointers has been added.
     A model of reference values (consisting of pointers and a null reference)
     has been added.
     A model of all values, consisting of primitive and reference values,
     has been added.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Kestrel Utilities")

   (xdoc::p
    "Note that some of the books below are not as polished as they could be.
    Such books contain the text @('STATUS: IN-PROGRESS') near the top of the
    file.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/conjunctions') contains
     utilities for manipulating conjunctions.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/declares0') contains
     utilities for manipulating @(tsee declare)s .")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/def-constant-opener')
    contains a utility that generates an opener theorem for a function when all
    arguments are constant (this is used by Axe).")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/defopeners') contains a
    utility for making opener rules for recursive functions.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/deftest'), contains a utility,
     @('deftest') for isolating tests and running them with extensive guard
     checking.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/defthm-events') contains
    utilities for processing @(tsee defthm) forms.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/defun-events') contains
    utilities for processing @(tsee defun) forms.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/disables') disables some
    built-in functions that may be convenient to have disabled from the
    start.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/doublets2') contains
    utilities that deal with doublets (true lists of length 2).")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/equal-of-booleans'), contains
     rules to break an equality of two booleans into the equivalent conjunction
     of two implications.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/erp') contains utilities
    for returning errors (which are often assigned to a variable called @('erp').")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/forms') contains basic
    utilities about forms that look like function calls.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/keyword-value-lists2')
    contains utilities about keyword-value-lists.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/make-and') contains a
    utility to make an untranslated conjunction.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/make-and-nice') contains a
    utility to make a, possibly simplified, untranslated conjunction.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/make-or') contains a
    utility to make an untranslated disjunction.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/make-or-nice') contains a
    utility to make a, possibly simplified, untranslated disjunction.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/my-get-event') contains a utility
    to get the (untranslated) event that introduced a function.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/pack') contains utilities for
    making symbols from strings, natural numbers, characters, and other
    symbols.")

   (xdoc::p
    "A new book,
    @('[books]/kestrel/utilities/remove-duplicates-equal-dollar') contains a
    utility to remove duplicates, keeping the first of each set.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/smaller-termp'), contains
     a utility to compare the sizes of terms.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/substitution') contains
   utilities that perform substitution.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/terms') contains various
    utilities for manipulating terms.")

   (xdoc::p
    "A new book, @('[books]/kestrel/utilities/world') contains utilities
    for querying the ACL2 logical world.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "list-utilities" "Kestrel List Utilities"))

   (xdoc::p
    "A theorem about @(tsee prefixp) has been added.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "set::theorems-about-osets" "Kestrel Oset Theorems"))

   (xdoc::p
    "A theorem has been added.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Pseudo-good-world")

   (xdoc::p
    "Some functions have been factored out of the file
     @('[book]/system/pseudo-good-worldp.lisp'),
     and put into new individual files,
     for greater modularity.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "remove-hyps" "Remove-hyps utility"))

   (xdoc::p
    "Now, @(tsee remove-hyps) succeeds when applied to a call of @(tsee thm)
    whose formula is not in the form of a valid rewrite rule.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/alists" "Standard Association Lists Library"))

   (xdoc::p
    "The functions @(tsee alist-map-keys) and @(tsee alist-map-vals)
     have been moved to @('[books]/std/alists/')
     from @('[books]/kestrel/utilities/alists/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/basic" "Standard Basic Library"))

   (xdoc::p
    "The function @(tsee pos-fix),
     along with its accompanying theorems and XDOC topic,
     has been moved from @('[books]/centaur/fty/basetypes.lisp')
     to a new file @('[books]/std/basic/pos-fix.lisp').")

   (xdoc::p
    "The function @(tsee symbol-package-name-lst)
     has been moved to the Std extensions in the Kestrel Books,
     under @('[books]/kestrel/std/basic/').")

   (xdoc::p
    "The function @(tsee symbol-package-name-non-cl),
     originally called @('symbol-package-name-safe') but now renamed,
     has been moved to the Std extensions in the Kestrel Books,
     under @('[books]/kestrel/std/basic/').")

   (xdoc::p
    "The functions @(tsee organize-symbols-by-name)
     and @(tsee organize-symbols-by-pkg)
     has been moved to the Std extensions in the Kestrel Books,
     under @('[books]/kestrel/std/basic/').")

   (xdoc::p
    "A variant @(tsee mbt$) of @(tsee mbt) has been introduced,
     which requires the argument to be just non-@('nil')
     instead of exactly @('t').
     This is in the Std extensions in the Kestrel Books,
     under @('[books]/kestrel/std/basic/').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/lists" "Standard Lists Library"))

   (xdoc::p
    "A file @('union.lisp') has been added
     with theorems about @(tsee union-equal).")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "stobjs::std/stobjs" "Standard STOBJs Library"))

   (xdoc::p
    "The theorems about range equivalences in
     @('std/stobjs/updater-independence.lisp') have been somewhat improved and
     a new utility @('def-range-equiv') added to allow defining new types of
     equivalences over ranges of indices.")

   (xdoc::p
    "A new book @('std/stobjs/nicestobj.lisp') defines @('defnicestobj'), a
     utility for defining a stobj with non-interference theorems about its
     accessors and updaters in the style discussed in @(see
     stobjs::stobj-updater-independence), with accessors that apply fixing
     functions to provide unconditionally well-typed results.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/strings" "Standard Strings Library"))

   (xdoc::p
    "A variant @(tsee str::strtok!) of @(tsee str::strtok) has been added,
     which does not treat contiguous delimiters as one.
     This is under the Std extensions in the Kestrel Books.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std/typed-lists" "Standard Typed Lists Library"))

   (xdoc::p
    "A file for lists of strings and symbols has been added.
     The recognizer has been factored out of
     @('[books]/system/pseudo-good-worldp.lisp').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "std::std/util" "Standard Utilities Library"))

   (xdoc::p
    "A new book @('std/util/defret-mutual-generate') provides a utility "
    (xdoc::seetopic "std::defret-mutual-generate" "defret-mutual-generate")
    " intended for generating mutually-inductive theorems over large mutual
     recursions by applying a set of rules referencing the @(see define)
     formals and returns to determine what hypotheses to assume and conclusions
     to prove about each function in the mutual recursion.")

   (xdoc::p
    "@(csee std::defret) now substitutes the list of return value names for
     symbols named @('<VALUES>') in the body and hints.")

   (xdoc::p
    "A new macro @(tsee defarbrec) (for `define arbitrary recursion')
     has been added, to introduce recursive functions
     without having to prove termination right away.
     There exist similar macros in the community books,
     but the specifics of this new macro are motivated for use with "
    (xdoc::seetopic "apt::apt" "APT")
    ". See the `Related Tools' section
     of the documentation of @(tsee defarbrec) for more information.
     This macro is currently in the Std/util extensions in the Kestrel Books,
     but could be moved to @('[books]/std/util') at some point.")

   (xdoc::p
    "A new macro @(tsee std::deffixer) has been added
     that automates the definition of fixing functions,
     and the generation of theorems about them,
     according to a common pattern.
     The macro can be extended to cover variations in the pattern if needed.
     This can be used as a building block
     for extending @(tsee fty::deffixtype) to generate
     not only the equivalence, but also the fixer for the fixtype.
     This macro is currently in the Std/util extensions in the Kestrel Books,
     but could be moved to @('[books]/std/util') at some point.")

   (xdoc::p
    "A new macro @(tsee defiso) has been added,
     to establish isomorphic mappings by verification.")

   (xdoc::p
    "A new macro @(tsee defmax-nat) has been added,
     to introduce functions to return maxima of sets of natural numbers.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Tools")

   (xdoc::p
    "The tool @(tsee remove-hyps) no longer causes an error when the number of
     prover steps exceeds the value of @('*default-step-limit*') (which is
     @(`*default-step-limit*`)).  Thanks to Mihir Mehta for reporting this bug.
     @(tsee Remove-hyps) also avoids skipping proofs, which can lead to false
     ``theorems''.  Thanks to Stephen Westfold for reporting this issue.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 "Toothbrush")

   (xdoc::p
    "Warnings have been eliminated when creating the file
    @('books/system/toothbrush/defined-syms.lsp').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "x86isa::x86isa" "X86ISA"))

   (xdoc::p
    "The following instructions have been added to the model:")
   (xdoc::ul
    (xdoc::li "@('MOV moffs8, AL')")
    (xdoc::li "@('MOV moffs16, AX')")
    (xdoc::li "@('MOV moffs32, EAX')")
    (xdoc::li "@('MOV moffs64, RAX')")
    (xdoc::li "@('SHLD r/m16, r16, imm8')")
    (xdoc::li "@('SHLD r/m32, r32, imm8')")
    (xdoc::li "@('SHLD r/m64, r64, imm8')")
    (xdoc::li "@('SHLD r/m16, r16, CL')")
    (xdoc::li "@('SHLD r/m32, r32, CL')")
    (xdoc::li "@('SHLD r/m64, r64, CL')")
    (xdoc::li "@('SHRD r/m16, r16, imm8')")
    (xdoc::li "@('SHRD r/m32, r32, imm8')")
    (xdoc::li "@('SHRD r/m64, r64, imm8')")
    (xdoc::li "@('SHRD r/m16, r16, CL')")
    (xdoc::li "@('SHRD r/m32, r32, CL')")
    (xdoc::li "@('SHRD r/m64, r64, CL')"))

   (xdoc::p
    "The @('def-inst') macro has been extended
     to generate more boilerplate code.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h4 (xdoc::seetopic "xdoc" "XDOC"))

   (xdoc::p
    "A new generic composite constructor has been added,
     namely @(tsee xdoc::ahref).")

   (xdoc::p
    "The generic composite constructor @('xdoc::seeurl')
     has been renmed to @(tsee xdoc::seetopic).
     The previous name is still temporarily available as a synonym,
     for compatibility with existing uses.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Licensing Changes")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Build System Updates")

   (xdoc::p
    "The `@('basic')' target in @('GNUmakefile') now certifies
     @('projects/apply/top.lisp'), as is necessary for using @(tsee defun$) or
     @(tsee defwarrant).")

   (xdoc::p
    "Modified custom makefiles @('books/projects/apply-model/Makefile') and
     @('books/projects/apply-model-2/Makefile') to avoid apparent mishandling of
     dependency analysis.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Testing")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Miscellaneous")

   (xdoc::p
    "Some @(see xdoc) string processing has been made a bit more efficient.")

   (xdoc::p
    "It was possible for some web-based @(see xdoc) manual pages to be
     mysteriously empty due to control characters in the source documentation.
     It is now checked before saving a web-based manual that the :short
     and :long strings, when supplied, consist solely of standard
     characters (see @(see standard-char-p)), except that tabs are also
     permitted.")

   (xdoc::p
    "Supporting materials for ACL2 Workshop 2020 have been added.  They are in
    directory @('workshops/2020/'); see the @('README') file there.")

   ))

(defxdoc note-8-2-books

; Please add information about your library in the appropriate
; category below --- the category title is enclosed in <h3>..</h3>
; tags (of course, feel free to add a new category if needed).  To
; ensure consistency with the style of previous book release doc
; topics, please follow the following convention:

;  <h4>Your Library Title</h4>
;  <p>Details go here.</p>

; If you are stuck, see comments in previous (defxdoc note-xxx-books ...).

  :parents (note-8-2 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 8.2"

  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 8.1 and 8.2.</p>

 <p>See also @(see note-8-2) for the changes made to ACL2 itself.  For
 additional details, you may also see the raw <a
 href='https://github.com/acl2/acl2/commits/master'>commit log</a>.</p>

 <h3>New Libraries</h3>

 <h4>Kestrel Alist Utilities</h4>

 <p>Added an operation @(tsee remove-assocs), which generalizes @(tsee
 remove-assoc) from single keys to lists of keys.</p>

 <h4><see topic='@(url crypto::cryptography)'>Cryptography</see></h4>

 <p>Started a library with placeholders for cryptographic functions that will
 be eventually replaced with complete specifications of those functions.</p>

 <h4>Declarative Definitions of Maxima</h4>

 <p>Added a macro @(tsee defmax-nat) to declaratively define the maximum of a
 set of natural numbers.</p>

 <h4><see topic='@(url event-macros)'>Event Macros</see></h4>

 <p>Started a library of concepts and utilities to develop event
 macros (i.e. macros at the event level) more quickly and consistently.</p>

 <p>This library includes some XDOC constructor utilities for the reference
 documentation of event macros.</p>

 <p>This library also includes functions to process inputs common to multiple
 event macros.</p>

 <h4>Graphviz</h4>

 <p>Added a book @('[books]/centaur/misc/graphviz.lisp') defining a syntax tree
 for the Graphviz @('.dot') file syntax and a printer for that syntax.</p>

 <h4><see topic='@(url irv::instant-runoff-voting)'>Instant Run-Off Voting</see></h4>

 <p>Formalized an instant run-off voting scheme and proved that it
 meets certain fairness criteria.</p>

 <h4>Integer Arithmetic</h4>

 <p>A library for integer arithmetic has been added at
 @('[books]/kestrel/utilities/integer-arithmetic').</p>

 <h4><see topic='@(url java::java)'>Java</see></h4>

 <p>Added a library for Java-related formalizations and tools, including:</p>

 <ul>

 <li><see topic='@(url java::aij)'>AIJ (<b>A</b>CL2 <b>I</b>n
 <b>J</b>ava)</see>, a deep embedding in Java of an executable,
 side-effect-free, non-stobj-accessing subset of the ACL2 language without
 guards.</li>

 <li><see topic='@(url java::atj)'>ATJ (<b>A</b>CL2 <b>T</b>o
 <b>J</b>ava)</see>, a simple Java code generator that turns ACL2 functions
 into AIJ representations that are evaluated by the AIJ interpreter.</li>

 <li>A <see topic='@(url java::language)'>formalization</see> in ACL2 of some
 aspects of the Java language.</li>

 </ul>

 <h4><see topic='@(url omap::omaps)'>Omaps</see></h4>

 <p>Added a library for omaps (ordered maps), analogous to @(csee
 std/osets).</p>

 <h3>Changes to Existing Libraries</h3>

 <h4><see topic='@(url aignet::aignet)'>Aignet library</see></h4>

 <p>Improved the @(see aignet::constprop) transform so that it canonicalizes
 inputs known to be equivalent or opposite to each other, not just to
 constants.  Added @(see aignet::obs-constprop) that combines this
 with the existing observability transform, which works better than running
 the two transforms separately.</p>

 <h4><see topic='@(url apt::apt)'>APT</see></h4>

 <p>Slightly extended the applicability of the @(tsee apt::tailrec)
 transformation, by relaxing a requirement on the function to be
 transformed.</p>

 <p>Improved and extended some documentation.</p>

 <p>Added some XDOC constructor utilities tailored to APT transformations.</p>

 <h4><see topic='@(url bitcoin::bitcoin)'>Bitcoin</see></h4>

 <p>Replaced uses of @(tsee ubyte8) and @(tsee ubyte8-list) with @(tsee byte)
 and @(tsee byte-list).</p>

 <p>Moved the previous placeholders for cryptographic functions into <see
 topic='@(url crypto::cryptography)'>a new library</see>.</p>

 <p>Added a formalization of BIPs (Bitcoin Improvement Proposal) 32, 39, 43,
 and 44 for hierarchical deterministic wallets.</p>

 <p>Improved the existing documentation.</p>

 <h4>Bytes</h4>

 <p>Added fixers @(tsee unsigned-byte-fix), @(tsee signed-byte-fix), @(tsee
 unsigned-byte-list-fix), and @(tsee signed-byte-list-fix) for @(tsee
 unsigned-byte-p), @(tsee signed-byte-p), @(tsee unsigned-byte-listp), and
 @(tsee signed-byte-listp).</p>

 <h4><see topic='@(url std::define)'>Define</see></h4>

 <p>Added support for configuration objects that can be used to specify some
 extended options.  Also added support for @(':verify-guards :after-returns')
 that indicates that guards are to be verified after the returns
 specifiers.</p>

 <h4><see topic='@(url rstobj::defrstobj)'>Defrstobj</see></h4>

 <p>Added support for defining universal accessor and updater functions.</p>

 <h4>Digits in Arbitrary Bases</h4>

 <p>The files @('[books]/kestrel/utilities/digits-any-base*.lisp') have been
 moved to a new subdirectory @('[books]/kestrel/utilities/digits-any-base/')
 and renamed.  Some files have been refactored into smaller files.</p>

 <p>Some theorems have been added.</p>

 <p>Added operations to group digits in a smaller base into digits in a larger
 base, and vice versa, in both big-endian and little-endian.</p>

 <p>The macro to generate additional return types for conversions from natural
 numbers to digits has been generalized and renamed.</p>

 <p>A macro @(tsee defdigits) has been added, to generate specialized versions
 of the conversion operations, and some theorems about them, for specific bases
 and specific recognizers and fixers of (lists of) digits.  Used this macro for
 some library fixtypes (e.g. bits and bytes as digits in base 2 and 256
 respectively).</p>

 <p>A macro @(tsee defdigit-grouping) has been added, to generate specialized
 versions of the digit grouping functions, and some theorems about them, for
 specific pair of bases such that the larger base is a positive power, greater
 than 1, of the smaller base.  Used this macro for some library fixtypes
 (e.g. to convert between bits and bytes).</p>

 <h4><see topic='@(url error-checking)'>Error-Checking Utilities</see></h4>

 <p>Added more error-checking functions.</p>

 <p>The files @('[books]/kestrel/utilities/error-checking*.lisp') have been
 moved to a new subdirectory @('[books]/kestrel/utilities/error-checking/')
 and renamed.  Some files have been refactored into smaller files.</p>

 <h4><see topic='@(url ethereum::ethereum)'>Ethereum</see></h4>

 <p>Replaced uses of @(tsee ubyte8), @(tsee ubyte8-list), @(tsee ubyte4), and
 @(tsee ubyte4-list) with @(tsee byte), @(tsee byte-list), @(tsee nibble), and
 @(tsee nibble-list).</p>

 <p>Modified the formalizations of RLP encoding and decoding to return an
 explicit error flag.  Added theorems showing that RLP encodings are decodable:
 RLP encoding is injective, and no valid encoding is a strict prefix of another
 one.  Added executable RLP decoders and proved them correct with respect to
 the ones declaratively defined as inverses of the RLP encoders.  Added the RLP
 tests from the Ethereum Wiki's page on RLP.</p>

 <p>Added a formalization of hex-prefix decoding, declaratively defined as the
 inverse of hex-prefix encoding.</p>

 <p>Added a formalization of Modified Merkle Patricia trees.</p>

 <p>Added a formalization of the database that underlies Modified Merkle
 Patricia trees.  This database is a finite map from Keccak-256
 hashes (i.e. byte arrays of length 32) to byte arrays.</p>

 <p>Added a formalization of the format of transactions and of their RLP
 encoding and decoding.</p>

 <p>Added several other theorems.  Improved some existing theorems.</p>

 <p>Improved some documentation.</p>

 <p>Moved the previous placeholders for cryptographic functions into <see
 topic='@(url crypto::cryptography)'>a new library</see>.</p>

 <h4>Filesystem Books</h4>

 <p>The filesystem books @('[books]/projects/filesystems/') have been
 substantially expanded; in particular, they now contain a new model which
 faithfully represents the state of a FAT32 disk image. More details about this
 work are available in the paper <i>Formalising Filesystems in the ACL2 Theorem
 Prover: an Application to FAT32</i>, to appear in the proceedings of
 ACL2-2018.</p>

 <p>Recent improvements to the filesystem books include proofs of correctness of
 filesystem representation transformations in terms of invertibility, and an
 expanded set of POSIX system calls verified through refinement.</p>

 <h4>FTY Type Definition Library</h4>

 <p>Added an option @(':non-emptyp') to @('fty::deflist') and @('std::deflist')
 to define list types that must contain at least one element.</p>

 <p>Added a book @('[books]/centaur/fty/typegraph.lisp') containing a utility that
 writes a Graphviz @('.dot') file showing an FTY type hierarchy.</p>

 <p>Added a book @('[books]/clause-processors/pseudo-term-fty') that supports
 for treating pseudo-terms as an FTY sum-of-products type; see @(see
 pseudo-term-fty).</p>

 <p>Collected several <see topic='@(url fty::fty-extensions)'>FTY
 extensions</see> under the <see topic='@(url acl2::kestrel-books)'>Kestrel
 Books</see>:</p>

 <ul>

 <li>A new macro @(tsee fty::deflist-of-len) that generates fixtypes for lists
 of specified lengths, based on existing fixtypes of lists of arbitrary
 lenghts (introduced via @(tsee fty::deflist)).</li>

 <li>A new macro @(tsee fty::defset) that generates fixtypes for @(csee
 std/osets) with elements of specified fixtypes.  This is analogous to @(tsee
 fty::deflist) and @(tsee fty::defalist).</li>

 <li>A new macro @(tsee fty::defomap) that generates fixtypes for <see
 topic='@(url omap::omaps)'>omaps</see> with keys and values of specified
 fixtypes.  This is analogous to @(tsee fty::deflist) and @(tsee
 fty::defalist).</li>

 <li>The @('acl2::defbyte') macro, which generated fixtypes and additional
 theorems for both bytes and lists of bytes, has been split into two macros
 @(tsee fty::defbyte), which generates a fixtype and some additional theorems
 for bytes, and @(tsee fty::defbytelist), which generates a fixtype and some
 additional theorems for lists of byte.</li>

 <li>A new macro @(tsee fty::deffixtype-alias) to introduce an ``alias'' of an
 existing fixtype, as well as of its recognizer, fixer, and equivalence.</li>

 <li>An existing fixtype @(tsee omap::map) for <see topic='@(url
 omap::omaps)'>omaps</see> with keys and values of any types.</li>

 <li>An existing fixtype @(tsee set::set) for @(csee std/osets) with elements
 of any types.</li>

 <li>An existing fixtype @(tsee nati) for natural numbers and infinity.</li>

 <li>New fixtypes @(tsee byte), @(tsee byte-list), @(tsee byte-list20), @(tsee
 byte-list32), and @(tsee byte-list64) for (unsigned 8-bit) bytes, true lists
 of bytes, and true lists of 20, 32, and 64 bytes.</li>

 <li>New fixtypes @(tsee nibble) and @(tsee nibble-list) for (unsigned 4-bit)
 nibbles and true lists of nibbles.</li>

 <li>A new fixtype @(tsee bit-list) for true lists of bits.</li>

 <li>Existing fixtypes @('ubyteN'), @('sbyteN'), @('ubyteN-list'), and
 @('sbyteN-list') for standard(ly named) fixtypes for unsigned or signed (true
 lists of) bytes of various sizes.</li>

 </ul>

 <h4><see topic='@(url ipasir::ipasir)'>Ipasir library</see></h4>

 <p>Used new ACL2 system features to fix the remaining known soundness bug and
 remove a trust tag.</p>

 <h4><see topic='@(url list-utilities)'>List Utilities</see></h4>

 <p>Added some theorems about functions on lists.</p>

 <h4>Profiling</h4>

 <p>Attempts to run @(tsee profile-acl2) or @(tsee profile-all) had failed, for
 ACL2 built on SBCL, with an obscure SBCL error message.  Now, the error
 message gives instructions for how to avoid the error by rebuilding SBCL from
 sources after doing a specified edit.  Thanks to Stas Boukarev for pointing to
 the appropriate SBCL source code line.</p>

 <h4>Quadratic Reciprocity</h4>

 <p>In @('projects/quadratic-reciprocity/'), certain include-books, namely
 those that bring in books from @('support/'), have been made local.  This follows
 the standard pattern of putting all proof work in separate \"support books\"
 which are included only locally in the main files.  (The main files simply
 re-iterate, redundantly, the events to be exported.)  If this change causes
 proof failures, and your development includes books such as
 @('projects/quadratic-reciprocity/fermat'), consider now also including the
 corresponding support books (e.g.,
 @('projects/quadratic-reciprocity/support/fermat')).  (Actually, to get
 broken proofs working again, it may suffice to include simpler books that were
 previously brought in via the support books, such as
 @('rtl/rel11/support/basic') or @('rtl/rel11/support/util').)</p>

 <h4>RAC: Restricted Algorithmic C</h4>

 <p>Minor modifications of @('projects/rac/') include a bug fix in the parser
 and a rewrite of @('examples/hello.cpp')
 (hat-tip to D. Hardin).</p>

 <h4>@(csee rtl)</h4>

 <p>A number of new lemmas have been added to @('rtl/rel11/lib/'), which were
 required in the verification of an Arm FPU currently under development.  This
 in turn required some minor modifications of @('projects/arm/*/').</p>

 <h4><see topic='@(url soft::soft)'>SOFT</see></h4>

 <p>The @(tsee soft::defun2), @(tsee soft::defchoose2), @(tsee
 soft::defun-sk2), and @(tsee soft::defun-inst) macros no longer include an
 explicit list of function parameters.  The function is implicitly
 parameterized over the function variables that it depends on.</p>

 <h4>@(csee std/alists)</h4>

 <p>Added a function @(tsee remove-assocs), moved from
 @('[books]/kestrel/utilities/').</p>

 <p>Added some theorems about @(tsee remove-assoc-equal), moved from
 @('[books]/kestrel/utilities/').</p>

 <h4>@(csee std/basic)</h4>

 <p>Added a recognizer @(tsee bytep) for ``standard'' (i.e. unsigned 8-bit)
 bytes, moved from @(csee std/io).</p>

 <p>Added a recognizer @(tsee nibblep) for ``standard'' (i.e. unsigned 4-bit)
 nibbles, moved from
 @('[books]/projects/oracle/stv-invariant-extraction-pitfall/alu.lisp').</p>

 <h4>@(csee std/io)</h4>

 <p>Added new lemmas to the <see topic='@(url combine-functions)'>Std/io
 byte-combining libraries</see>.</p>

 <p>Factored out the @(tsee bytep) predicate into a new file under @(csee
 std/basic).</p>

 <h4>@(csee std/lists)</h4>

 <p>The definition of function @(see list-fix) from
 @('\"books/std/lists/list-fix.lisp\"') has been incorporated into the ACL2
 sources in a way that minimizes changes to existing books.  See @(see
 note-8-2) for details.</p>

 <p>The built-in function @(tsee take) has been redefined exactly along the
 lines suggested by the theorem @('take-redefinition') that was previously
 introduced in @('\"books/std/lists/take.lisp\"').  This theorem has been now
 removed.  See @(see note-8-2) for details.</p>

 <h4>@(csee std/util)</h4>

 <p>Added macros @(tsee std::defthm-natp), @(tsee std::defthm-unsigned-byte-p),
 and @(tsee std::defthm-signed-byte-p), from the X86ISA model.</p>

 <h4><see topic='@(url string-utilities)'>String Utilities</see></h4>

 <p>Added new lemmas and generalized and improved some existing lemmas.</p>

 <p>Redefined more compactly the predicates in
 @('[books]/kestrel/utilities/string/char-kinds.lisp') via @(tsee
 str::defcharset).  Added a new predicate.</p>

 <p>Added functions @(tsee hexchars=>ubyte8) and @(tsee ubyte8=>hexchars) to
 convert between single bytes and pairs of hexadecimal digit characters;
 rephrased @(tsee ubyte8s=>hexchars) in terms of @(tsee ubyte8=>hexchars).
 Added functions @(tsee hexchars=>ubyte8s) and @(tsee hexstring=>ubyte8s),
 inverses of @(tsee ubyte8s=>hexchars) and @(tsee ubyte8s=>hexstring).</p>

 <h4>System Utilities</h4>

 <p>The new utility @(tsee sublis-expr+) replaces terms by variables even
 inside @('lambda') (@('let')) bodies.</p>

 <p>Several files @('[books]/kestrel/utilities/*.lisp') that contain system
 utilities have been moved to the subdirectory
 @('[books]/kestrel/utilities/system/').</p>

 <p>The utility, @(tsee directed-untranslate), has been improved in several
 ways, including more complete handling of @(tsee mv-let), @(tsee let*), @(tsee
 b*), @(tsee progn$), @(tsee er), @(tsee cw), and @(tsee mbe).</p>

 <p>For the event macro @(tsee orelse*), the default for the @(':expansion?p')
 argument has been changed from @('nil') to @('t'), for consistency with @(tsee
 orelse).</p>

 <p>Added utilities @(tsee macro-keyword-args) and @(tsee macro-keyword-args+)
 to retrieve an alist of the keyword arguments of a macro, associated to their
 default values.</p>

 <p>The file @('kestrel/utilities/system/event-forms.lisp') has been split,
 with material on lists of event forms put into the new file
 @('kestrel/utilities/system/event-form-lists.lisp').  When @('event-forms') is
 included, @(tsee std::deflist) is now no longer brought in, so
 @('std/util/deflist') may now need to be explicitly included in more
 places.</p>

 <h4><see topic='@(url use-termhint)'>Termhint utility</see></h4>

 <p>The @('use-termhint') utility has been moved to its own book
 @('std/util/termhints') from its former location at
 @('clause-processors/use-by-hint').</p>

 <p>Added a new utility, @(see function-termhint), for creating termhints from
 existing function definitions containing @(see hintcontext) annotations.</p>

 <h4>Typed List Utilities</h4>

 <p>Refactored the old file
 @('[books]/kestrel/utilities/typed-list-theorems.lisp') into separate files
 under a new directory @('[books]/kestrel/utilities/typed-lists').</p>

 <p>Added a recognizer @(tsee bit-listp) for true lists of bits, and associated
 theorems.</p>

 <h4><see topic='@(url x86isa)'>X86ISA</see></h4>

 <p>Finished adding support for 32-bit application-level execution for all the
 instructions, including the floating-point ones, supported by the model.</p>

 <p>Added support for enabling/disabling machine features that depend on CPUID
 flags.</p>

 <p>Detection of many decode-time exceptions is now done during opcode
 dispatch, as opposed to inside the instruction semantic functions.  This not
 only lets us catch exceptions early, but also allows us to specify them
 even if the semantic functions themselves are missing.</p>

 <p>Improved incrementing and decrementing of the stack pointer to be modular:
 64, 32, or 16 bits, based on the current mode and on the SS.B bit of the
 current stack segment.</p>

 <p>Modified the logical definitions of the x86 state (i.e., the abstract
 stobj).  Now, the x86 state accessor functions unconditionally return
 well-formed values and the x86 state updater functions return a well-formed
 state, provided that the initial state was well-formed; thus, constraints on
 the index (in case of array fields) and value being written have been
 eliminated.</p>

 <p>Improved the @('defthm-natp'), @('defthm-usb'), and @('defthm-sb')
 utilities to generate minimal and reliable hints for corollaries.  Improved
 the @('defthm-natp') utility to also generate a rewrite rule.  Extended
 @('defthm-natp') with the ability to turn on/off the generation of the type
 and linear corollaries, to modify their hypotheses, to supply more specific
 hints for the corollaries, and to specify @(':otf-flg'); these options are
 like the ones provided by @('defthm-usb') and @('defthm-sb').  Improved the
 @('defthm-usb') utility to also generate a linear linear saying that the value
 is greater than or equal to 0.  Renamed @('defthm-usb') and @('defthm-sb') to
 @('defthm-unsigned-byte-p') and @('defthm-signed-byte-p'), for consistency
 with @('defthm-natp').  Moved all three utilities to @(csee std/util).</p>

 <p>Extended top-level memory reading functions to take into account the R bit
 of code segment descriptors, when they access for reading (not execution) a
 code segment in 32-bit mode: in this case, if R = 0, the code segment is
 execute-only and thus reading data from it is not allowed.  Extended top-level
 memory functions to take into account the W bit of data segment descriptors,
 in 32-bit mode: if W = 0, the data segment is read-only and thus writing data
 to it is not allowed; writing to a code segment is not allowed either.</p>

 <p>Opcode maps are now represented using @(see fty::defprod)s, which makes it
 easier to operate on them in order to automatically generate dispatch
 functions and documentation, and to precompute some kinds of decoding
 information.</p>

 <p>Extended effective-to-linear address translation to check that the visible
 part of the DS, ES, FS, and GS segment registers does not contain a null
 segment selector.  A similar check on CS and SS is not needed because a null
 segment selector cannot be loaded into these two segment registers.</p>

 <p>Improved the `PUSH segment register' instruction to handle a 32-bit operand
 size as in modern processors: instead of zero-extending the 16-bit content of
 the segment register to 32 bits, now the model writes the low 16 bits, leaving
 the high 16 bits unchanged.</p>

 <p>Extended @(tsee x86isa::select-operand-size) to accommodate instructions
 that do not follow the ``normal'' rules.  The extended function has additional
 parameters, whose different values trigger the use of the non-``normal''
 rules.  Now many more instructions use this function, avoiding repeated blocks
 of identical codes in their semantic functions.</p>

 <p>Improved and extended some documentation.</p>

 <h4>XDOC Utilities</h4>

 <p>Improved the <see topic='@(url xdoc::constructors)'>XDOC constructors</see>
 to use a tree representation that is converted into a flat string only at the
 top level.  This enforces a better type discipline and facilitates future
 optimizations if needed.</p>

 <p>Introduced several additional constructors.</p>

 <p>Extended the documentation of the constructors.</p>

 <p>Moved the constructors to @('[books]/xdoc/constructors.lisp').</p>

 <h3>Licensing Changes</h3>

 <h3>Build System Updates</h3>

 <p>Added a feature to @('books/GNUMakefile') that allows books to specify
 dependencies on cert ACL2 system features, so that they will be automatically
 be recertified when such features are changed.  See @(see
 build::acl2-system-feature-dependencies).</p>

 <p>Added utilities @(see ifdef-define) and @(see ifdef-undefine) in
 @('books/build/ifdef.lisp') which set or unset environment variables while
 allowing the build system to correctly track them for its support of @(see
 ifdef) and @(see ifndef).</p>

 <p>Cleaned up the Perl scripts implementing <see topic='@(url build::cert.pl)'>cert.pl</see>,
 factoring them into several supporting libraries.</p>

 <h3>Testing</h3>

 <h3>Miscellaneous</h3>

 <p>We now avoid causing an error when building the manual in the case that the
 @('zip') program is not installed; that causes a warning instead.</p>

 ")

(defxdoc note-8-1-books

; Please add information about your library in the appropriate
; category below --- the category title is enclosed in <h3>..</h3>
; tags (of course, feel free to add a new category if needed).  To
; ensure consistency with the style of previous book release doc
; topics, please follow the following convention:

;  <h4>Your Library Title</h4>
;  <p>Details go here.</p>

; See also comments in (defxdoc note-8-0-books ...).

; Too trivial to mention in the xdoc string below:

; - Added a check in defopener -- actually, in supporting function
;   simplify-with-prover in books/misc/bash.lisp -- that :hints is indeed an
;   alist, to avoid an ugly raw Lisp error when that's not the case.

  :parents (note-8-1 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 8.1"

  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 8.0 and 8.1.</p>

 <p>See also @(see note-8-1) for the changes made to ACL2 itself.  For
 additional details, you may also see the raw <a
 href='https://github.com/acl2/acl2/commits/master'>commit log</a>.</p>

 <h3>New Libraries</h3>

 <p>A new regular expression library, @(see acre::acre), is available in
 @('books/centaur/acre/').  Compared to the implementation in
 @('projects/regex'), this version's features are less similar to GNU grep and
 somewhat more similar to Perl regular expressions.  However, it does not aim
 to be fully compatible, but to have a well-defined set of features with clean
 code that can be easily extended and behaves predictably (as much as possible,
 for regular expressions).</p>

 <p>Added PLTP(A), The Pure Lisp Theorem Prover, reimplemented in ACL2.  An
 ACL2 reconstruction of the 1973 Pure Lisp Theorem Prover (PLTP), the original
 ``Boyer-Moore theorem prover'' after which both NQTHM and ACL2 were modeled,
 is available in @('books/projects/pltpa/pltpa.lisp').  More importantly, a <a
 href='http://www.cs.utexas.edu/users/moore/best-ideas/pltp/index.html'>PLTP
 archive</a> has been set up.  That archive includes much original source
 material (e.g., scanned images of the 1973 POP-2 implementation of PLTP) as
 well as an extensive discussion of the differences between PLTP and PLTP(A),
 and an OCaml version of PLTP, named PLTA(O), by Grant Passmore.</p>

 <p>A new directory, @('books/projects/arm/'), contains proofs of correctness
 of the Floating-point operations of addition, multiplication, fused
 multiply-add, division, and square root, as implemented in the FPU of an Arm
 Cortex-A class high-end processor.</p>

 <p>Added utility @(see include-book-paths) to list paths via @(tsee
 include-book) down to a given book, which may be useful for reducing book
 dependencies.</p>

 <p>Added utility @(see apply-fn-if-known) to apply a function that might not
 exist; even the package for the function symbol might not exist.</p>

 <p>Added a fixer @(tsee integer-range-fix) for @(tsee integer-range-p), as
 well as a recognizer @(tsee integer-range-listp) and and a fixer @(tsee
 integer-range-list-fix) for true lists of @(tsee integer-range-p), all with
 accompanying theorems.</p>

 <p>Added a <see topic='@(url digits-any-base)'>library</see> to convert
 between natural numbers and their representations as lists of digits in
 arbitrary bases in big-endian and little-endian order.  Digits are natural
 numbers below the base.  There are variants for minimum-length,
 non-zero-minimum-length, and specified-length lists of digits.  The library
 includes, among others, theorems stating that the number-to-digits and
 digits-to-number conversions are mutual inverses in a suitable sense.</p>

 <p>Added a new utility, @(tsee skip-in-book), that wraps around a form to
 prevent its evaluation during book certification or inclusion.</p>

 <p>The new utility @(tsee defthm<w) will attempt to prove a theorem directly
 from previously-proved theorems.  It does this by generating suitable @(see
 hints) using the new utility, @(see previous-subsumer-hints).</p>

 <p>Added some utilities for building XDOC documentation.  The <see
 topic='@(url xdoc::constructors)'>XDOC constructors</see> are utilities to
 construct well-tagged XDOC strings via ACL2 function calls whose nesting
 structure mirrors the nesting of the XML.  @(tsee defxdoc+) extends @(tsee
 defxdoc) with additional conveniences.</p>

 <p>A new event, @(tsee defunt), is a variant of @(tsee defun) that uses
 termination theorems from a large set of @(see community-books) &mdash;
 namely, all books included in @('books/doc/top.lisp'), which is the book that
 creates the ACL2+Books manual &mdash; to generate termination proofs
 automatically.  Those proofs use @(':')@(tsee termination-theorem) @(see
 lemma-instance)s that reference @('defun') events in those included books.
 Several new supporting utilities are documented: @(tsee fms!-lst), which
 writes a list to a character output channel; @(tsee injections), which lists
 all maps from a domain to a range; @(tsee strict-merge-sort-<), which sorts without
 duplicates; and @(tsee subsetp-eq-linear), which is a linear-time subset test
 for sorted lists of symbols.</p>

 <p>Added a new macro @('defbyte') for introducing fixtypes for unsigned and
 signed bytes of specified sizes, as well as fixtypes of lists of such bytes,
 along with theorems relating the fixtype recognizers to the built-in binary
 predicates @(tsee unsigned-byte-p) and @(tsee signed-byte-p) and to the
 library binary predicates @(tsee unsigned-byte-listp) and @(tsee
 signed-byte-listp).</p>

 <p>Started a new library for <a href=\"https://ethereum.org\">Ethereum</a>.</p>

 <p>Started a new library for <a href=\"https://bitcoin.org\">Bitcoin</a>.</p>

 <p>A new book, @('clause-processors/bindinglist.lisp'), supports a meta-level
 structure for a list of bindings of variables to values, with functions that
 convert these to and from nests of lambdas and proofs that establish these
 functions' semantics with respect to an evaluator.</p>

 <h3>Changes to Existing Libraries</h3>

 <p>The behavior and code for the expander (see @(see defthm?)) have been
 improved in a few ways (some of them technical), as follows.</p>

 <ul>

 <li>A bug has been fixed that was preventing @(see hints) from being passed to
 the forcing round (if any).  An example may be found in the new book,
 @('misc/expander-tests.lisp').</li>

 <li>The deprecated @(tsee fmt) directives @('~p') and @('~q') have been
 replaced by @('~x') and @('~y'), respectively.</li>

 <li>Error messages have been improved for the function @('simplify-hyps') when
 there is a contradiction.</li>

 <li>The @(see state) globals @('tool2-result') and @('tool2-error') are no
 longer set.  (They appear to have been unused.)</li>

 <li>The functions @('tool2-fn'), @('tool2-fn-lst'), and @('simplify-hyps') now
 have a new final argument, @('ctx').  Also, the macro @('tool2') now has a
 @(':ctx') keyword argument.</li>

 </ul>

 <p>Updated the ACL2+books manual to accommodate the replacement of David
 Russinoff's online rtl manual by his upcoming Springer book.</p>

 <p>Improved @(tsee install-not-normalized) to handle cases in which
 recursively-defined functions have non-recursive normalized definitions.</p>

 <p>The @('misc/assert.lisp') book no longer includes @('misc/eval.lisp'),
 since tests about the @('misc/assert.lisp') utilities are now in a separate
 book @('misc/assert-tests.lisp').</p>

 <p>The @('misc/eval.lisp') utilities @(tsee ensure-error), @(tsee
 ensure-soft-error), @(tsee ensure-hard-error), @(tsee thm?), and @(tsee
 not-thm?)  have been renamed to @(tsee must-fail-with-error), @(tsee
 must-fail-with-soft-error), @(tsee must-fail-with-hard-error), @(tsee
 must-prove), and @(tsee must-not-prove).  The old names are still available as
 deprecated synonyms, which will be removed in one of the next releases.</p>

 <p>The old directory @('books/projects/masc/') has been replaced by the bew
 directory@('books/projects/rac/').  The reason is that our RTL modeling
 language now uses the register class templates of Algorithm C instead of those
 of SystemC, so the name <i>Modeling Algorithms in SystemC</i> now makes even
 less sense than it did; the best we could come up with as a replacement is
 <i>Restricted Algorithmic C</i>. </p>

 <p>The utility @(tsee make-flag) has a new keyword argument, @(':last-body'),
 to specify using the most recent @(see definition) rule for a function symbol
 instead of its original definition.</p>

 <p>Extended and simplified the <see topic='@(url
 defun-sk-queries)'>@('defun-sk') query utilities</see>.  The utilities now
 handle the recently introduced @(':constrain') option.  The utilities no
 longer build a record with all the information about the @(tsee defun-sk)
 function (whose fields can then be accessed); instead, now the utilities
 retrieve the various pieces of information directly.</p>

 <p>Extended the <see topic='@(url defchoose-queries)'>@('defchoose') query
 utilities</see> with a recognizer for symbols that name @(tsee defchoose)
 functions.</p>

 <p>Made several improvements to @(tsee directed-untranslate), including: avoid
 assertion errors that could occur when using @(tsee declare) forms with @(tsee
 let), @(tsee let*), or @(tsee mv-let) expressions: enhance insertion of
 appropriate @(tsee mv) calls; extend dropping of unused @(tsee let) bindings;
 avoid an assertion error with @('mv-let') expressions; and preserve basic uses
 of @(tsee b*).</p>

 <p>Removed the @('keywords-of-keyword-value-list') utility, because it is
 subsumed by the built-in @(tsee evens) utility.</p>

 <p>Extended the <see topic='@(url error-checking)'>error-checking
 utilities</see> with several error-checking functions.</p>

 <p>Extended the Kestrel world query utilities with functions to collect the
 names of all the known packages in the ACL2 @(see world) and to check if a
 function is primitive.</p>

 <p>Extended the <see topic='@(url std/system/term-function-recognizers)'>term
 function recognizers</see> with recognizers for true lists of
 (pseudo-)lambda-expressions and (pseudo-)term-functions.</p>

 <p>Extended the Kestrel term utilities with operations to substitute function
 symbols without performing simplification, to construct terms that are
 functions applications of certain forms, to collect all the lambda expressions
 in terms, and to collect all the package names in (symbols in) terms.</p>

 <p>The utility @(tsee install-not-normalized-event) now includes option
 @(':allp nil') in the generated @(tsee install-not-normalized) event.  The new
 utility, @(tsee install-not-normalized-event-lst), can thus handle @(tsee
 mutual-recursion) nicely, e.g.: @('(install-not-normalized-event-lst (getpropc
 'f1 'recursivep nil) nil nil (w state))').  Also, added new utility @(tsee
 install-not-normalized$) to submit the event generated by @(tsee
 install-not-normalized-event).</p>

 <p>Extended the <see topic='@(url set::oset-utilities)'>oset utilities</see>
 with a <see topic='@(url fty)'>fixtype</see> for osets.</p>

 <p>Added some <see topic='@(url nat-list-fix-theorems)'>theorems about lists
 of natural numbers</see>.</p>

 <p>Added a theorem about lists of strings.</p>

 <p>Merged the utilities in @('[books]/kestrel/utilities/characters.lisp') into
 the <see topic='@(url string-utilities)'>string utilities</see>.  Extended the
 combined utilities with some theorems about the pre-existing functions and
 with new functions to check if (lists of) characters are all of specified
 kinds, to convert a list of unsigned 8-bit bytes to a corresponding list or
 string of hex digit characters.  Refactored all the old and new utilities into
 separate files to reduce dependencies.</p>

 <p>Extended the Kestrel symbol utilities with a utility that lifts @(tsee
 symbol-package-name) to lists.</p>

 <p>Moved @(tsee maybe-msgp) under newly created <see topic='@(url
 message-utilities)'>message utilities</see>.  Extended these utilities with a
 recognizer of true lists of messages.</p>

 <p>Moved @(tsee msg-downcase-first) and @(tsee msg-upcase-first) from the <see
 topic='@(url string-utilities)'>string utilities</see> to the <see
 topic='@(url message-utilities)'>message utilities</see>.</p>

 <p>A new book, @('kestrel/utilities/proof-builder-macros.lisp'), is a place to
 define @(see proof-builder) macros.  This book currently defines a simple
 macro, @('when-not-proved') (see @(tsee acl2-pc::when-not-proved)), for
 skipping instructions when all goals have been proved.  It also defines two
 (more complex) macros, @('prove-guard') (see @(tsee acl2-pc::prove-guard)) and
 @('prove-termination') (see @(tsee acl2-pc::prove-termination)), for
 (respectively) using previously-proved @(see guard) or termination theorems
 efficiently, as well as a more general macro, @(tsee acl2-pc::fancy-use), for
 using lemma instances (via @(':use')) efficiently.</p>

 <p>Improved the @('copy-def') utility (community book
 @('kestrel/utilities/copy-def.lisp')) in several ways: added an @(':expand')
 hint in the recursive case (as is sometimes necessary), improved it to work
 better with @(tsee mutual-recursion), and improved it to work better with an
 @(':equiv') argument.</p>

 <p>Fixed the utility, @(tsee orelse), so that @(':quiet t') pushes the output
 stack, as per existing documentation.</p>

 <p>Fixed a few books that broke due to the change in @(tsee defevaluator) (see
 @(see note-8-1) for details).</p>

 <h4><see topic='@(url soft::soft)'>SOFT</see></h4>

 <p>Added a @(':print') option to control screen output.</p>

 <p>Improved user input validation.</p>

 <p>Added support for the new @(':constrain') option of @(tsee defun-sk).  This
 option is now supported by SOFT's @(tsee soft::defun-sk2) and @(tsee
 soft::defun-inst) macros.</p>

 <h4><see topic='@(url x86isa)'>X86ISA</see></h4>

 <p>Most of the model has been extended to 32-bit mode.  The only instructions
 that remain to be extended to 32-bit mode are JMP far and the floating-point
 instructions.  The 32-bit-only instructions PUSHA, POPA, INC with opcodes
 40h-47h, DEC with opcodes 48h-4Fh, and PUSH CS/SS/DS/ES have been added to the
 model.  Support for the kinds of paging in 32-bit mode is still missing, but
 this is only needed for the system view of the model, not the application
 view.</p>

 <p>Some of the XDOC documentation and some of the comments have been slightly
 expanded.</p>

 <p>The notion of programmer-level mode and system-level mode have been renamed
 to `application-level view' and `system-level view', to avoid overloading the
 word `mode', which in the x86 has a more specific meaning.  Similarly, the
 notion of page structure marking mode has been renamed `marking view'.  This
 involved renaming the @('programmer-level-mode') and
 @('page-structure-marking-mode') field of the state stobj to the shorter
 @('app-view') and @('marking-view'), and also renaming some functions and
 theorems acccordingly.</p>

 <p>The instruction decoder has been extended to detect VEX- and EVEX-encoded
 (AVX, AVX2, AVX512) instructions, in both 64- and 32-bit modes of operation.
 However, semantic functions of many of these instructions are still
 unimplemented.</p>

 <p>Annotated opcode maps are now used to generate opcode dispatch functions
 and instruction coverage information.</p>

 <h4><see topic='@(url apt::apt)'>APT</see></h4>

 <p>Improved documentation.</p>

 <p>Improved options to control the screen output.</p>

 <p>Improved @(tsee apt::tailrec) transformation with an option to attempt to
 automatically infer the domain for some of the transformation's applicability
 conditions.</p>

 <p>Improved @(tsee apt::restrict) transformation to wrap the restriction test
 with @(tsee mbt); added an applicability condition to ensure that the
 restriction test is boolean-valued.</p>

 <p>Imported more symbols from the @('\"ACL2\"') package into the @('\"APT\"')
 package.</p>

 <h4><see topic='@(url acl2::bitops)'>Bitops</see></h4>

 <p>Added the @(see bitops::sparseint) library, which represents large integers
 as balanced binary trees, which can save memory by sharing structure among many
 such objects.</p>

 <h4><see topic='@(url acl2::sv)'>SV</see></h4>

 <p>Improved scalability of several SV utilities when large variables are present
 by recoding several functions that previously used Lisp bignums to use a
 @(see bitops::sparseint) based encoding.</p>

 <h4><see topic='@(url gl::gl)'>GL</see></h4>
 <p>Added optional accumulated-persistence-style profiling of attempted rule
 applications, available with keyword argument @(':prof-enabledp t').</p>

 <p>Changed the representation of symbolic objects, removing the @(':g-number')
 form which could represent complex rationals and replacing it with a simpler
 @(':g-integer') form.  (Complex rationals may still be supported using
 rewriting.  Also, the @(':g-number') shape specifier is still supported for
 backward compatibility, though it is restricted to only represent integers and
 translates directly into @(':g-integer') symbolic objects.)  Removed some
 native symbolic counterparts for functions that can be dealt with more cleanly
 via rewrite rules.</p>

 <h4><see topic='@(url gl::glmc)'>GLMC</see></h4>
 <p>Added option to bind some variables that can be used by the nextstate, property,
 constraint, and initstate terms.  These bindings will be symbolically evaluated once,
 which can perhaps improve performance by not requiring them to be repeated.</p>

 <h4><see topic='@(url acl2::xdoc)'>Xdoc</see></h4>

 <p>Added a utility, @(see xdoc::archive-xdoc), that saves the documentation
 generated by a series of local events, partially preprocessing it to avoid
 references to definitions that might only be locally available.</p>

 <p>The @(tsee defpointer) utility for @(see xdoc) now accepts names that have
 special characters such as @('<').</p>

 <h4><see topic='@(url acl2::std)'>STD</see></h4>

 <p>The @('std/typed-lists/unsigned-byte-listp.lisp') book now includes
  @('std/lists/take') locally. As a result,
  @('projects/x86isa/tools/execution/exec-loaders/mach-o/mach-o-reader.lisp'),
  @('std/io/take-bytes.lisp'), @('unicode/read-utf8.lisp'), and
  @('unicode/utf8-decode.lisp') also include this book locally.</p>

 <h3>Licensing Changes</h3>

 <h3>Build System Updates</h3>

 <p>The build system now has support for @(see ifdef) and @(see ifndef), which
 are @(see make-event)-supported macros defined in @('books/build/ifdef.lisp').
 In particular, this allows the community books' makefile to support building
 different versions of the manual depending what external tools are
 installed.</p>

 <h3>Testing</h3>

 <h3>Miscellaneous</h3>

 <p>A BibTeX file has been added to the community books, containing reference
 information for papers published at the ACL2 Workshops.  This may be useful to
 you if you wish to cite such a paper in a LaTeX document.  It is available at
 @('books/workshops/references/').  That directory also contains an example
 LaTeX file demonstrating how the references may be cited, as well as a README
 with some more information.</p>

 <p>A Developer's Guide (see @(see developers-guide)) has been added, to assist
 those who may wish to become ACL2 Developers.  It replaces the much smaller
 ``system-development'' topic.</p>

 <p>The download button now works in the web-based manual.</p>

 <p>When the @(tsee include-raw) utility with option @(':do-not-compile t') was
 followed by @(':')@(tsee comp), it was possible for that subsequent
 compilation to overwrite intended raw Lisp definitions, for a host Lisp that
 does not compile on-the-fly (i.e., for a host Lisp other than CCL or SBCL).
 The way to prevent such overwrites is to extend @(see state) globals
 @('program-fns-with-raw-code') and @('logic-fns-with-raw-code'), which however
 was not always done.  This is now done automatically, which fixes the
 overwrite problem.</p>

 ")

(defxdoc note-8-0-books

; Note: To see all git log entries with a given author, for example Joe
; Q. Bignerd, you can issue a command such as the following (use a substring of
; the author name) and then look at the new file, tmp:

;    git log -n 1000 --name-only --author='gnerd' > tmp

; Shilpi Goel: As discussed in the ACL2 2017 Workshop, I am adding
; this doc topic in the hopes that the members of the ACL2 community
; will track changes to their books as they go by logging them here.
; The idea is that the information in this topic can be somewhat more
; high-level than is normally provided in commit messages.

; Please add information about your library in the appropriate
; category below --- the category title is enclosed in <h3>..</h3>
; tags (of course, feel free to add a new category if needed).  To
; ensure consistency with the style of previous book release doc
; topics, please follow the following convention:

;  <h4>Your Library Title</h4>
;  <p>Details go here.</p>

  :parents (note-8-0 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 8.0"

  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 7.4 and 8.0.</p>

 <p>See also @(see note-8-0) for the changes made to ACL2 itself.  For
 additional details, you may also see the raw <a
 href='https://github.com/acl2/acl2/commits/master'>commit log</a>.</p>

 <h3>New Libraries</h3>

 <h4>Supporting materials for the 2017 ACL2 Workshop</h4>

 <p>See the new directory, @('workshops/2017/') &mdash; specifically, its
 @('README') file.</p>

 <h4>SAT proof-checker for cube-and-conquer</h4>

 <p>The new directory is @('projects/sat/lrat/cube/').  See file @('README') in
 that directory.</p>

 <h4>SAT proof-checker from 2011</h4>

 <p>An early SAT proof-checker based on resolution may be found in directory
 @('books/projects/sat/zz-resolution-checker/'); see the @('README') in that
 directory.  It was sufficiently efficient to get limited use in industry, but
 ultimately was superseded by much more efficient clause-based
 proof-checking (see directory @('books/projects/sat/lrat/')).</p>

 <h4>EDIF conversion</h4>

 <p>See @('projects/async/tools/convert-edif.lisp') for tools to convert
 between EDIF format and corresponding convenient s-expressions.</p>

 <h4>try-gl-concls</h4>

 <p>See @(see try-gl-concls) for a small but convenient utility to
 find all the true conclusions (if any) from a user-provided list of
 possible conclusions using @(see GL::GL).</p>

 <h4>GLMC</h4>

 <p>GLMC (in directory @('centaur/glmc')) is a connection from ACL2 to
 AIG-based hardware model checkers, via @(see gl::gl); this can be used to
 prove safety properties without finding an inductive invariant.  See @(see
 gl::glmc) for details.</p>

 <h4>Truth</h4>

 <p>Directory @('centaur/truth') contains a library for using integers as a
 representation for Boolean functions with small (single-digit) numbers of
 variables, expressing the functions as truth tables.  Truth tables for 5 or
 fewer variables are especially efficient since the formulas are represented as
 fixnums (at least in 64-bit lisps).</p>

 <h4>Ipasir</h4>

 <p>The @(see ipasir::ipasir) library (in directory @('centaur/ipasir'))
 contains an axiomatized interface for using incremental SAT solver libraries in
 ACL2.  A solver object is represented as an abstract stobj, and actual solver
 functions from a suitable shared library can be called as the implementation.
 Integration with @(see aignet::aignet) is also provided in the book
 @('centaur/aignet/ipasir').</p>

 <h4>ABNF</h4>

 <p>The <see topic='@(url abnf::abnf)'>ABNF (Augmented Backus-Naur Form)
 library</see> provides (1) a formalization of the syntax and semantics of the
 ABNF notation, (2) a verified parser that turns ABNF grammar text (e.g. from
 the HTTP RFC) into a formal representation suitable for formal
 specification (e.g. for HTTP parsing), and (3) executable operations on ABNF
 grammars, e.g.  to check their well-formedness and to compose them.</p>

 <h4>APT</h4>

 <p>The <see topic='@(url apt::apt)'>APT (Automated Program Transformations)
 library</see> provides tools to transform programs and program specifications
 with automated support.</p>

 <h3>Changes to Existing Libraries</h3>

 <h4>@(see std/io)</h4>

 <p>The @(see std/io) library now contains lemmas to help users prove
 that opened input and output channels remain open until closed, to
 aid guard theorem proofs.  See @(see open-channel-lemmas).</p>

 <h4>Miscellaneous @(see std) changes</h4>

 <p>The @('why') and @('why-explain') convenience macros in
 @('std/std-customization.lsp') now support rule classes other than
 @(':rewrite').</p>

 <p>The rule @('sets-are-true-lists') has been split into three rules with the
 same formula: a disabled @(see rewrite) rule of that name, a @(see
 compound-recognizer) rule @('sets-are-true-lists-compound-recognizer'), and a
 rewrite rule @('sets-are-true-lists-cheap') whose @(see backchain-limit) is
 1.</p>

 <p>A new utility @('def-updater-independence-thm') for proving stobj (and
 stobj-style) accessors independent of updaters has been added to
 @('std/stobjs/updater-independence.lisp').</p>

 <h4>Kestrel Utilities</h4>

 <p>The <see topic='@(url kestrel-utilities)'>Kestrel Utilities</see> have
 undergone several improvements and extensions.</p>

 <p>Improved an error message for @('verify-guards-program') (thanks to Eric
 Smith for feedback); see
 @('kestrel/utilities/verify-guards-program.lisp').</p>

 <p>Added utilities @(tsee trans-eval-state) and @(tsee
 trans-eval-error-triple), which provide convenient interfaces to the ACL2
 evaluator, @(tsee trans-eval).</p>

 <p>Improved the utility, @(tsee directed-untranslate), especially for handling
 @(tsee let) and @(tsee mv-let) expressions (and @('lambda') expressions) and
 towards ensuring executability of its results.</p>

 <p>Improved the utility, @('copy-def'), to avoid failures for some functions
 defined by @(tsee mutual-recursion).  Thanks to Eric Smith for a helpful bug
 report.</p>

 <p>Added utility @(tsee er-soft+) for producing soft errors with @(':')@(tsee
 logic) mode code, returning a specified @(see error-triple).  The new utility
 @(tsee er-soft-logic) is similar but a bit simpler, for use when the only
 property needed of the returned @(see error-triple) is that its error
 component is not @('nil').</p>

 <p>Added utility @(tsee manage-screen-output) which is an improved version of
 @(tsee control-screen-output) (which may eventually be removed).  Added
 utilities @(tsee make-event-terse), @(tsee restore-output), @(tsee
 restore-output?), @(tsee fail-event), and @(tsee try-event) to fine-tune
 screen output in event-generating macros.  Moved obsolete utility
 @('control-screen-output-and-maybe-replay') to Workshop supporting materials,
 where the only remaining use of this utility was.</p>

 <p>The new utility @(tsee orelse) arranges to evaluate an event and, if that
 fails, then to evaluate a second event.</p>

 <p>The applicability condition utilities have been replaced with the <see
 topic='@(url named-formulas)'>named formula utilities</see>, which are
 slightly more general and include a few improvements.</p>

 <p>New <see topic='@(url paired-names)'>paired name utilities</see> have been
 added, to construct names consisting of two names separated by a global
 customizable separator.</p>

 <p>A new @(tsee add-const-to-untranslate-preprocess) utility has been added
 that extend @(tsee untranslate-preprocess) to keep a constant unexpanded in
 output.</p>

 <p>New @(see error-checking) utilities have been added that check conditions
 on data (e.g. user input) and provide informative and consistent error
 messages. These utilities include a macro @(tsee def-error-checker) to
 concisely define error-checking functions.</p>

 <p>A new macro @('defbyte') has been added that introduces <see topic='@(url
 fty)'>fixtypes</see> for signed or unsigned bytes of specified sizes. Several
 instances of applications of this macro for common sizes of both signed and
 unsigned bytes is also provided.</p>

 <p>Utilities @(tsee doublets-to-alist) and @(tsee keyword-value-list-to-alist)
 have been added that convert lists of doublets and keyword-value lists to
 corresponding alists.</p>

 <p>A utility @(tsee assert?) has been added that is a variant of @(tsee
 assert$) with customizable context and message.</p>

 <p>The @(tsee integers-from-to) utility now has a logical definition that is
 easier to reason about than its tail-recursive definition for execution (which
 has not changed).</p>

 <p>The Kestrel world query utilities, term utilities, <see topic='@(url
 string-utilities)'>string utilities</see>, and character utilities
 (@('[books]/kestrel/utilities/characters.lisp')) have undergone several
 improvements and extensions.</p>

 <p>A few theorems about world-related functions and theorems about lists (in
 @('kestrel/utilities/list-theorems.lisp')) have been added.</p>

 <p>A new @(see logic)-mode utility, @(tsee magic-macroexpand), performs
 macroexpansion when all macros to be expanded are in logic mode.</p>

 <p>There is a new Kestrel symbol utilities book (initially with a single
 function, @('symbol-package-name-safe')).</p>

 <h4>The apply books</h4>

 <p>Updated books pertaining to @('apply$'); see @('projects/apply-model/') and
 @('projects/apply/').</p>

 <h4>SAT proof-checker</h4>

 <p>Additions and improvements have been made to the SAT proof-checker
 directories, under @('projects/sat/lrat/').  In particular, the proof was
 completed for the incremental checker (subdirectory @('incremental/') with an
 improved soundness theorem; a new directory was addded (@('cube/'), as
 mentioned above); and renamed subdirectory @('main/') to @('sorted/').  The
 key subdirectory is @('incremental/'); a new top-level book @('top.lisp')
 includes the top-level book in that subdirectory.</p>

 <h4>Aignet library</h4>

 <p>A few new verified <see topic='@(url aignet::aignet-comb-transforms)'>
 combinational logic transforms</see> have been
 added to aignet, most notably <see topic='@(url aignet::fraig)'>fraiging</see>,
 DAG-aware <see topic='@(url aignet::rewrite)'>rewriting</see>, and
 DAG-aware and-tree <see topic='@(url aignet::balance)'>balancing</see>.
 These can be used as preprocessors for SAT solving with GL via @(see
 gl::gl-simplify-satlink-mode).</p>

 <h4>VL/SV libraries</h4>

 <ul>

 <li>SystemVerilog @('unique case') and @('unique0 case') can now optionally be
 treated differently from regular @('case') statements: either a constraint may
 be generated off to the side expressing the one-hot constraint, or logic may be
 added that assigns @('X') instead of the stated values when the one-hot constraint
 is violated.</li>

 <li>Somewhat similarly, @('enum') type variables may optionally either
 generate constraints stating that they take proper enum values, or may generate
 extra logic that forces them to @('X') when assigned an improper value.</li>

 <li>When composing together 0-delay update functions, if bit-level
 combinational loops are present, these are composed together to a fixpoint.</li>

 <li>@(see Vl::vl-lint) has yet another use-set check, @(see vl::vl-design-sv-use-set),
 which uses SV's interpretation of SystemVerilog semantics to more exactly
 analyze the usage and updates of module variables.  The previous @(see vl::Lucid)
 use-set check is still useful since sv-use-set only checks variables, not
 parameters, functions, types, etc., and also does not analyze variables local
 to procedural code blocks.</li>

 </ul>

 <h4>SOFT</h4>

 <p>The <see topic='@(url soft::soft)'>SOFT (Second-Order Functions and
 Theorems) library</see> has been improved in several ways. The @(':thm-name')
 option is now fully supported for second-order quantifier functions and their
 instances.  The treatment of user inputs is more robust. The user interface is
 more terse. The implementation is more streamlined. A more comprehensive test
 suite now exists.</p>

 <h4>X86ISA</h4>

 <ul>

 <li>The <see topic='@(url x86isa)'>X86ISA</see> has been slightly extended with
 infrastructure to support 32-bit mode of operation; in particular, the
 @('64-bit-modep') predicate is no longer always true. Some documentation
 topics and some comments have been expanded and clarified. Some exceptions are
 now being added to the fault field of the x86 state rather than the
 model-specific field. A complete model of segment address translation has been
 added.</li>

 <li>Codewalker can now be used to reason about 64-bit user-level x86
 programs --- see
 @('books/projects/x86isa/proofs/codewalker-examples') for demos.</li>

 <li>Memory functions do not traffic in lists anymore.  Instead of a
 list of canonical addresses, a contiguous linear memory region is now
 specified by: @('<n, lin-addr>'), where @('n') is the number of bytes
 to be read or written and @('lin-addr') is the first address of the
 memory region.</li>

 <li>In the programmer-level mode, disjointness of memory regions can
 be conveniently expressed using a function called @('separate').  All
 the proofs in the programmer-level mode have been updated to use this
 paradigm.</li>

 </ul>

 <h4>AVR ISA</h4>
 <p>Julien Schmaltz and Peter Schwabes' AVR ISA model has been contributed in book
 @('projects/avr-isa').</p>

 <h4>Miscellaneous Books</h4>

 <p>The book @('clause-processors/use-by-hint') now contains an additional
 utility, @(see use-termhint), that helps structure hints in a way that
 coincides with the structure of a proof and allows hints to contain terms that
 have been simplified along with the goal.</p>

 <p>A new book @('tools/symlet') introduces a macro @('let-syms') and @('b*')
 binder @('symlet') that simply replace occurrences of some symbols with some
 corresponding terms in the enclosed term.  Like Common Lisp's
 @('symbol-macrolet') but much less smart.</p>

 <p>Fixed @('misc/profiling.lisp') for newer distributions of CCL (Clozure
 Common Lisp), both from SVN and from GitHub.</p>

 <p>The macro @(tsee defconsts) now provides a better error message when given
 a symbol that does not have the syntax of a constant.</p>

 <p>The macro @(tsee must-fail) has a new keyword option, @(':expected'), to
 indicate the kind of error that is expected.  New macros @(tsee
 ensure-soft-error), @(tsee ensure-hard-error), and @(tsee ensure-error)
 provide nice interfaces to @('must-fail') with the legal values of this new
 option.  See @(see must-fail).  Thanks to Eric Smith for discussions leading
 to these changes.</p>

 <p>Modified @(tsee removable-runes) to allow a multiplier greater than 1.
 Modified output accordingly.  Also, the multiplier @('m') now provides
 non-strict bounds @('(floor (* m steps) 1)') rather than the previous
 strict bound @('(1- (ceiling (* m steps) 1))').  Moreover, a related new utility,
 @(tsee minimal-runes), returns a list of runes to enable that is sufficient
 for admitting the event.</p>

 <h3>Licensing Changes</h3>

 <h3>Build System Updates</h3>

 <p>Improved books cleaning slightly, in @('books/GNUmakefile').</p>

 <p>By default, the @(''make'') targets for certifying books now include the
 books that depend on quicklisp, except when the host Lisp is GCL.  Specify
 @('USE_QUICKLISP=0') if that is not what you want.</p>

 <p>Improved @('books/GNUmakefile') so that by default, it reports an error
 when the @('bash') shell is missing.  (Note that a version of @('sh') on a
 FreeBSD machine caused an error.)</p>

 <p>Also see @(see note-8-0), specifically the section on ``Changes at the
 System Level''.</p>

 <h3>Testing</h3>

 <p>The documentation topics for testing have been reorganized, with
 introduction of a new topic, @('kestrel-testing-utilities'), as a parent of
 the testing utilities that are part of the @(see kestrel-books), so that now
 the topic @(see testing-utilities) is the top-level topic for the testing
 utilities.</p>

 <p>The Kestrel Testing Utilities have been integrated with similar testing
 utilities under @('[books]/misc').  The utilities in
 @('kestrel/utilities/testing.lisp') have been added to @('misc/eval.lisp') and
 @('misc/assert.lisp'), and the tests in
 @('kestrel/utilities/testing-tests.lisp') have been moved into two new files
 @('misc/eval-test.lisp') and @('misc/assert-tests.lisp').</p>

 <p>The utility @(tsee run-script) supports testing of evaluation of the forms
 in a given file, to check that the output is as expected.  So far, several
 existing scripts have been adapted to take advantage of this utility:</p>

 <ul>

 <li>@('books/demos/mini-proveall-input.lsp') &mdash; a long-standing, small
 basic test of ACL2</li>

 <li>@('books/demos/marktoberdorf-08/') &mdash; based on material originally
 presented by J Moore in 2008 at the Marktoberdorf Summer School; see the
 @('README') file in that directory</li>

 <li>@('books/demos/big-proof-talks/') &mdash; based on material about ACL2
 presented by J Moore on July 6 and 7, 2017, at the <a
 href='https://www.newton.ac.uk/event/bpr'>Big Proof workshop</a>; see the
 @('README') file in that directory</li>

 <li>@('books/projects/paco/books/proveall-input.lsp'), formerly named
 @('proveall.lsp')</li>

 </ul>

 <h3>Miscellaneous</h3>

 <p>Added file @('system/to-do.txt') to list some potential developer
 tasks.</p>

 <p>Fixed a bug in the package redefinition utility in community book
 @('books/misc/redef-pkg.lisp').</p>

 <p>Defined a constant @(tsee *acl2-system-exports*) that extends @(tsee
 *acl2-exports*) for system programmers.</p>

 ")

(defxdoc note-7-2-books

; Shilpi Goel
; A note on how I prepared :doc note-7-2-books
;
; Of course, the easiest (and the fairest?) way to prepare the books
; release notes is for everyone to update them the way Matt updates the
; ACL2 release notes --- as and when updates are made.  But we all don't
; do that.
;
; In this note, I've mentioned some useful git filtering commands that
; I used to sift through the commit messages. Please feel free to add
; suggestions, advice, etc. or delete this note altogether.

; Actually, this wasn't too bad to do, considering the huge amount of
; work that was done in the community between 7.1 and 7.2 releases. It
; took me about six hours, in two 3 hour increments. Note though that
; note-7-2-vl was prepared by Jared Davis.
;
; # Get a commit log from the date of last release onwards; in this
;   case, the date was May 5, 2015.
;
; > git log --since="May 5, 2015" --no-merges > note-7-2-books-raw.txt
;
; # Get a list of all authors that contributed during this period:
;
; > fgrep "Author:" note-7-2-books-raw.txt | sort | uniq
;
; # Separate out commit messages by author --- the assumption is that an
;   author will usually work on the same corpus of books and it'll be
;   easier to consolidate commmits made to them.
;
; > git log --since="May 5, 2015" --no-merges --author=shigoel > shigoel.txt
;
;   and so on for every author in the list above.
;
; # Check if any commits were missed out during this separation of
;   commits by authors: the outputs of the following two commands must
;   be the same. Note that the second command assumes that the only
;   *.txt files in the current directory are those created during this
;   process.
;
; > fgrep "Author:" note-7-2-books-raw.txt | wc -l
;
; > fgrep "Author:" --exclude=note-7-2-books-raw.txt *.txt | wc -l
;
; # Look in [books]/system/doc/acl2-doc.lisp (the book where users are
;   free to contribute documentation) for clues about where the books
;   release notes must be placed. For 7.2 release (and for others before
;   it till 6.4 release), this is in [books]/doc/relnotes.lisp, as is
;   noted in *acl2-broken-links-alist*.
;
; # Start writing the release notes by going over the author-specific
;   text files.
;
;   - I mentioned the authors of "New Libraries" but I did not mention
;     the names of those who made changes to existing libraries, unless
;     their contribution was "overwhelming" or "total" in some
;     way. E.g., Dmitry Nadezhin made considerable changes to the RTL
;     books between 7.1 and 7.2 and so I've mentioned his name in the
;     release notes under RTL.
;
;   - In case a commit message is unhelpful in determining whether that
;     commit is weighty enough to warrant a mention in the release
;     notes, it can be useful to get a list of files changed by an
;     author along with the commit SHA and date.
;
;     > git log --since="May 5, 2015" --no-merges --stat --author="Foo"
;
;   - It can also help to read discussions on closed pull requests and
;     steal stuff from there (see
;     https://github.com/acl2/acl2/pulls?q=is%3Apr+is%3Aclosed). You can
;     choose to filter the pull requests by author, term, etc., and even
;     sort them.
;
;   - If you want to go crazy and do a thoroughly good job, you can
;     examine the patch introduced at each commit. You might want to
;     redirect the output to a temp file for the following command.
;
;     > git log --since="May 5, 2015" --no-merges -p --author="Foo"
;
;   - Sometimes, it can be helpful to see whether a new file was added
;     in a commit or merely modified. Use --name-status for that.
;
;     > git log --since="May 5, 2015" --no-merges --author="Foo" --name-status
;
;   - To see the history of a particular file:
;
;     > git log --since="May 5, 2015" --no-merges --stat filename
;
  :parents (note-7-2 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 7.2 (Jan 2016)"
  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 7.1 and 7.2.</p>

 <p>See also @(see note-7-2) for the changes made to ACL2 itself.  For
 additional details, you may also see the raw <a
 href='https://github.com/acl2/acl2/commits/master'>commit log</a>.</p>

 <h3>New Libraries</h3>

<h4>@(see kestrel-books)</h4>

 <p>Kestrel Institute's contributions are now available under
 @('kestrel/') directory. This directory contains some system
 utilities to complement the built-in @(see system-utilities). It also
 includes some general utilities to build and execute tests, retrieve
 constituents of ACL2 events like @(see defun-sk), etc.</p>

 <h4>Modeling Algorithms in SystemC and ACL2</h4>

 <p>David Russinoff has contributed a library, @('projects/masc/'),
 for modeling algorithms in SystemC and ACL2.</p>

 <h4>SOFT</h4>

 <p>Alessandro Coglio has contributed a tool called SOFT (Second-Order
 Functions and Theorems) that mimics second-order behavior. See
 @('tools/soft.lisp').</p>

 <h4>stateman</h4>

 <p>J Strother Moore's @('stateman') books are located in
 @('projects/stateman/'). @('Stateman') is a utility that uses
 metafunctions to manage large terms tepresenting machine states.</p>

 <h4>@(see sv)</h4>

 <p>SV is a new hardware verification library from Centaur Technology
that includes a vector-based expression representation, efficient
symbolic simulation integrated with @(see gl), and support for many
SystemVerilog features.  It replaces @(see esim) as a backend to @(see
vl); see @(see sv::sv-versus-esim) for a comparison.</p>

 <h4>@(see x86isa)</h4>

 <p>Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann have
 contributed a library, @('projects/x86isa/'), containing the
 specification of the x86 instruction set architecture and utilities
 to simulate and reason about x86 machine code.</p>

 <h4>Other new books</h4>

 <p>A toy cache coherency protocol called VI and its proof of
  correctness have been contributed by Ben Selfridge and David Rager
  in @('projects/cache-coherence/'). This effort takes an approach
  that starts with a goal invariant and develops many helper
  invariants while trying to prove this goal invariant.</p>

 <p>David Russinoff has contributed a proof of the group axioms for
 the addition operation on the elliptic curve known as
 @('Curve25519'); these books can be found in
 @('projects/curve25519/'). Another library in @('projects/shnf')
 contains a formalization of the theory of sparse Horner normal forms
 for integer polynomials.</p>

 <p>Ben Selfridge has contributed his library @('projects/sb-machine')
 that contains a formalization of the x86-TSO memory model. This model
 contains a machine with multiple processors, a shared memory, and
 store buffers.</p>

 <p>The book @('demos/meta-wf-guarantee-example.lisp') has an example
 that demonstrates the use of @(':well-formedness-guarantee') for
 @(see meta) rules</p>

 <p>The book @('misc/install-not-normalized.lisp') installs an
 unnormalized definition; see @(see install-not-normalized).</p>

 <p>The book @('hints/hint-wrapper.lisp') allows you to supply hints
 in the statement of a theorem; see @(see hint-wrapper).</p>

 <p>@('system/event-names.lisp') defines @(see ep) and @(see ep-) to
  return the list of event names (resp., excluding those events built
  into ACL2) with a given case-insensitive prefix.</p>

 <p>@('system/termp.lisp') contains work done to verify the guards of
  the ACL2 built-in function @(see termp).</p>

 <p>A new book @('tools/flag.lisp') creates a flag-based induction
 scheme for a mutual recursion; see @(see make-flag).</p>

 <p>New timing tools like @(see oracle-time) and @('oracle-timelimit')
 in @('tools/oracle-time.lisp') provide the run time and bytes
 allocated during the execution of a form.</p>

 <p>A new book @('tools/removable-runes.lisp') automatically computes
    runes to disable in order to speed up a proof. See @(see
    removable-runes).</p>

 <h4>Libraries in @('workshops/2015/')</h4>

 <p>Supporting materials for some accepted papers in the <a
 href='https://www.cs.utexas.edu/users/moore/acl2/workshop-2015/'>ACL2
 Workshop, 2015</a> can be found in the directory
 @('workshops/2015/').</p>

 <ul>

 <li>Cuong Chau, Matt Kaufmann, and Warren Hunt contributed their
 books on Fourier Series Formalization in ACL2(r) in subdirectory
 @('chau-kaufmann-hunt/').</li>

 <li>David Hardin contributed his books involving reasoning about LLVM
 code using Codewalker in the subdirectory @('hardin/').</li>

 <li>Panagiotis Manolios and Mitesh Jain submitted their work on
 proving skipping refinement with ACL2s in the subdirectory
 @('jain-manolios/').</li>

 <li>Yan Peng and Mark Greenstreet contributed their libraries to
 extend ACL2 with SMT solvers using SMTLINK in the subdirectory
 @('peng-greenstreet/').</li>

 </ul>

 <h3>Changes to Existing Libraries</h3>

 <h4>@(see ACL2-sedan) related books</h4>

 <p>The book @('acl2s/defdata/defdata-attach.lisp'), which is used to
 attach or modify metadata for a @(see defdata) type, now truely uses
 defattach for enumerators, i.e., enumerators have constant names that
 can be attached to different enumerator functions. This facility thus
 deprecates enum/test and separate test-enumerators. For now, most
 enumerators are in @(see program) mode and non-guard-verified, and
 hence, defattaching them requires trust-tags.</p>

 <p>The @(see cgen) books have been updated as follows:</p>

 <ul>

 <li>Support has been added for collecting statistics on which
    hypotheses are failing in vacuous tests.</li>

 <li>First-class support (e.g., for equality) has been added for
    membership relation/constraint, i.e., member/enum has the same
    status as range types.</li>

 <li>Nested testable events like @('thm'), @('defthm'), etc. are not
    supported anymore. This results in the simplification of the
    @('event-stack') global to just a @('event-ctx') global, which
    stores the @('ctx-form'). This simplification also allows us to
    aim for a global timeout on cgen/testing thm/defthm forms.</li>

 <li>Support for complex-rationals has been added in number
    ranges.</li>

 </ul>

 <p>The @(see acl2s::defunc) books have been udpated as follows:</p>

 <ul>

  <li>The @('print-summary') event prints total time taken by
    @('defunc') events.  Now time is only printed twice, once for
    @('test?') and once for @('defunc') logical events. Both these
    times are computed using @(see read-run-time) ACL2 function and is
    the accurate run time (not wall-clock time).</li>

  <li>A new timeout abort event is inserted at the beginning of the
    defunc/static/non-static events set (generated by
    @('defunc-events-with-staticp-flag') function) . This event checks
    if the elapsed time has exceeded the timeout limit and if it has,
    then it aborts with an error and thus we fall through the outer
    @(':OR') to the next choice.</li>

  <li>The @('program-mode-p') predicate function now checks the
   following: Is there a program-mode sub-function in the body?</li>

  <li>The @('cgen-timeout') parameter is used to restrict time spent
   by all the body contract testing as a global timeout.</li>

 </ul>

 <h4>@(see b*)</h4>

 <p>The syntax for FUN binders @(see patbind-fun) has been extended to
    allow inline/notinline declarations on the resulting @('FLET')
    forms.</p>

 <p>@('b*') now requires that variables be bound to a form and it will
 no longer treat @('nil') and @('t') as aliases for @('&'). Error
 messages produced by @('b*') have been made more informative.</p>

 <h4>@(see bitops)</h4>

 <p> Reduction XOR related functions have been added to the
 @('bitops') library in @(see bitops::parity). Lemmas in @(see
 bitops::bitops/ihsext-basics) have been cleaned up. Theorems about
 @(see unsigned-byte-p) have been added for @(see
 bitops::rotate-right) and @(see bitops::rotate-left).</p>

 <p>A small book about @(see floor) has been added:
 @('centaur/bitops/floor.lisp').</p>

 <p>More slice and merge functions have been added in @(see
 bitops::bitops/merge). Some @(see integer-length) rules in
 @('centaur/bitops/integer-length.lisp') have been changed to allow
 better free variable matching.</p>

 <h4>coi</h4>

 <p>A new book for reasoning about modular arithmetic using @('nary')
 congruences has been contributed; see
 @('coi/nary/nary-mod.lisp').</p>

 <p>Books in @('coi') have been updated so as to avoid name conflicts
 with @('std') books.</p>

 <h4>@(see fty)</h4>

 <p>The @('fty') books have been re-organized --- @('deftypes.lisp')
 has been split up into different files, and tests have been moved to
 a subdirectory @('tests/'). Performance problems with certain macros,
 mostly related to reasoning about tag and kind functions, have been
 fixed.</p>

 <p>@(see fty::deftranssum) has been extended to support nested @(see
 fty::defprod)s.</p>

 <h4>@(see quicklisp)</h4>

 <p>The bundled quicklisp libraries have been updated.  The quicklisp
books work only for ACL2 built on CCL or SBCL.</p>

 <h4>@(see rtl)</h4>

 <p>The @('rtl/rel11') books have seen many updates, courtesy of
 Dmitry Nadezhin.</p>

 <p>Guards have been added to functions in
 @('rtl/rel11/lib/'). General cleanup of the @('rtl/rel11/') books,
 like removing unnecessary hypotheses and @(see include-book)s, has
 also been done.</p>

 <p>New radix-aware versions of functions in @('rtl/rel11/support/')
 directory have been added. E.g., the old function @('bitn') has a
 fixed radix of 2 and takes @('x') and @('n') as input arguments and
 the new radix-aware version corresponding to this function is
 @('digitn'), which takes the radix @('b') in addition to @('x') and
 @('n') as inputs.</p>

 <p>The books @('rtl/rel11/support/basic.lisp'),
 @('rtl/rel11/support/bits.lisp'),
 @('rtl/rel11/support/float.lisp'),
 @('rtl/rel11/support/reps.lisp'), and
 @('rtl/rel11/support/masc.lisp') are now certifiable by ACL2(r).</p>

 <p>Some books from @('rtl/rel11/rel9-rtl-pkg/lib'), like
 @('reps.lisp'), @('rom-helpers.lisp'), and
 @('simple-loop-helpers.lisp'), along with their supporters, have been
 moved to @('rtl/rel11/support/').</p>

 <p>Bugs in @('rtl/rel11/lib/excps.lisp') related to divide-by-zero
 exception and the @('ep') exponent width in the function
 @('convert-nan-to-op') have been fixed.</p>

 <h4>@(see std)</h4>

 <p>A new macro called @(see impliez) has been added in
 @('std/basic/defs.lisp'). This macro expands to an @(see if), so
 unlike @(see implies), guards in the consequent can be verified
 assuming the antecedent.</p>

 <p>New theorems about @(see acl2-count) and @(see nth) have been
 added to @('std/lists/nth.lisp').</p>

 <p>The guards of @(see list-equiv) in @('std/lists/list-defuns.lisp')
 have been verified. The function @(see list-fix) was tweaked so that
 it avoids consing if its input is indeed a @('true-listp'). A new
 function @(see llist-fix), which is logically @('list-fix') but is
 the identity function for execution, has been also added.</p>

 <p>A possibly better non-CCL raw Lisp implementation of @(see
 bitsets::bignum-extract) has been added.</p>

 <p>A new rule @('pick-a-point-subset-constraint-helper') was added in
    @('std/osets') to allow pick-a-point proofs to be used even when
    subset is disabled.</p>

 <p>For @(see std::define), @('defretd') has been added to go with
 @(see std::defret). Also, @('defret') now allows the @('otf-flg')
 flag. @(':guard t') declarations in @('define') have been eliminated
 if guards have already been provided. Also, information displayed by
 @(see pe) of functions introduced using @('define') has been cleaned
 up using @(see pe-table).</p>

 <p>A new macro @(see std::rule) is a @('THM')-like version of @(see
 std::defrule).  @('Rule') and @('defrule') produce leaner output now,
 almost identical to that produced by @('thm') and @('defthm').</p>

 <h4>@(see vl)</h4>

 <p>For details about changes made to VL, see @(see note-7-2-vl).</p>

 <h4>@(see xdoc)</h4>

 <p>Topics with missing parents are now placed under a new topic @(see
 xdoc::missing-parents) instead of under @('top').</p>

 <p>The title of xdoc manuals can be easily configured by editing
 @('xdoc/fancy/config.js'). No warning about a redefined topic is
 produced when the topic is identical to the original one.</p>

 <p>@('xdoc') now loads @('acl2-doc-wrap') instead of @('acl2-doc') so
 that the loaded documentation doesn't overwrite the user's
 topics.</p>

 <p>A bug in @('see') that did not allow properly escaping the printed
 name of a symbol has been fixed. The implementation of @(see
 xdoc::defsection) had another bug that caused 'Definitions and
 Theorems' section to be added to topics even when there were no
 definitions or theorems in that section; this bug has been fixed as
 well. Also, @('defsection') does not explicitly turn on error
 printing during event submission anymore.</p>

 <p>The output from @(see xdoc::save) now shows more timing
 information.</p>

 <p>Legacy stuff like @('write-acl2-xdoc'), @(':import') option with
 @(see xdoc::save), and @('xdoc-verbose') has been removed.</p>

 <h4>Other Libraries</h4>

 <p>A new book @('projects/codewalker/demo-fact-partial.lisp') is a
 variant of @('projects/codewalker/demo-fact.lisp') that provides a
 guide to how Codewalker might be modified so that termination proofs
 can be avoided or delayed.</p>

 <p>Multiple values and stobjs are now supported in the
 @('coi/defung/') libraries.</p>

 <p>@(see Must-fail) and related utilities in @('misc/eval.lisp')
 produce much less output by default. Also,
 @('make-event/eval-check.lisp') no longer duplicates code from
 @('misc/eval.lisp').  Instead, it defines @('!') utilities that
 behave like the counterparts previously defined (without the @('!')
 suffix).</p>

 <p>A bug in @(see remove-hyps) that occurred when no proof steps are
 required in a proof has been fixed.</p>

 <p>A new @('tarai-measure') has been added in
 @('coi/termination/assuming/complex.lisp'), which is allows this book
 to certify quickly in ACL2(r) as well. Consequently, this book was
 removed from @('SLOW_BOOKS') in @('books/GNUmakefile').</p>

 <p>Some floating-point support has been added to the JVM M5 model;
 see @('models/jvm/m5/m5.lisp').</p>

 <p>@(see GL) now displays a more informative error message about
 duplicated indices in @(':g-bindings').</p>

 <p>@(see Satlink) now uses @('drat-trim'), available at
 @('tools/drat-trim/'), instead of @('drup-trim').</p>

 <p>The book @('tools/untranslate-for-exec.lisp') has been improved to
 handle nested mv-lets.</p>

 <h4>Deleted Books and Stubs</h4>

 <p>The book @('defexec/other-apps/records/records-bsd.lisp') has been
 deleted --- it was out of sync with @('records.lisp') in the same
 directory.</p>

 <p>The book @('make-event/assert-check-include-1.lisp') has been
 deleted.</p>

 <p>The book @('misc/dead-events.lisp') has been moved to
 @('tools/dead-events.lisp'), and a relocation stub has been added in
 the older location.</p>

 <p>In the directory @('misc/'), @('*-bsd.lisp') books are now
 @('reloc_stub') books.</p>

 <p>Books in @('projects/concurrent-programs/german-protocol/') have
 been moved to @('projects/cache-coherence/german-protocol/').</p>

 <p>The @('rtl/rel10') has been removed from the community
 books. These books were not in use anywhere in the contributed
 books.</p>

 <p>The book @('system/gather-dcls.lisp') has been deleted after its
 contents were moved to
 @('system/verified-termination-and-guards.lisp').</p>

 <h3>Licensing Changes</h3>

 <p>The following books now have BSD-3-Clause license.</p>

 <ul>

 <li>@('arithmetic-2/') and @('arithmetic-3/')</li>

 <li>@('misc/rtl-untranslate.lisp')</li>

 <li>M5 books @('models/jvm/m5/')</li>

 <li>@('rtl') books</li>

 <li>@('system/cantor-pairing-bijective.lisp')</li>

 <li>@('tools/with-arith5-help.lisp')</li>

 </ul>

 <h3>Build System Updates</h3>

 <h4>@(see build::cert.pl)</h4>

 <p>The @('cert.pl') documentation at @('build/doc.lisp') has been
 moved to its own @('BUILD') package.</p>

 <p>@('cert.pl') now produces successful certification messages that
 include times and color coding.  @('cert.pl') has also been patched
 to correctly handle filenames with dollar signs. It has new options
 for removing @('.cert.out') files after successful certifications and
 for sending them to a temporary directory.</p>

 <p>A new @(see build::cert_param) for SMTLINK, @('uses-smtlink'), has
    been added so that books using it will not be certified unless
    supporting software such as Z3 is installed. Another
    @('cert_param') called @('non-gcl') has been added.</p>

 <p>A new @('CERT_PL_SHOW_HOSTNAME') environment variable has been
 added to @('cert.pl') that can show the hostname after each book gets
 certified.</p>

 <h4>make system</h4>

 <p>The topic @(see Books-certification) gives clearer instructions on
 building the books and the manual.</p>

 <ul>

 <li>@('make manual') now just builds @('doc/top.cert') and
 @('system/doc/acl2-manual.cert').</li>

 <li>@('make everything') now just depends on all the books it was
 going to build.</li>

 <li>@('make quicklisp') now just causes an error if
 @('USE_QUICKLISP') is not set.</li>

 </ul>

 <h3>Miscellaneous</h3>

 <p>A new tool @('build/memsum.pl') analyzes memory usage during
 regressions.</p>

 <p>A new tool @('build/slowevents.pl') attempts to identify the
 slowest events in a book or a set of books.</p>")

(defxdoc note-7-2-vl
  :parents (note-7-2-books)
  :short "Notes about changes to @(see vl) and @(see sv) in ACL2 7.2."

  :long "<p>Below we describe changes since the ACL2 7.1 release to the
unstable, development version of @(see VL).  Note that the stable version,
@(see vl2014), is essentially unchanged except for minor bugfixes.  See also
@(see note-7-1-vl) for some background about VL and VL2014.</p>


<h3>Extended SystemVerilog Support</h3>

<p>Much of the development work has focused on supporting additional features
of SystemVerilog.</p>

<p><b>Interfaces.</b> VL and SV now have much better support for interfaces.
They can now contain functions, tasks, assignments, etc.  Modports are now
generally understood: they participate in scopes, are sanity checked for name
clashes, are supported in submodule instantiation, etc.  Interface usage in
submodule instances are properly type checked and are generally supported in VL
and through SV.  Note that interface arrays are not yet supported.</p>

<p><b>Assertions.</b> VL's parser and pretty-printer now support many
SystemVerilog assertion features, including at least sequence/property
expressions (see @(see vl::property-expressions)), procedural assertions (see
@(see vl::vl-assertstmt) and @(see vl::vl-cassertstmt)), sequence and property
declarations (see @(see vl::vl-sequence) and @(see vl::vl-property)), and
module-level assertions (see @(see vl::vl-assertion) and @(see
vl::vl-cassertion)).  Note that all of this assertion-related stuff is
currently ignored by the SV flow.  However, modules with assertions should at
least no longer result in parse errors, and these structures may some day be a
useful basis for implementing assertion checking tools.</p>

<p><b>Aliases.</b> Alias constructs should now work in VL and are also
supported by SV.</p>

<p><b>Expressions.</b> The @('**') (exponent/power) operator, @('inside')
operator are now supported in both @(see vl) and SV.  Note that NCV/VCS
disagree about the sizing of @('inside') operators and that in general these
operators may be buggy on commercial tools.  Added support for a few additional
system functions like @('$dimensions'), etc.</p>

<p><b>Statements.</b> The parsing and representation of @(see vl::statements)
has been extended in various ways.  Note that our support for statements in SV
is still rather limited, so just because we can parse these things doesn't
necessarily mean they will be handled all the way through the SV flow:</p>

<ul>

<li>@('break') and @('continue') statements are now implemented.</li>

<li>Statement labels are now supported.</li>

<li>There is better support for subroutine call statements; so we can now parse
things like @('void'(...)') and otherwise do slightly better with calls of
tasks/functions in statements.</li>

<li>We now permit function calls/task enables with explicit parens but no
arguments.  (In Verilog-2005, was is syntactically legal to write statements
like @('mytask;') but not @('mytask();') with the explicit parens, even though
they seem like they should be equivalent.  In SystemVerilog both forms are
allowed, but we had previously only supported the @('mytask;') version.)</li>

<li>Block statements (@('begin/end'), @('fork/join'), ...) can now have
typedefs.  We can now parse @('fork/join_any') and @('fork/join_none')
statements.</li>

<li>@('final') statements are now allowed.  Much like @('initial') statements,
these are simply ignored in the SV flow.</li>

</ul>


<p><b>DPI import/exports.</b> DPI import/exports, used to connect SystemVerilog
to C programs, are now tolerated by VL's parser and are now to some degree
understood by other parts of VL.  For instance, they are known to @(see
vl::scopestack)s and can be considered when checking for name clashes,
introducing implicit wires, etc.  See @(see vl::vl-dpiimport) and @(see
vl::vl-dpiexport).</p>


<p><b>Instances.</b> Module and gate instance arrays can now use the
single-expression ranges, i.e., we now support things like:</p>

@({
      and foo [3] (o, a, b);
      submod foo [3] (a, b, c);
})

<p>Note that SystemVerilog also allows multiple-dimension instance arrays, but
those are still unsupported.</p>


<p><b>Other.</b> Many bugfixes (e.g., to the parser, scoping, etc) have
resulted in VL being able to successfully load additional designs.</p>


<h3>Scoping and @(see vl::annotate) improvements.</h3>

<p>The SV and Linter flows now use a unified @(see vl::annotate) meta-transform
to prepare the design for analysis.  This transform has been significantly
improved to do a better job with scoping issues related to functions, tasks,
generate constructs, and statements.  This provides broad improvements to what
VL can successfully parse and translate.</p>

<p>The @(see vl::make-implicit-wires) transformation, which plays a
surprisingly important role in getting scoping right, now more closely matches
commercial tools like NCV and VCS.  We are particularly more careful about how
implicit wires are inferred from expressions involving indexing/selection like
@('foo[w]').  In general, in a structure pattern like @(''{foo : 3}'), it's
tricky to tell whether @('foo') is a structure member or a parameter.  VL now
handles this much better and our strategy is documented; see @(see
vl::vl-patternkey-ambiguity).  It also used to be that such patterns could fool
VL into inferring implicit wires for @('foo')!  This has been fixed.</p>

<p>Much of @('make-implicit-wires') has been moved into the related @(see
vl::shadowcheck) transform.  The representation of functions and tasks has been
adjusted to better support correct scoping and shadowchecking, and shadowcheck
now understands user-defined types.  Shadowcheck was also incorrectly handling
certain situations with package imports, which has been fixed.  It also now
checks for name clashes in all scopes and produces good warnings in this case.
Finally, shadowcheck treats the global scope in a less incorrect way, fixing
many problems with global package imports.</p>

<p>VL's scoping of generates also used to be completely wrong.  While it still
has some known bugs, it has been significantly improved.  The scoping of
@('genvars') is also improved.  Bugs have also been fixed related to
disambiguating types from expressions in functions and tasks, and also in the
handling of types versus interfaces in ports.</p>


<h3>Generates, Elaboration</h3>

<p>One of the trickiest parts of VL is elaboration, where parameters are
expanded into constants, generate blocks are resolved, etc.  To evaluate a
parameter like</p>

@({
     parameter foo = $bits(mypkg::mytype_t) + blah2size(settings.blah);
})

<p>we need to evaluate its expression.  This can involve looking up the values
of other parameters from other places in the hierarchy, evaluating system and
user-defined functions, etc.  Functions are defined in terms of statements, so
we need to understand statements as well.  This all gets to be a very messy
mutual recursion.</p>

<p>VL's implementation of elaboration now reuses much of the SV code for
converting Verilog expressions into @(see sv::svex)es, and is now able to
resolve many significantly more complex parameters and generates.</p>


<h3>Linter</h3>

<p>The @(see vl::vl-lint) tool now uses much more of the SV code.  It shares the
@(see vl::annotate) code with the SV flow and also uses SV-based elaboration,
which provides much better handling of generates and allows it to
unparameterize modules involving types and other complex expressions.  The very
useful size warnings from VL2014 have also been ported to work with the new SV
code base.</p>

<p>Various warning heuristics and messages have been tweaked.  We no longer
complain about duplicate interface instances, since that's perfectly
reasonable.  Parse errors have some additional context.  Lucid has been
extended to understand new features like interfaces and modports, DPI
imports/exports, and final blocks.</p>


<h3>Test Suites</h3>

<p>Significant work has gone into testing VL.  VL now has three test
suites:</p>

<ul>

<li><b>centaur/vl/linttest</b> &mdash; tests of Linter functionality.  This
notably includes a lot of tests of scoping and sizing issues.</li>

<li><b>centaur/sv/cosims</b> &mdash; tests comparing VL+SV behavior against
that of commercial simulators such as NCV and VCS.  These are our main tests of
SV.  You can also search for @('no_ncv') or @('no_vcs') to discover places
where VL disagrees with one tool or another (e.g., because the commercial tools
don't agree.)</li>

<li><b>centaur/sv/failtest</b> &mdash; tests that ensure VL+SV report fatal
errors for modules that have some bad problem.  This turns out to be a nice way
to test many scoping issues and make sure that we will reject bad
constructs.</li>

</ul>

<p>Running @('make vl') in the @('acl2/books') directory now automatically also
runs all of the linttests and failtests.  It doesn't automatically run the
cosims, since that requires commercial simulators.)</p>

<p>Each of the test suites has been extended considerably, especially in the
tricky areas of scoping, implicit wire creation, generate handling, and also in
order to test new features like interface support.  Many of the old VL2014
@('systest') tests have also been ported to the new @('cosims') format.</p>



<h3>Other Notes</h3>

<p>VL and SV are still evolving rapidly and a lot is in flux.</p>

<p>There has been significant renaming of files, moving of files, and deleting
of dead files.  The documentation has gotten a lot of work in some areas, but
of course there is more to do.</p>

<p>Numerous minor bugfixes in all areas of VL are not mentioned, but can be
found in the change log.</p>")

(defxdoc note-7-1-books
  :parents (note-7-1 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 7.1 (May 2015)"

  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 7.0 and 7.1.</p>

 <p>The <a
 href='https://github.com/acl2/acl2/wiki/Release-version-numbers'>acl2-books
 Wiki page on Release Version Numbers</a> gives the Git/SVN revision numbers
 corresponding to releases.  See also @(see note-7-1) for the changes made to
 ACL2 itself.  For additional details, you may also see the raw <a
 href='https://github.com/acl2/acl2/commits/master'>commit log</a>.</p>


 <h3>Deleted Books and Stubs</h3>

 <p>When we move a book, we often add a <b>stub</b> book in its previous
 location to help you transition your @(see include-book) commands.  The @(see
 build::cert.pl) build system prints warnings when a stub book is being
 included.  Stub books have a lifespan of one release.  The following books
 were stubs in ACL2 7.0, so we've deleted them.</p>

 @({
     Previous Location                          Replacement
   --------------------------------------------------------------------------------
     centaur/vl/mlib/context                    centaur/vl/parsetree
     centaur/vl/util/toposort                   centaur/depgraph/toposort
     centaur/vl/transforms/xf-unparameterize    centaur/vl/transforms/unparam/top
     misc/{qi,qi-correct}                       centaur/ubdds/lite
     oslib/logic-defs                           oslib/top-logic
     tools/defredundant                         std/util/defredundant
   --------------------------------------------------------------------------------
 })

 <p>The directory @('fix-cert/') has been deleted, as it is no longer necessary
 now that it is possible to move the system books directory after certifying
 its books (see @(see note-7-1)).</p>

 <p>The directory @('regex/') has been moved to @('projects/regex/').</p>


 <h3>New Libraries and Documentation</h3>

 <p>David Russinoff has contributed a new version of the rtl library:
 @('rtl/rel10/').  This time the new version depends on a previous version,
 namely, @('rtl/rel9/').  The new @('rtl/rel10/') library has, in turn, been
 adapted to reside in a new @('\"RTL\"') package; the result is
 @('rtl/rel11/').</p>

 <p>Marijn Heule's @('drat-trim') tool, for checking SAT solver proofs, is now
 available in @('tools/drat-trim').</p>

 <p>Matt Kaufmann and Cuong Chau have formalized the overspill property in
 ACL2(r), see @('nonstd/nsa/overspill.lisp').</p>

 <p>The new @('clause-processors/induction') book demonstrates a (not very
 practical) clause processor that does induction.</p>

 <p>The new directory @('projects/fifo') has a list-based FIFO implementation,
 that has some properties proven about it.</p>

 <p>The new book @('books/tools/include-an-arithmetic-book.lisp')
 provides short-hand includes of the arithmetic libraries, including
 various configurations of @('arithmetic-5').</p>

 <p>The @('misc/assert') book is now documented; see for instance @(see
 assert!).</p>

 <p>The documentation for @(see data-structures) is now included in the manual;
 previously it was excluded because of name conflicts with other libraries, but
 these have now been resolved.</p>

 <h3>Name Changes</h3>

 <p>As mentioned above, the newest @(see rtl) library is now in an @('RTL')
 package.</p>

 <p>The @(see bitops) library is now in a new @('BITOPS') package.  See below
 (under ``bitops'') for more information and suggestions about porting books.</p>

 <p>Renamed @('remove-keywords') to @('remove-any-keywords') in
 @('coi/nary/nary.lisp') to avoid a name conflict between the @('coi') and
 @('ccg') books; also updated the @('nary') workshop books.</p>


 <h3>@(see std)</h3>

 <p>The @(see b*) book has moved from @('tools/bstar') to @('std/util/bstar').
 There is a stub in the previous location.  As a special compatibility measure,
 this stub will be kept available for two releases.</p>

 <p>Added new @(see print-legibly) and @(see print-compressed) functions to
 @(see std/io).  These can print to @(':object') channels with or without @(see
 serialize)-style compression, and have the necessary theorems about state and
 output-channel preservation.</p>

 <p>There is new syntactic sugar based on @(see define)'s named return values.
 The new @(see defret) macro offers a more comfortable syntax for proving
 theorems about return values by their name.  Also, the new <see topic='@(url
 patbind-ret)'>ret</see> binder for @(see b*) allows you to name the bundled
 return values from a @(see define) and then access individual components using
 a C-like or @(see std::defaggregate)/@(see fty::defprod)-like @('.') syntax.</p>

 <p>The @(see define) macro now checks the arity of @(':returns') specifiers
 when possible.</p>

 <p>Some @('std/lists') books have been tweaked:</p>

 <ul>

 <li>The @(see acl2-count) book now provides stronger rules.</li>

 <li>The @('equal-sets') book now includes the lemma
 @('set-equiv-of-nil').</li>

 <li>The @('append') book now includes a few rules about (ca/dr (append ...))
 to std/lists.  (Two of the new rules are disabled, and there's a theory
 invariant to make sure things stay reasonable.)</li>

 <li>The @('duplicity') book now have stronger theorems relating @(see
 duplicity) to @(see member-equal).</li>

 </ul>


 <h3>@(see oslib)</h3>

 <p>Added a new @(see oslib::universal-time) function.</p>

 <p>Fixed a raw lisp bug with the definition of @9see oslib::ls), and added a
 regression test.</p>

 <p>Fixed minor bugs with @(see oslib::copy).</p>


 <h3>@(see bitops)</h3>

 <p>Bitops is now in a package.  To minimize backwards incompatibility, the new
 package imports a lot of stuff that you might not expect.  For instance all of
 the @(see logops-definitions), and their recursive @('**') variants are still
 found in the ACL2 package, as are most of the bitops rulesets, its new
 function definitions, and many frequently instantiated theorems.  When
 updating your books, you may find it convenient to import
 @('*bitops-exports*') into packages that use bitops functions.</p>

 <p>Extended the @(see bitops::bitops/merge) book with several new 256- and
 512-bit merges, @(see bitops::merge-8-u2s), and improved its
 documentation.</p>

 <p>Added @(see nth-slice128).</p>


 <h3>@(see fty::fty)</h3>

 <p>The case macros from @(see fty::defflexsum) and @(see fty::deftranssum) now
 require a variable, and cannot bind that variable itself, because the syntax
 for doing so was too weird and unintuitive.  They can now also be used to
 carry out type-checks, e.g., @('(foo-case x :mytag)') now returns true when
 @('x') has tag @(':mytag').</p>

 <p>The macros @('defoption') and @('deftranssum') macros, formerly part of
 @(see vl), are now integrated into the @(see fty::deftypes) framework.</p>


 <h3>@(see xdoc)</h3>

 <p>The fancy viewer's jump-to box should perform better.  It now suggest exact
 name matches first and otherwise shows results in importance order, instead of
 alphabetical order, which may be better when there are many matches.</p>

 <p>The fancy viewer now features a mobile-friendly version with many features.
 This should greatly improve access to ACL2 documentation at parties, sporting
 events, and other social occasions.</p>

 <p>Fixed a bug with @('<em>') tag handling that affected the @(':xdoc')
 command and Emacs-based @(see acl2-doc) tool.</p>

 <p>Fixed a bug with using multiple @(see defsection) extensions with the same
 name.  Defsection now requires a non-nil symbol as the section name.</p>

 <p>As the manual has grown substantially, some memory management measures have
 been taken in @('doc/top.lisp').</p>


 <h3>@(see quicklisp)</h3>

 <p>The approach to distributing Common Lisp libraries has been updated to use
 the new <a href='http://www.quicklisp.org/beta/bundles.html'>Quicklisp
 bundles</a> feature.  Some additional Common Lisp libraries have been
 added to the bundle.</p>

 <p>The @(see tshell) library is now based on the <a
 href='https://github.com/jaredcdavis/shellpool'>Shellpool</a> Common Lisp
 library (via @(see quicklisp)).  This may improve reliability and cross-lisp
 portability for @('tshell') itself and also for libraries like @(see satlink)
 which are based on it.</p>


 <h3>@(see vl), @(see esim), and now @(see vl2014)</h3>

 <p>VL and ESIM have undergone major changes, including a fork of VL.  For
 details about these changes, see @(see note-7-1-vl).</p>


 <h3>Other Libraries</h3>

 <p>Ben Selfridge's @(see leftist-trees) library is now available under an
 MIT/X11 style license instead of the GNU General Public License.</p>

 <p>The bounding theorems for @(see logext) in @('ihs/logops-definitions') have
 been tightened.</p>

 <p>For the @(see tau-system), there is now a @(see UNARY--) bounder in
 @('tau/bounders/elementary-bounders').</p>

 <p>The @(see defsort) macro has been enhanced to better support the fixtype
 discipline of the @(see fty::fty) library.  In support of this, it now
 requires a stricter transitivity property, i.e., the comparison function must
 support unconditional transitivity, regardless of element type.  (This is
 typically easy to achieve by using @('<<') as a fallback in case of malformed
 elements.)</p>

 <p>The Codewalker demo books have been improved to use built-in function
 nat-listp and weaken the hyps (state invariant) so that the state components
 consist of integers, not naturals.</p>

 <p>@(see gl) now uses an improved theory for better @(see
 def-gl-clause-processor) event performance.</p>

 <p>The @(see template-subst) tool now has some extended repetition
 capabilities.</p>

 <p>Various other libraries have received minor cleanups.</p>


 <h3>Build System Updates</h3>

 <p>@(see build::cert.pl), et al. now tolerate @('( include-book...') instead
 of @('(include-book...'), etc.</p>

 <p>Errors during portcullis events (i.e., @('.acl2') files) should now cause
 certification to fail; many books have been updated to avoid problems that
 were, until now, just being ignored.</p>

 <p>Various updates have been made to the Jenkins scripts to keep things up to
 date.</p>

 <p>For most Lisps, @(see build::cert.pl) will now include garbage collection
 messages in output logs files.  This may occasionally be useful when debugging
 performance issues.</p>

")


(defxdoc note-7-1-vl
  :parents (note-7-1-books)
  :short "Notes about changes to @(see vl) and @(see esim) in ACL2 Version
7.1."

  :long "<h3>VL Fork</h3>

 <p>There have been many changes to @(see vl) and @(see esim).  Most notably,
 VL has been forked into two versions.</p>

 <dl>
 <dt>@(see vl2014) is a ``stable'' fork of VL.</dt>
 <dd>It lives in a new directory: @('books/centaur/vl2014')</dd>
 <dd>It uses the @('VL2014') package.</dd>
 <dd>It continues to work with @(see esim) and other, older tools.</dd>
 <dd>It is no longer under active development by Centaur.</dd>

 <dt>@(see vl) continues as the ``development'' version of VL.</dt>
 <dd>It continues to live in: @('books/centaur/vl').</dd>
 <dd>It continues to use the @('VL') package.</dd>
 <dd>It <b>no longer supports @(see esim)</b>.</dd>
 <dd>It remains under active development.</dd>
 <dd>It targets a new backend (instead of esim) which is still under development.</dd>
 <dd>It may be rather unstable and not yet particularly usable.</dd>
 </dl>

 <p>The new @('vl') code base is in many cases significantly different than
 @(see vl2014).  It features a new, more strongly typed expression
 representation, generally better abstractions for working with
 scopes/hierarchy and types, and new approaches to elaboration and sizing that
 can handle much more of SystemVerilog.  More information on the motives and
 consequences of this split can be found in the documentation for @(see
 vl2014).</p>

 <p>Largely in support of this fork, many books have been reorganized.  Many
 books that are specific to the VL/ESIM flow have been moved into the ESIM
 directory:</p>

 @({
    centaur/vl/top.lisp --> centaur/vl/defmodules.lisp (with a stub)
    centaur/vl/defmodules.lisp --> centaur/esim/defmodules.lisp
    centaur/vl/translation.lisp --> centaur/esim/translation.lisp
    centaur/vl/toe --> centaur/esim/vltoe (filenames have been unsmurfed)
    centaur/vl/util/esim-lemmas.lisp --> centaur/esim/vltoe
    centaur/vl/transforms/occform/* --> centaur/esim/occform
 })

 <p>Various other files have also been moved into ESIM:</p>

 @({
    centaur/tutorial --> centaur/esim/tutorial
    centaur/vcd --> centaur/esim/vcd
    centaur/regression --> centaur/esim/tests
 })

 <p>Many other minor file-name changes have been made to help improve the
 organization of the code base.</p>

 <p>The various VL <i>flows</i> are also now better separated.  For
 instance:</p>

 <ul>

 <li>The ESIM flow no longer performs certain linter checks that are better
 handled by VL-Lint.  For instance, it no longer generates a classic
 use-set-report since the new Lucid reporting is much better.</li>

 <li>The @('vl model') command (based on the ESIM flow) is no longer used in
 the module browser.  Instead, the module browser now reads @('.vlzip') files
 that are produced by the @('vl zip') command, which is independent of
 ESIM.</li>

 </ul>


 <h3>Extended Support for Verilog/SystemVeriog</h3>

 <p>The new VL (and in some cases VL2014) now have better support for at least
 the following Verilog/SystemVerilog features:</p>

 <ul>
 <li>@('.*') connections that involve interface ports,</li>
 <li>@('return') statements in functions,</li>
 <li>@('inside') expressions like @('a inside {b, c, [d:e]}'),</li>
 <li>@('generate') constructs,</li>
 <li>System functions like @('$bits') and @('$clog2'),</li>
 <li>Unpacked dimensions in various contexts,</li>
 <li>Matched @('end : foo') style endings on blocks,</li>
 <li>Declarations on unnamed blocks,</li>
 <li>Typedefs with a single unpacked dimension, i.e., @('typedef ... foo_t [3]'),</li >
 <li>Ports whose expressions involve parameters,</li>
 <li>Scope expressions and other complex hierarchical expressions,</li>
 <li>Module level begin/end blocks (not in the spec but supported by simulators),</li >
 <li>Package imports in block statements, functions, and tasks,</li>
 <li>Certain complex assignment patterns,</li>
 <li>The @('`\"'), @('`\\`\\\"'), and @('``') escapes in @('`define') macros,</li>
 <li>Certain macro invocations in @('`include')/@('`ifdef') forms,</li>
 </ul>


 <h3>@(see vl::vl-lint) Improvements</h3>

 <p>The loader works harder to attach parse-time warnings to the appropriate
 modules.</p>

 <p>The new @(see vl::lucid) check is a far more capable check for unused,
 unset, and multiply driven wires, with proper understanding of SystemVerilog
 scoping.  The old use-set and multidrive warnings have been retired.</p>

 <p>Heuristic improvements have been made to leftright checking,
 extension/fussy size warnings for @(''1')/@(''0')/..., and duplicate instance
 checking involving interfaces and portless modules.  Extension warning
 heuristics are also now attachable.</p>

 <p>Improved the warning messages for zero-sized replications, overflowing
 integer literals, and generally for warnings where expressions involve
 parameters after unparameterization.</p>

 <p>Portcheck now warns about stylistically undesirable ports such as
 @('foo[3:0]').</p>

 <p>There is now a basic suite of system-level tests directed at the linter;
 see the @('linttest') directory.  These tests have shed light on many minor
 linter bugs.</p>")




(defxdoc note-7-0-books
  :parents (note-7-0 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 7.0 (January
 2015)"
  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 6.5 and 7.0.</p>

 <p>The <a
 href='https://github.com/acl2/acl2/wiki/Release-version-numbers'>acl2-books
 Wiki page on Release Version Numbers</a> gives the Git/SVN revision numbers
 corresponding to releases.  See also @(see note-7-0) for the changes made to
 ACL2 itself.  For additional details, you may also see the raw <a
 href='https://github.com/acl2/acl2/commits/master'>commit log</a>.</p>

 <h2>Organizational, Build System, and Name Changes</h2>


 <h3>Source Code Moved</h3>

 <p>The ACL2 Community Books and ACL2 System source code repositories have been
 merged into one repository and are now available at</p>

 <box><p><a
 href=\"https://github.com/acl2/acl2\">https://github.com/acl2/acl2</a></p></box>

 <p>See the @('Readme.md') file found there for more details.  See also the
 @(see git-quick-start) guide if you are interested in contributing.</p>



 <h3>Deleted Stubs</h3>

 <p>When we move a book, we often add a <b>stub</b> book in its previous
 location to help you transition your @(see include-book) commands.  The @(see
 build::cert.pl) build system prints warnings when a stub book is being
 included.</p>

 <p>Stub books have a lifespan of one release.  The following books were stubs
 in ACL2 6.5, so we've deleted them.</p>

 @({
      Previous Location                New Location
    ---------------------------------------------------------------
      str/*                            std/strings/*

      xdoc/portcullis                  std/portcullis
      std/osets/portcullis             std/portcullis
      std/bitsets/portcullis           std/portcullis
      std/strings/portcullis           std/portcullis

      coi/osets/instance               std/osets/instance
      coi/osets/computed-hints         std/osets/computed-hints

      centaur/bitops/sign-extend       centaur/bitops/fast-logext

    ---------------------------------------------------------------
 })


 <h3>Build System Changes</h3>

 <p>The @('arithmetic-2') library is no longer built by default when running an
 ordinary @('make').  All books that previously depended on @('arithmetic-2')
 have been transitioned to use @('arithmetic-3') instead.  If your own work
 depends on @('arithmetic-2'), you can still build these books, e.g., by running
 @('make arithmetic-2') in the @('books') directory.</p>

 <p>Many minor tweaks and cleanups have been made to the build system
 itself.</p>

 <ul>

 <li>@('cert.pl') now has better support for @(see
 provisional-certification).</li>

 <li>The @(see build::cert_param) mechanism, which is used by @(see
 build::cert.pl) to indicate that books have special requirements, is now
 documented.</li>

 <li>New @('cert_param') directives have been added to avoid certifying certain
 books on incompatible Lisps.</li>

 <li>@(see build::cert.pl) now better avoids overflowing the maximum number of
 arguments to shell commands on some platforms when certifying large numbers of
 books.</li>

 <li>The new @(':ignore-certs') feature of @(see include-book) is now used in
 special two-pass books like @('std/strings/defs-program.lisp'), and should help
 to make building these books more reliable.</li>

 <li>Hundreds of old Makefiles from the @(see books-certification-classic) era
 have been eliminated.  Some obsolete GCL-specific directives have also been
 eliminated.</li>

 <li>Installing @(see quicklisp) now works from behind a proxy.  See <i>Using a
 Proxy</i> in @(see books-certification) for details.</li>

 <li>The implementation of ``@('make everything')'' has been cleaned up.  In
 particular, it no longer sets @('USE_QUICKLISP=1') since this is not
 appropriate for some Lisps.</li>

 <li>The @('make clean') command now does a better job of cleaning up generated
 files.</li>

 </ul>

 <p>Numerous books have been patched up for better portability across Lisps and
 integration with ACL2(p).  For instance: In many cases, previous calls of @(see
 without-waterfall-parallelism) are no longer necessary, largely due to
 thread-safe memoization; several @(see oslib) functions have been extended to
 work on additional Lisps; many books with raw Lisp code now use @(see
 include-raw) for more portable compilation behavior across Lisps.</p>

 <p>Various other utilities have been made more reliable.</p>

 <ul>

 <li>For Emacs @('TAGS') users, the @('etags.sh') script has been improved to
 permit whitespace before definitions.</li>

 <li>For ACL2 packaging mechanisms, the @('fix-cert') utility has been improved
 and now includes scripts for moving ACL2 distributions.</li>

 </ul>

 <p>Supporting scripts for the <a href='http://jenkins-ci.org/'>Jenkins</a>
 continuous integration server can now be found in the @('build/jenkins')
 directory.  These scripts have received significant attention and can now
 support multi-configuration builds for checking ACL2 books compatibility with
 many host Lisps.</p>


 <h3>Name Conflict Resolution</h3>

 <p>Progress has been made toward resolving name clashes in order to be able to
 include more books together.  This work involves renaming certain lemmas and
 may require updates to your books.</p>

 <p>Arithmetic-2</p>

 <ul>
 <li>@('floor-mod-elim') no longer forces its hypothesis.</li>
 </ul>

 <p>Arithmetic-5</p>
 <ul>
 <li>@('floor-=-x/y') now has additional corollaries.</li>
 </ul>

 <p>IHS</p>
 <ul>
 <li>@('floor-mod-elim') no longer forces its hypothesis.</li>
 <li>@('floor-=-x/y') now has additional corollaries.</li>
 <li>@('justify-floor-recursion') has been renamed to @('floor-recursion').</li>
 <li>@('cancel-floor-+') has been renamed to @('cancel-floor-+-basic').</li>
 <li>@('cancel-mod-+') has been renamed to @('cancel-mod-+-basic').</li>
 <li>@('rationalp-mod') no longer requires @('(rationalp x)').</li>
 </ul>

 <p>COI/osets</p>

 <ul>

 <li>Many @('coi/osets') books are now just small wrappers around @('std/osets')
 books.</li>

 <li>COI's @('double-containment') rule has been renamed to
 @('double-containment-expensive').</li>

 </ul>


 <h3>Licensing Changes</h3>

 <p>Robert Krug's @('arithmetic-3') library of is now available under a
 BSD-3-Clause style license instead of the GNU General Public License.</p>

 <p>Several books contributed by David Rager, which were formerly released under
 the GNU General Public License or a BSD-3-Clause style license, are now instead
 released under a (more permissive) MIT/X11-style license.</p>

 <p>Several books contributed by Oracle, which were formerly released under the
 GNU General Public License, are now instead released under an MIT/X11-style
 license.</p>

 <p>The @(see ubdds) library and a few \"miscellaneous\" books have also been
 transitioned from the GNU General Public License to a 3-clause BSD style
 license.</p>

 <p>Several books in the @('coi') library, which previously lacked explicit
 license information, now have explicit MIT/X11-style licenses.</p>


 <h2>New Libraries and Documentation</h2>

 <p>The ACL2+Books manual has a great deal of new and improved content and many
 topics have been reorganized to provide a more coherent hierarchy.  Notably,
 all documentation in the legacy <i>defdoc</i> format has been rewritten into
 the @(see xdoc) format.  Some highlights:</p>

 <ul>
 <li>The @(see ihs) documentation has been considerably updated.</li>
 <li>The @(see defsort) macro is now documented.</li>
 <li>The @(see sneaky) documentation has been considerably expanded.</li>
 <li>Topics like @(see lists), @(see strings), @(see alists), etc., now
 group together some related @(see programming) functions.</li>
 </ul>

 <p>The ACL2 @(see Sidekick) is an experimental and very preliminary graphical
 add-on to ACL2.  It currently features a session viewer, theory linter, a
 horribly primitive interface to the @(see proof-builder), and a slick
 <i>Lookup</i> feature that can show you documentation and other information
 about various symbols.</p>

 <p>The new @('system/toothbrush') directory provides a way to create
 applications with ACL2 that have a much smaller memory footprint than an
 ordinary ACL2 @(see save-exec) image.  See the @('README') file in this
 directory for more information.</p>

 <p>The new @(see depgraph::depgraph) library now contains a few algorithms for
 working with dependency graphs.  It provides @(see depgraph::toposort), a
 topological sort, @(see depgraph::invert), an edge-inversion algorithm, and
 @(see depgraph::transdeps), which can compute the transitive dependencies for a
 set of nodes.  This functionality was formerly part of @(see VL) but has now
 been made more general and extracted.</p>

 <p>The new @('projects/codewalker/') directory contains Codewalker, a utility
 for exploring code in any programming language specified by an ACL2 model to
 discover certain properties of the code.  Demos of Codewalker are also in that
 directory.</p>

 <p>The new directory @('projects/hybrid-systems/') is a
 specification/verification project by Shant Harutuntian using ACL2(r) (see
 @(see real)), in support of his 2007 Ph.D. dissertation, with a few recent
 updates (because of ACL2 changes) made by Cuong Chau.</p>

 <p>There are also several new small tools and books.</p>

 <ul>

 <li>(CCL Only) The new @(see spacewalk) tool can be used to get a report about
 heap memory usage.  It may be useful for identifying unusually large functions
 and constants in your ACL2 session.</li>

 <li>The new @(see simp) tool can be used to ask ACL2 to simplify terms under
 certain hypotheses.</li>

 <li>The new tool @('misc/check-fn-inst') can be used to check the constraints
 to a functional instantiation.</li>

 <li>The new tool, @(see def-saved-obligs), can be used to save proof
 obligations for an event as independent defthms.</li>

 <li>The new tool, @('system/dead-source-code.lisp'), may be useful
 for finding dead code in the ACL2 sources.</li>

 <li>The new books @('system/cantor-pairing-bijective.lisp') and
 @('system/hl-nat-combine-onto.lisp') contain proofs of bijectivity and
 surjectivity (one-one/onto and onto, respectively) of cantor-pairing
 functions.</li>

 </ul>

 <h2>Changes to Major Libraries</h2>

 <h3>XDOC Changes</h3>

 <p>The web-based XDOC viewer has been improved.  It now uses newer versions of
 the JQuery and Typeahead libraries.  Some bugs with the typeahead (jump to) box
 have been fixed and it has been extended to show more results.  The jump-to box
 has been extended with a @('Alt+/') hotkey (or perhaps some other key
 combination like @('Ctrl+/'), depending on your browser).  Middle clicking on
 XDOC links should now properly open them in new tabs and the fonts have been
 updated.  Some ugly quotes are now replaced by ``smart'' replacements.</p>

 <p>Significant work has been done to try to make XDOC content accessible to
 search engines such as Google.  A new PHP script largely replaces previous
 failed efforts to generate \"static\" HTML files, site maps, and so forth.</p>

 <p>XDOC now supports \"resource directories\" for incorporating images, PDF
 files, and other kinds of resources.  See @(see xdoc::add-resource-directory)
 for details.</p>

 <p>XDOC now features @(see xdoc::katex-integration) for writing LaTeX-like
 formulas like @($ \\left( \\sum_{i=0}^{n} \\sqrt{f(i)} \\right) <
 \\frac{n^2}{k} $) within your documentation.  Note that ACL2's new @(see
 fancy-string-reader) can be used to make escaping simpler, and this may be
 especially useful when trying to write LaTeX-like formulas, where the escaping
 of @('\\') characters can be irritating.</p>

 <p>There are also many other minor changes:</p>

 <ul>

 <li>The @(see defpointer) macro has been integrated into XDOC itself.  (It was
 formerly only part of the ACL2 system documentation.)</li>

 <li>@(see defsection) and @(see define) now permit plain strings to be included
 among the list of events.  These strings are incorporated into the resulting
 documentation as running commentary.</li>

 <li>The @(see defxdoc), @(see defsection), and @(see define) macros now all
 evaluate the arguments to @(':short') and @(':long') instead of quoting them.
 This may make it more convenient to write macros that produce documentation
 from boilerplate templates, e.g., you can now directly write things like
 @(':short (cat ...)').</li>

 <li>Tweaked @(see defsection) so that you can give @(':extension (foo)')
 instead of just @(':extension foo.')</li>

 <li>Better error handling on @(see xdoc::xdoc-extend) and @(see
 xdoc::xdoc-prepend).</li>

 </ul>



 <h3>@(see STD) Library Changes</h3>


 <h5>@(see std/basic)</h5>

 <p>Added @(see tuplep) and @(see impossible).</p>


 <h5>@(see std/lists)</h5>

 <p>Cleaned up rules about take in @(see std/lists/take).</p>

 <p>@(see replicate) is now an alias for @(see repeat) and is compatible with
 the definition of @('repeat') in the COI libraries, fixing a longstanding
 incompatibility.</p>

 <p>The @(see all-equalp) function has been added.</p>

 <p>Several lemmas about @(see intersection$), @(see intersectp), and @(see
 set-difference$) have been extracted from @(see vl) and moved into
 @('std/lists').  See for instance @(see std/lists/intersection$),
 @(see std/lists/intersectp), and @(see std/lists/set-difference).</p>




 <h5>@(see std/util)</h5>

 <p>The @(see b*) binders for @(see std::defaggregate)s now also bind the
 variable, fixing a longstanding issue.  Also, the syntax @('((prodname name))')
 is now permitted as an abbreviation for @('((prodname name) name)').  (This is
 often useful when destructuring a function's arguments).</p>

 <p>The @(see b*) binders for @(see std::defaggregate) (and also @(see
 fty::defprod)) are now extensible and can translate bindings like @('x.foo')
 into calls of user-defined functions.  See the description of <i>Extra Binder
 Names</i> in the documentation of @(see std::defaggregate) for details.</p>

 <p>The @(see std::deflist), @(see std::defalist), @(see std::defprojection),
 and @(see std::defmapappend) macros are now \"pluggable\" and can be extended
 with additional theorems; see for instance the new book
 @('std/lists/abstract.lisp').</p>

 <p>The new books @('std/util/deflist-base') and @('std/util/defalist-base')
 offer lighter-weight alternative to @('std/util/deflist') and
 @('std/util/defalist').</p>

 <p>The @(see std::defrule) book now has fewer dependencies.</p>

 <p>Documentation for @(see std::deflist) has been improved.  @('Deflist') now
 uses @(see define) so that you get a signature block in the resulting
 documentation.  The documentation for automatically generated deflist events is
 now put in a more sensible order and split off into a @('foolistp-basics')
 section underneath of @('foolistp'), to reduce the prominence of this
 \"boilerplate\" documentation.  Deflist can now also create documentation even
 in the @('already-definedp') case.</p>

 <p>Fixed an obscure bug with @(see define)'s return-specifiers that could
 affect non-executable functions that involve stobjs.</p>

 <p>The @(see define) macro now interprets @(':inline nil') as \"make this a
 <see topic='@(url defun-notinline)'>$notinline</see> function\" instead of
 \"make this a regular function instead of an <see topic='@(url
 defun-inline)'>inline</see> one.\"</p>

 <p>The @(see define), @(see defines), and also the @(see fty::deffixequiv)
 macros now have improved, more advanced default hints set for inductive proofs
 in return specs and @('deffixequiv(-mutual)') forms.</p>


 <h5>@(see std/strings)</h5>

 <p>Certification time has been improved.</p>

 <p>The @('fast-cat') book (see @(see str::cat)) now uses @(see include-raw) to
 avoid possible issues on various Lisps.</p>

 <h5>@(see std/io)</h5>

 <p>Added @(see read-file-as-string) function.</p>

 <h5>@(see std/alists)</h5>

 <p>There are some new functions: @(see fal-find-any) and @(see
 fal-all-boundp).</p>

 <p>Moved @(see worth-hashing) into @('std/alists') from
 @('misc/hons-help').</p>

 <h5>@(see std/typed-lists)</h5>

 <p>Move @(see cons-listp) and @(see cons-list-listp) out of VL and into
 @('std/typed-lists').</p>



 <h3>Defdata (Data Definition Framework)</h3>

 <p> @('Defdata') has undergone significant improvements.  Automated theorem
 proving support has been increased by a tight integration with @(csee
 Tau-system).  A significant new capability is the support for parametric
 polymorphism via @('sig') rules. There have been many improvements in its
 engineering too.</p>

 <h5>Tau Integration</h5>
 <p>
 Defdata analyzes the predicate definition of every new type and, if
 possible, produces a set of Tau rules that completely characterize
 the type. Defdata thus provides the following guarantee: If Tau is
 complete over the type reasoning theory, then adding a type to the
 current theory via @('defdata') preserves completeness.
 </p>

 <h5>Parametric Polymorphism</h5>
 <p>
 Defdata provides a new macro @('sig') which can be used to define
 signatures of polymorphic functions
 such as <tt>append</tt>, <tt>remove1</tt>, <tt>put-assoc</tt> etc:
 </p>
 @({
   (sig append ((listof :a) (listof :a)) => (listof :a))
   (sig remove1-equal (all (listof :a)) => (listof :a))
   (sig put-assoc-equal (:a :b (alistof :a :b)) => (alistof :a :b))
 })

 <p>
 Defdata automatically instantiates these generic theorems
 (type signatures) for previously defined types and as new types are defined
 after the @('sig') forms. Defdata, thus implements parametric polymorphism, by
 providing the following invariants:</p>

 <ul>
 <li> Every new defdata type is instantiated for every polymorphic
      signature (specified via sig) that matches (one of its argument
      types).</li>
 <li> Every new polymorphic signature is appropriately instantiated for
      all defdata types of the right shape in the current world. </li>
 </ul>

 <p> Dependent type hypotheses are supported by @('sig') -- e.g. the
 polymorphic signature of <tt>nth</tt> is specified as follows.  </p>

 @({
   (sig nth (nat (listof :a)) => :a
        :satisfies (< x1 (len x2)))
 })

 <h5>Other Theory Reasoning</h5>

 <p>Theory support for Records (structs) and Maps has been tuned to be more
 robust. Destructor Elimination is now available for records.</p>

 <h5>Advanced Usage</h5>
 <p>
 @('Defdata') has been re-engineered to have a plug-in like
 architecture. The following macros provide ways to extend the Defdata
 language and its semantics.</p>
 <dl>
 <dd> @('register-type') -- Register a name as a defdata type (with its associated metadata).</dd>
 <dd> @('register-data-constructor') -- Register a data constructor (for product types).</dd>
 <dd> @('register-user-combinator') -- Add user-defined syntactic sugar to the defdata language.
 e.g. <i>alistof</i> was added with minimal coding overhead using this facility (See defdata/alistof.lisp).</dd>
 <dd> @('defdata-attach') -- Replaces/subsumes) defdata-testing; it can be used to change or add defdata type metadata. </dd>
 </dl>


 <h3>Defsort</h3>

 <p>The interface to @(see defsort) has been extended, and it can now reuse
 existing list recognizers.</p>

 <p>Defsort can now (optionally) prove that the new sorting function is
 equivalent to an insertion sort.</p>

 <p>Defsort now allows extra arguments, e.g., to parameterize the sort.</p>



 <h3>Tools</h3>

 <p>The @(see include-raw) utility has been made more robust.  It now checks the
 write-date of compiled files, to avoid including stale files.</p>

 <p>The utilities @(see profile-acl2) and @(see profile-all) now work in the
 ACL2 loop, and are documented.</p>

 <p>The @('watch') utility works again.  Thanks to Bob Boyer for providing
 fixes.  To use this utility:</p>

 @({
    (include-book \"centaur/memoize/old/watch\" :dir :system :ttags :all)
    :q
    (watch)
    (lp)
    ; Now in Emacs, bring into a buffer the file reported by (watch), whose
    ; name is of the form watch-output-temp-n.lsp.  Then execute ACL2 forms.
 })

 <p>The @(see untranslate-patterns) tool is now compatible with @(see define)'s
 @(see untranslate-preprocess) hook.</p>


 <h3>OSLIB</h3>

 <p>OSLIB has been reorganized to try to make it somewhat more coherent.  Most
 files in oslib are now split up into, e.g., argv-logic.lisp (no raw code or
 ttags) and argv.lisp (actual implementation).</p>

 <p>OSLIB has new functions including @(see oslib::dirname), @(see
 oslib::basename), @(see oslib::copy), and @(see oslib::catpaths).</p>

 <p>The @(see oslib::ls), @(see oslib::ls-files), and @(see oslib::ls-subdirs)
 functions have been improved to return better error information, and made more
 portable across Lisps.</p>

 <h3>Tau</h3>

 <p>The book @('tau/bounders/elementary-bounders') has been improved by adding
 guards, thanks to Dmitry Nadezhin.</p>

 <h2>Changes to Centaur Libraries</h2>

 <h3>@(see bitops)</h3>

 <p>The new @(see bitops::bitops/part-install) macro can be used to set particular bits of an
 integer to a value.  It is somewhat similar to utilities like @(see wrb) from
 the IHS library, but its interface is perhaps more intuitive.</p>

 <p>The new @(see bitops::bitops/fast-rotate) macros provide optimized versions of @(see
 rotate-left) and @(see rotate-right).</p>

 <p>The new @(see bitops::bitops/logbitp-bounds) book provides a few lemmas relating
 @(see logbitp) to @(see expt).</p>


 <h3>@(see fty::fty)</h3>

 <p>The @(see std::deflist) and @(see fty::deflist) books are now integrated, so
 that @('fty::deflist') can provide the ordinary @('std::deflist') theorems.
 The @('fty::deflist') and @('fty::defalist') macros now provide at least @(see
 append) theorems by default.</p>

 <p>The documentation-generating macros have been enhanced.</p>

 <p>The @(see fty::deftypes) macro now uses more aggressive theory management to
 speed up certification, and also has more comprehensive error checking.</p>

 <p>The @(see fty::deffixtype) macro has better error checking.</p>

 <p>The cases macros introduced by @(see fty::deftypes) now support an
 @(':otherwise') case.</p>

 <p>The @(see fty::deftypes) @('make-') macros now disallow duplicated
 keywords.</p>

 <p>The @(see fty::deflist) and @(see fty::defalist) macros can now tolerate
 already-defined predicates.</p>

 <p>The @(see fty::basetypes) book has been filled out a bit, e.g., it now includes
 @(see maybe-natp).</p>

 <p>By default, @(see fty::deffixtype) now verifies the guards on the equivalence
 relations it introduces.</p>

 <h3>@(see Quicklisp)</h3>

 <p>Quicklisp can now read proxy information from the @('HTTP_PROXY_WITH_PORT')
 environment variable.  See also the \"Using a proxy\" page in @(see
 books-certification).  BOZO move that into Quicklisp?  Blah, all this stuff
 always ends up duplicated everywhere.</p>

 <p>Quicklisp now includes books for loading the @('uiop') library and a more
 sensible @('cl-fad') book.  These libraries may be useful for doing file system
 things.  The CCL-only restrictions on @('bordeaux-threads') and
 @('hunchentoot') have been dropped since these libraries seem to be working
 fine on modern SBCL distributions.  A book for the @('html-template') library
 has also been added.</p>

 <p>The Quicklisp build should be more robust.  It now checks for existing
 Quicklisp installations and produce a sensible error message instead of dying
 horribly.</p>


 <h3>Other</h3>

 <p>The @(see getopt) library now has a basic test suite.</p>

 <p>The @('centaur/misc/sharedlibs') code for relocating shared libraries has
 been extended with a test/demo script.  The sharedlibs functions no longer
 cause errors when used on non-CCL Lisps (they simply print a message,
 instead.)</p>

 <p>The @(see template-subst) tool has been expanded with some additional
 functions.</p>

 <p>The @(see profile-all) and @(see profile-acl2) functions can now be used
 from within the ACL2 loop instead of only from raw Lisp.</p>

 <p>The @(see flag::def-doublevar-induction) macro has been extended and improved.</p>

 <p>For @(see esim), there is a new tool for @(see stv) decomposition theorems,
 @('oracle/stv-decomp-theory-expander.lisp'), and a demo of using this tool in
 @('centaur/regression/composed-stv.lisp').  The documentation tables for STVs
 should now look nicer in the printer-friendly xdoc view.</p>

 <p>In the @(see 4v) library, there are a few new @(see *sexpr-rewrites*).</p>

 <p>Minor bug-fix to avoid complaint in an @(see aignet) @('bind-free')
 routine.</p>

 <p>Added @(see satlink::gather-benchmarks), a plugin for collecting DIMACS
 files that SATLINK sends to the SAT solver. You could use this to gather
 benchmarks for evaluating SAT solvers or for the SAT solving competitions.</p>

 <p>In @(see gl), fixed a bug in @('trace-gl-interp').</p>



 <h3>VL Changes</h3>

 <p>VL has undergone significant extensions and changes, mostly toward extending
 VL to support a subset of SystemVerilog.  VL is intended to also still support
 Verilog-2005, and in many cases its Verilog-2005 support has been improved as
 new SystemVerilog features have been implemented.  Some highlights:</p>

 <ul>

 <li>VL now has a more extensive \"systest\" suite for checking its work against
 NCVerilog and VCS, and a preliminary \"failtest\" suite for ensuring that
 certain modules with bad constructs are properly rejected.</li>

 <li>Added parsing support for many constructs such as interfaces, packages,
 generate statements, structs, unpacked arrays, etc.  The parser functions now
 pass around a \"parse state\" object and generates warnings in a more coherent
 way.  This results in certain speedups to its certification and allows for
 distinguishing the names of data types from other identifiers, which is
 necessary for parsing certain constructs.</li>

 <li>More comprehensive parameter support.  This involved reworking
 unparameterization to handle SystemVerilog data types, and adding support for
 richer expressions in wire ranges, etc., by reworking how constant expressions
 are evaluated to handle many more operators and operands of mixed sizes/types.
 Generate statements are also now supported to some degree.</li>

 <li>Added support for fancier ports, e.g., ports with data types, module
 instances with @('.name') and @('.*') style connections, and interface
 ports.</li>

 <li>Added support for combinational user-defined primitives, and at least basic
 parsing support for sequential UDPs.</li>

 <li>Added some support for SystemVerilog packages and imports.  A new
 \"scopestack\" abstraction is now widely used to provide more comprehensive
 handling of nested scopes (e.g., named begin/end blocks), packages, etc.  There
 is now some support for functions defined at the global scope.</li>

 <li>Sizing has been extended to handle unpacked arrays.  The sizing code has
 been reorganized to be more modular, and extended to handle additional
 operators.</li>

 <li>Miscellaneous improvements.  The pretty-printer has been extended to handle
 the new SystemVerilog constructs, ansi-style ports, etc.  Some transforms are
 more configurable, e.g., gate elimination can easily use alternate replacements
 for gate instances.  There is better support for @('case') statements,
 especially in @('always_comb') blocks.  Various operators are now supported to
 various degrees, e.g., @('++'), casting operators, @('$bits'), streaming
 concatenations.  The preprocessor now supports @('`define') macros with
 arguments.  The hierarchy tools have been greatly simplified.</li>

 <li>Numerous organizational changes, bug fixes, and updates to existing tools
 and transforms to keep things working.</li>

 </ul>

 <p>Besides these improvements to the core library, there have been various
 user interface improvements.  For instance, the @(see vl::vl-server) has been
 entirely rewritten and is now included in the @(see vl::kit); it allows you to
 view Verilog modules in a web browser.  The loader has been made more
 user-friendly and more gracefully handles search paths, errors, etc.  The
 @(see vl::vl-lint)er has been tweaked to provide better output and to run more
 quickly.</p>")



(defxdoc note-6-5-books
  :parents (note-6-5 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 6.5 (August
 2014)."

  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 6.4 and 6.5.</p>

 <p>The <a
 href='https://code.google.com/p/acl2-books/wiki/ReleaseVersionNumbers'>acl2-books
 Wiki page on ReleaseVersionNumbers</a> gives SVN revision numbers corresponding
 to releases.  See also @(see note-6-5) for the changes made to ACL2 itself.
 For additional details, you may also see the raw <a
 href='http://code.google.com/p/acl2-books/source/list'>commit log</a>.</p>



 <h2>Organization, Build, and Licensing Changes</h2>

 <h3>Deleted Stubs</h3>

 <p>When we move a book, we often add a <b>stub</b> book in its previous
 location to help you transition your @(see include-book) commands.  The @(see
 build::cert.pl) build system prints warnings when a stub book is being
 included.</p>

 <p>Stub books have a lifespan of one release.  The following books were stubs
 in ACL2 6.4, so we've deleted them.</p>

 @({
      Previous Location                         New Location
    ------------------------------------------------------------------
      cutil/*.lisp                              std/util/*.lisp
      tools/defconsts                           std/util/defconsts

      parallel/with-waterfall-parallelism       misc/with-waterfall-parallelism
      parallel/without-waterfall-parallelism    misc/without-waterfall-parallelism

      serialize/unsound-read                    std/io/unsound-read

      centaur/bitops/bitsets                    std/bitsets/bitsets
      centaur/bitops/bitsets-opt                std/bitsets/bitsets-opt
      centaur/bitops/sbitsets                   std/bitsets/sbitsets
    ------------------------------------------------------------------
 })


 <h3>Book Reorganization</h3>

 <p>We've moved several books to new homes in an effort to improve the overall
 organization of the books.  Users of these libraries will need to update their
 @(see include-book) commands, and in some cases, packages have also
 changed.</p>

 <p>The table below shows which libraries have moved and where they have moved
 to.  Books with stubs may continue to work until the next release, but you'll
 need to update your @('include-book')s eventually.</p>


 @({
    Stubs?     Previous Location        New Location
   ----------------------------------------------------------------------
     Yes       str/                     std/strings/

     No        memoize/                 centaur/memoize/

     No        centaur/doc.lisp         doc/top.lisp

   ----------------------------------------------------------------------
 })

 <p>The @(see defpkg) commands for @(see xdoc), @(see std/strings), @(see
 std/osets), and @(see std/bitsets) have been merged into a single
 @('std/package.lsp') file, with a single corresponding @('std/portcullis.lisp')
 file, to simplify package management.</p>


 <h3>Name Conflict Resolution</h3>

 <p>Preliminary work has been carried out toward unifying coi/std versions of
 osets.  In particular:</p>

 <ul>
 <li>The @(see std/osets) package has been changed from @('SETS') to @('SET').</li>
 <li>The @('coi/osets') library now uses the @('std/osets') package files.</li>
 <li>Some @('coi/osets') books now merely include the corresponding files from
 @('std/osets').</li>
 </ul>

 <p>The @(see std/lists) function @('repeat') has been renamed to @(see
 replicate), and had its arguments reordered, to resolve a name clash with the
 coi library.  See <a
 href='https://code.google.com/p/acl2-books/issues/detail?id=136'>Issue 136</a>
 for additional discussion about this change.</p>

 <p>The @('data-structures') library @('STRUCTURES') package has been renamed to
 @('DEFSTRUCTURE') to resolve a name conflicts with the COI books.</p>

 <p>The @(see bitops) library's @('sign-extend') function has been renamed to
 @(see fast-logext) to resolve a name conflict with the @(see rtl)
 library.</p>

 <p>The new @('tools/book-conflicts') tool can be used to detect name conflicts
 between books.  See its @('README') file for more information.</p>


 <h3>Build System Changes</h3>

 <p>Support for ACL2(r) is now directly included in the top-level Makefile.
 ACL2(r) users no longer need to use a separate build process and can now make
 use of many additional books.  Books that are incompatible with ACL2(r) should
 be annotated with @('non-acl2r') @('cert_param')s, and books that require
 ACL2(r) should have a @('uses-acl2r') cert_param.</p>


 <p>The top-level Makefile has been made more robust in various ways.</p>

 <ul>

 <li>Certification of books under @('models/y86') has a cleaner implementation.
 These books are no longer certified by the @('make') target @('all') since they
 are resource intensive.  For ACL2(h) and host Lisps that can handle this task,
 they are certified by using the target @('everything').  Also, the value of the
 @('-j') option of the @('make') command is no longer ignored.</li>

 <li>It no longer tries to build certain long-running books when USE_QUICKLISP
 is set and Hons is not present.</li>

 <li>It no longer tries to build the @(see gl) solutions book, as this can
 overwhelm modest machines.</li>

 <li>A new @('ccl-only') @('cert_param') can be used for books that require CCL.
 Used this to avoid trying to certify certain books that require, e.g., @(see
 tshell).</li>

 <li>The @(see esim-tutorial) books have been removed from @('doc/top.lisp') to
 avoid requiring Glucose to build the ACL2+Books manual.</li>

 <li>Certain problematic books have been annotated with @(see
 non-parallel-book), to avoid incompatibilities with @(see
 waterfall-parallelism) problems on ACL2(p).</li>

 </ul>


 <p>The @(see build::cert.pl) build system has been enhanced in many ways.  Of
 particular note, it now deals more automatically with portcullis files, which
 may help to improve the reliability of including uncertified files.  Other
 improvements include:</p>

 <ul>
  <li>Better support for generated books</li>
  <li>Support for ACL2 images that start up in other packages</li>
  <li>Enhanced @('--help') message with more information</li>
  <li>Added support for @(see add-include-book-dir!)</li>
  <li>More informative error messages in certain cases</li>
  <li>Miscellaneous, minor bug fixes, e.g., support for @('$') in book names.</li>
 </ul>


 <p>The build speed has been improved in various ways.</p>

 <ul>

 <li>Many books have reordered @(see include-book) to take advantage of new
 optimizations in ACL2.</li>

 <li>The performance of the @('tau/bounders/elementary-bounders') book has been
 significantly improved, reducing the critical path time for the @('make all')
 target.</li>

 <li>A computationally expensive proof has been split out of the
 @('defung-stress') book, also substantially improving the critical path for
 @('make all').</li>

 <li>Reduced dependencies in @(see std/util), @(see std/lists), @(see
 std/alists), and @(see xdoc) to speed up certification.</li>

 </ul>

 <p>Added a TAGS target to the Makefile.</p>

 <p>Added scripts to support using a <a
 href='http://jenkins-ci.org/'>Jenkins</a> continuous integration server to
 continually rebuild ACL2 and the books on various platforms.</p>


 <h3>Licensing Changes</h3>

 <p>Books contributed by Computational Logic, Inc. are now licensed under
 a (more permissive) 3-clause BSD style license instead of the GNU General
 Public License.</p>

 <p>Books contributed by Centaur Technology, Inc. are now licensed under a (more
 permissive) MIT/X11 style license instead of the GNU General Public
 License.</p>

 <p>Books contributed by Jared Davis / Kookamara are now licensed under an
 MIT/X11 style license instead of the GNU General Public License.</p>

 <p>Many books that lacked explicit licensing information have been updated to
 include appropriate copyright headers.</p>


 <h2>New Libraries, Demos, and Documentation</h2>

 <h5>New Libraries and Tools</h5>

 <p>The @('workshops/2014') directory contains contributions from the ACL2
 Workshop for 2014.</p>

 <p>The new @(see remove-hyps) tool may be useful for identifying unnecessary
 hypotheses in theorems.</p>

 <p>@(see fty::fty) is a new library offers functionality similar to @(see std)
 or @(see defdata) libraries.  This library enforces a certain fixing-function
 discipline and may help to avoid many type-like hypotheses on theorems.</p>

 <p>The new book @('tools/rewrite-with-equality.lisp') is a certified clause
 processor that causes certain equality hypotheses to cause massive substitution
 of the \"good\" term for the \"bad\" term in clauses that are stable under
 simplification.</p>

 <p>The new @(see with-supporters) macro can be used to automatically produce
 redundant versions of events that are needed from local include books.</p>

 <p>The new @(see flag::def-doublevar-induction) macro can be used to create
 certain kinds of induction schemes, and may be especially useful for proving
 @(see congruence) rules about mutually recursive functions.</p>

 <p>The new @(see nrev) book is something like @('nreverse').  It can be used to
 implement in-order, tail-recursive list processing functions.  With a trust
 tag, these functions can avoid the memory overhead of a final @(see
 reverse).</p>

 <p>The new @(see fast-alist-pop) function provides something akin to
 @('remhash') for fast alists, with various restrictions and limitations.</p>

 <p>The new @('system/hons-check') books provide some basic tests for the @(see
 hons-and-memoization) code.</p>

 <p>The new @('oracle/') directory contains tools and examples from Oracle,
 Inc.</p>

 <h5>New Demos</h5>

 <p>A new demo, @('demos/tutorial-problems/equivalence-of-two-functions'), shows
 some ways to prove the equivalence of two functions that recur in different
 ways.</p>

 <p>A new demo, @('demos/knuth-bendix-problem-1.lisp'), has been added.</p>

 <p>COI's @('defung') has a new fractran example: see
 @('coi/defung/fractran.lisp').</p>

 <p>A new demo, @('demos/gl-and-use-example.lisp'), shows a way to use GL to
 establish the crux of an unbounded theorem.</p>


 <h5>New Documentation</h5>

 <p>The @('cowles'), @(see arithmetic-1), and @(see rtl) libraries now
 have some XDOC documentation.</p>

 <p>There are now some preliminary recommendations for @(see best-practices) for
 developing ACL2 books.</p>

 <p>The documentation for portions of the @(see ihs) library and @(see plev) had
 been inadvertently excluded from the manual, but are now included.</p>

 <p>A new topic describes some noteworthy @(see clause-processor-tools).</p>

 <p>The topic hierarchy has received some attention, e.g., all topics that were
 formerly listed under the grab-bag @('switches-parameters-and-modes') have been
 relocated to more suitable homes.</p>

 <p>Converted the documentation for @(see esim), @(see b*), and other topics
 into @(see xdoc) format.</p>

 <p>Many topics have been improved by eliminating typos, making minor
 clarifications, adding appropriate cross-references, fixing broken links, and
 ensuring that @(':parents') are correct.</p>



 <h2>Changes to Major Libraries</h2>

 <h3>XDOC Changes</h3>

 <p>The new @(see xdoc::order-subtopics) command can be used to control the
 order that subtopics are presented in.</p>

 <p>The \"classic\" XDOC viewer is no longer supported.</p>

 <p>The XDOC viewers have been improved in many ways.</p>

 <ul>

 <li>Fancy manuals now produce a clear error message for users of IE8 and IE9,
 and will work properly for users of IE11.  (IE10 still works, as before).</li>

 <li>Fancy manuals now load much more quickly (faster jump-to box
 initialization).</li>

 <li>The :doc command and the @(see acl2-doc) tool now show URLs for external
 links.</li>

 <li>XDOC now includes tools that can create a <a
 href='http://www.sitemaps.org/'>sitemap</a> and other \"static\" HTML files,
 which may be useful for search engine optimization.</li>

 <li>Added @('.htaccess') files to fancy manuals, which can enable server-side
 compression for significant file size/performance improvements.</li>

 </ul>


 <p>Various bugs have also been fixed in the core XDOC system.</p>

 <ul>

 <li>The @('@(def ...)') directive sometimes printed the wrong event; this has
 been fixed.  It also now handles mutually recursive functions more nicely.</li>

 <li>The @(see xdoc::save) command should no longer cause an error when trying
 to write manuals to paths like @('~/my-manual').</li>

 <li>Fixed bugs in XDOC's handling of <tt>@@('...')</tt> and <tt>@@({...})</tt>
 directives, and otherwise improved error messages with more context.</li>

 <li>Fixed a problem with @(see xdoc::xdoc-extend) when the topic to extend
 lacked a @(':long') string.</li>

 </ul>

 <p>Other minor changes:</p>

 <ul>

 <li>XDOC now uses @(see str::pretty) instead of @(see fmt-to-string) and the
 preprocessor uses @(see state) less than before.</li>

 <li>Factored xdoc tests out of the main directory and excluded them from the
 basic build, to improve build times.</li>

 </ul>



 <h3>@(csee Std) Library Changes</h3>

 <h5>@(see std/basic)</h5>

 <p>A new book of basic @(see induction-schemes) has been added.</p>

 <p>Certain equivalence relations like @(see chareqv) and @(see streqv) have
 been factored out of the @(see std/strings) library and moved into
 @('std/basic') instead, mainly to improve integration with the new @(see
 fty::fty) library.</p>

 <p>@(see lnfix) and @(see lifix) are now enabled, inlined functions instead of
 macros.  This may help to simplify guard obligations in functions that call
 @('lnfix') and @('lifix').</p>


 <h5>@(see std/lists)</h5>

 <p>An @(see std/lists/update-nth) book has been added.</p>

 <p>A @('remove-duplicates') book has been added with lemmas about @(see
 remove-duplicates-equal) and @(see hons-remove-duplicates).</p>

 <p>Added a missing rule about @(see acl2-count) to
 @('std/lists/acl2-count').</p>

 <p>@(see uniquep) no longer uses @(see equality-variants).  Theorems that
 target @('uniquep') should be rewritten in terms of @('no-duplicatesp').</p>

 <p>Various books have been reorganized to reduce dependencies.</p>


 <h5>@(see std/alists)</h5>

 <p>The general purpose alist functions @(see append-alist-vals) and @(see
 append-alist-keys) have been moved out of @(see vl) and into @(see
 std/alists).</p>

 <p>There are new books for @(see alist-fix) and @(see hons-remove-assoc).</p>

 <p>The new @('fast-alist-clean') book includes lemmas about @(see
 fast-alist-fork) and @(see fast-alist-clean).</p>

 <p>Various books have been reorganized to reduce dependencies.</p>


 <h5>@(see std/osets)</h5>

 <p>Most osets functions are now disabled by default.  They can be re-enabled
 using the ruleset @('set::definitions').</p>

 <p>Some useful but sometimes expensive rules, including for instance the @(see
 set::pick-a-point-subset-strategy) and @(see set::double-containment), and also
 including other rules such as the transitivity of @(see set::subset), are now
 disabled by default.  They can be re-enabled using the ruleset
 @('set::expensive-rules').</p>


 <h5>@(see std/util)</h5>

 <p>Some new macros have been added.</p>

 <ul>

 <li>@(see std::defines) can introduce mutually recursive functions, using a
 @(see std::define)-like syntax, and features automatic integration with @(see
 make-flag).</li>

 <li>@(see std::defval) is like @(see defconst) but has @(see xdoc) integration.</li>

 <li>@(see std::defsum) is a preliminary macro for tagged union types.</li>

 <li>@(see std::defaggrify-defrec) adds @(see std::defaggregate)-style emulation
 for structures introduced using @('defrec').</li>

 </ul>


 <p>The @(see std::define) macro has been improved in many ways.</p>

 <ul>

 <li>It has been modified to make it easier to extend, largely in support of
 @(see std::defines).</li>

 <li>It now uses @(see with-output) to avoid printing so much output.</li>

 <li>Theorems introduced by @(see std::returns-specifiers) now often have better
 names, and the name can also be controlled using @(':name').</li>

 <li>The new @(see std::more-returns) macro allows for additional @(see
 std::returns-specifiers) style theorems after a @('define').</li>

 <li>A performance bug with the @(see std::var-is-stobj-p) function, notably
 used by @('define'), has been fixed.</li>

 <li>Experimental <i>post-define hooks</i> can allow for custom actions to be
 carried out after submitting a @('define'); such a hook allows for a tight
 integration between @('define') and the new @(see fty::fty) library.</li>

 <li>New options allow you to avoid introducing an encapsulate and to name and
 save the termination proof.</li>

 </ul>

 <p>Other macros have also been improved in various ways.</p>

 <ul>

 <li>@(see std::defredundant) tool has been expanded to better handle @(see
 mutual-recursion) and <see topic='@(url macro-aliases-table)'>macro
 aliases</see>.</li>

 <li>@(see std::defmvtypes) now has smarter handling of @(see force).</li>

 <li>@(see std::defenum) now automatically produces a fixing function and
 forward-chaining rule to give the possible values of the objects.</li>

 <li>@(see std::defrule) now has a @(':local') option.</li>

 <li>@(see std::deflist) is now smart enough to tell whether functions are
 defined; its former @(':already-definedp') option is now useless and, hence,
 deprecated.</li>

 <li>@(see std::defprojection) now uses @(see nrev::nrev) instead of optimizing
 things with @('nreverse') directly, reducing the use of trust tags.</li>

 <li>@(see std::defprojection) now accepts @(see std::define)-like syntax for
 @(see std::extended-formals) and @(see std::returns-specifiers).</li>

 <li>A bug with @(see std::defprojection)'s @('subsetp') theorem has been
 fixed.</li>

 </ul>

 <p>Many macros now have a @(':verbosep') option that can be used to disable
 output suppression.</p>

 <p>The @('std/util') testing code has been factored out into a new
 @('std/util/tests') directory.</p>



 <h5>@(see std/typed-lists)</h5>

 <p>There are now books for many built-in ACL2 list recognizers that were
 previously not covered, e.g., @(see boolean-listp), @(see integer-listp),
 etc.</p>


 <h5>@(see std/strings)</h5>

 <p>Many logical definitions throughout the @(see std/strings) library have been
 cleaned up.  Also, many definitions have been changed to use @(see std::define)
 for better documentation.</p>

 <p>The new book @('std/strings/defs-program') contains @(see program) mode
 definitions of most functions in the @('std/strings') library.</p>

 <p>The new @(see str::pretty) routine can convert arbitrary ACL2 objects into
 pretty-printed strings.  Is a fast, state-free, logic mode reimplementation of
 much of ACL2's pretty printer.</p>

 <p>There are now a much richer collection of numeric functions, especially for
 non-decimal bases; see @(see str::numbers).</p>

 <p>The string library now has a very efficient, bitset-like way to represent
 sets of characters, and some functions for working with these character
 sets. See @(see str::charset-p).</p>


 <h5>@(see std/io)</h5>

 <p>The @(see read-string) function will now produce better error messages and
 can (optionally, via raw Lisp) avoid checking @('bad-lisp-objectp'). </p>


 <h3>Defdata Changes</h3>

 <p>Defdata's output has been tweaked.</p>

 <p>The @(see defdata) library now supports range types.</p>

 <p>Counterexample generation has been updated to use tau instead of the former
 @('graph-tc') book, and has many other updates.</p>


 <h3>COI Changes</h3>

 <p>COI's @('def::signature') macro now has support for generalized
 congruences.</p>



 <h3>@(see Quicklisp) and @(see OSLIB)</h3>

 <p>The experimental @(see quicklisp) build has been updated in many ways.
 Quicklisp files are now installed under the @('centaur/quicklisp/inst')
 directory instead of the user's home directory.</p>

 <p>The Quicklisp install can be carried out using a proxy.</p>

 <p>The @(see quicklisp) books now include support for the @('bordeaux-threads')
 and @('hunchentoot') libraries.</p>

 <p>@(see oslib::getpid) has been extended to work on Lisps other than CCL.</p>

 <p>Added minimal tests to @(see oslib) functions such as @(see
 oslib::file-kind) and @(see oslib::date).</p>

 <p>OSLIB has new @(see oslib::lisp-type) and @(see oslib::lisp-version) functions.</p>

 <p>A new book, @('centaur/misc/sharedlibs'), may be useful for relocating @(see
 save-exec) images that require shared libraries for CCL/Linux systems.</p>

 <p>We have remove dependencies on @('iolib') since its build does not seem to
 be reliable.</p>


 <h2>Changes to Centaur Libraries</h2>


 <h3>@(see GL::GL) Changes</h3>

 <p>The @('rtl9') library has been updated to better support GL.</p>

 <p>GL has better @(see if) handling, and as a result may be better able to cope
 with unsatisfiable path conditions (i.e., unreachable code regions) when using
 SAT-based @(see gl::modes).</p>

 <p>New @(see gl::preferred-definitions) may slightly improve performance of
 bit-vector operations like @(see logcar), @(see logcdr), @(see loghead), and
 @(see logtail).</p>

 <p>Some symbolic arithmetic functions have been changed so as to possibly
 improve AIG performance.</p>

 <p>GL's rewrites to @(see 4v) constants have been improved.</p>

 <p>The new macro @(see gl::gl-thm) is like @(see gl::def-gl-thm), but doesn't
 store the theorem.  That is, it's like @(see thm) is to @(see defthm).
 Similarly, @(see gl::gl-param-thm) is to @(see gl::def-gl-param-thm), and @(see
 gl::def-gl-rule) is similar to @(see std::defrule).</p>

 <p>The definitions of @('def-gl-thm'), etc., have been simplified, @(see
 gl::gl-hint) can now be told which GL clause processor to use.</p>

 <p>Minor bugs have been fixed.</p>
 <ul>

 <li>GL's @(see gl::def-gl-rewrite) macro has been reworked to avoid the
 possibility of dropping rules when books are included in different orders.</li>

 <li>The GL interpreter now uses the @('clk') from the given @(see
 gl::glcp-config).</li>

 </ul>

 <p>The documentation for GL has been generally improved.</p>


 <h3>@(see VL) Verilog Toolkit</h3>

 <p>VL has been significantly refactored.  All of the internal @(see vl::syntax)
 is now based on @(see fty::fty), which is a major change.  The representation
 of @(see vl::statements) is especially different.</p>

 <p>VL is beginning to gain support for some limited SystemVerilog constructs.
 This is a major change that affects all areas, e.g., lexing, parsing, syntax,
 and transformations.</p>

 <p>VL now support certain kinds of combinational always blocks.  It also
 supports richer edge-triggered always blocks, including, e.g., registers with
 asynchronous set/reset signals.</p>

 <p>Many bugs have been fixed, some severe.  For instance, VL was incorrectly
 translating BUF, NOT, and XNOR gates with \"extra\" terminals.  The new VL
 @('systest') directory includes various end-to-end tests of VL's translations
 of certain modules.</p>

 <p>Warnings have been improved.  For instance, VL now warns about 0-bit
 replications since some Verilog tools do not implement them correctly.</p>

 <p>Many ttags have been removed from VL, using @(see nrev::nrev).</p>

 <p>VL's always/delay transforms can now optionally produce less bitblasted
 modules.</p>

 <p>The @(see vl::kit) includes new commands such as @('vl gather') and many
 commands have additional options.  It also now prints backtraces on errors for
 improved debugging.</p>

 <p>Numerous other minor bug fixes, extensions, performance improvements,
 etc.</p>


 <h3>Other Centaur Libraries</h3>

 <p>@(see satlink) now uses @('glucose-cert') instead of @('lingeling') as the
 default SAT solver.</p>

 <p>The default @(see sexpr-rewriting) rules have been expanded and improved.
 These changes may improve decomposition proofs and also the performance of
 GL-based STV proofs.</p>

 <p>@(see tshell) should now handle interrupts more reliably.</p>

 <p>The executable counterparts of @(see symbolic-test-vectors) are now disabled
 by default.</p>

 <p>There is now better support for decomposition proofs of @(see
 symbolic-test-vectors), see files such as
 @('centaur/esim/stv/stv-decomp-proofs*') and
 @('centaur/regression/composed-stv.lisp').</p>

 <p>The new @(see stv-run-for-all-dontcares) function is a less conservative
 alternative to @(see stv-run).</p>

 <p>Some lemmas have been localized in @(see esim).</p>

 <p>@(see aignet) now has a basic @('aignet-print') function for debugging.</p>

 <p>The @(see bridge::json-encoding) routines now use @(see define) for better
 documentation.</p>

 <p>Some @(see aignet) functions and @('numlist') are now tail recursive.</p>

 <p>The @(see bitops) @('ihsext-basics') book has additional rules about @(see
 lognot) and @(see logmask).</p>

 <p>Improved and documented the @(see logbitp-reasoning) hint.</p>

 <p>Added @(see bit->bool) to the @(see bitops) library.</p>

 <p>The new @('centaur/bitops/contrib') directory contains additional lemmas.</p>


 <h2>Other Changes</h2>

 <p>(File interface/emacs/inf-acl2.el) One now gets a clear error, suggesting a
 solution, when Emacs command @('meta-x run-acl2') cannot find an ACL2
 executable.  Thanks to Scott Staley for helpful correspondence leading to this
 fix.</p>

 <p>The @(see make-flag) tool now uses slightly faster, more robust hints.</p>

 <p>The @(see witness-cp) clause processor has been made more flexible.</p>

 <p>The @('clause-processors/unify-subst') and @('clause-processors/generalize')
 books have been reworked to avoid nearly duplicate definitions.</p>

 <p>The @(see def-universal-equiv) macro now takes an @('already-definedp')
 option.</p>

 <p>The @('demos/patterened-congruences.lisp') book has been improved.</p>

 <p>The book @('centaur/misc/intern-debugging') book has been modified and
 should now be generally unnecessary, thanks to CCL improvements which have
 resolved the problems it was intended to warn about.</p>

 <p>Something happened to profiling.lisp in r2423.</p>

 <p>@(see disassemble$) now supports macro aliases.</p>

 <p>Several ordinary files that were incorrectly marked as executable are now
 properly non-executable.</p>

 <p>The tau @('elementary-bounders') book has been extended with additional
 lemmas about @(see expt) for powers of 2.</p>



 <h2>Changes to ACL2(r) Books</h2>

 <p>Many explicit function definitions have been replaced with constraints, in
 order to make theorems about those functions more useful for functional
 instantiation later.  For example, instead of insisting that @('(f+g)(x)') is
 really equal to @('f(x) + g(x)'), this is now only required for valid values of
 @('x').</p>

 <p>The theory of integration is now updated to conform to the current version
 of continuity and differentiability (which allows functions that are only
 continuous or differentiable over a particular domain).</p>

 <p>The concepts of continuity, differentiability, and integration now have both
 non-standard and classical definitions.  These are shown to be equivalent for
 classical functions without parameters.  Even when parameters are present, the
 classical definitions can be used to take advantage of important theorems, such
 as the intermediate-value theorem, mean-value theorem, fundamental theorem of
 calculus, etc.</p>")


(defxdoc note-6-4-books
  :parents (note-6-4 release-notes-books)
  :short "Release notes for the ACL2 Community Books for ACL2 6.4 (January,
 2013)."

  :long "<p>The following is a brief summary of changes made to the @(see
 community-books) between the releases of ACL2 6.3 and 6.4.  See the <a
 href='https://code.google.com/p/acl2-books/wiki/ReleaseVersionNumbers'>acl2-books
 Wiki page on ReleaseVersionNumbers</a> for svn revision numbers corresponding
 to releases.  See also @(see note-6-4) for the changes made to ACL2 itself.</p>

 <p>For additional details, you may also see the raw <a
 href='http://code.google.com/p/acl2-books/source/list'>commit log</a>.</p>


 <h3>Build System Changes</h3>

 <p>In previous versions of ACL2, the default @('make') command for building the
 Community Books could take several hours.  Starting in ACL2 6.4, the default
 build is much faster because it <b>excludes many books</b>.</p>

 <p>This particularly affects what happens when you run @('make') from the
 @('books') directory.  We have <i>not</i> changed how @('make regression')
 works from the @('acl2-sources') directory&mdash;it still builds (nearly) all
 of the books.</p>

 <p>See @(see books-certification) for details about how to use the new build
 system.</p>


 <h3>Deleted Stubs</h3>

 <p>When we move a book, we often add a <b>stub</b> book in its previous
 location to help you transition your @(see include-book) commands.  The @(see
 build::cert.pl) build system prints warnings when a stub book is being
 included.</p>

 <p>Stub books have a lifespan of one release.  The following books were stubs
 in ACL2 6.3, so we've deleted them.</p>

 @({
    Previous Location                              New Location
  -----------------------------------------------------------------------
    finite-set-theory/osets/sets.lisp              std/osets/top.lisp

    finite-set-theory/osets/map.lisp               std/osets/*
    finite-set-theory/osets/map-tests.lisp
    finite-set-theory/osets/instance.lisp
    finite-set-theory/osets/membership.lisp
    finite-set-theory/osets/sort.lisp
    finite-set-theory/osets/cardinality.lisp
    finite-set-theory/osets/under-set-equiv.lisp
    finite-set-theory/osets/quantify.lisp
    finite-set-theory/osets/computed-hints.lisp
    finite-set-theory/osets/delete.lisp
    finite-set-theory/osets/intersect.lisp
    finite-set-theory/osets/primitives.lisp
    finite-set-theory/osets/union.lisp
    finite-set-theory/osets/difference.lisp
    finite-set-theory/osets/outer.lisp
    finite-set-theory/osets/portcullis.lisp

    std/lists/make-character-list.lisp             str/*
    std/lists/coerce.lisp
    std/misc/explode-atom.lisp
    std/misc/explode-nonnegative-integer.lisp

    std/io/unsigned-byte-listp.lisp                std/typed-lists/*
    std/io/signed-byte-listp.lisp

    std/io/read-object.lisp                        std/io/base.lisp

    centaur/aig/base.lisp                          {aig,faig}-base
    centaur/aig/three-four.lisp                    faig-constructors.lisp

    centaur/misc/resize-list.lisp                  std/lists/resize-list.lisp
    centaur/misc/equal-by-nths.lisp                std/lists/nth.lisp
  -----------------------------------------------------------------------
 })


 <h3>Book Reorganization</h3>

 <p>We've moved several books to new homes in an effort to clean up the
 top-level @('books') directory.  Users of these libraries will need to update
 their @(see include-book) commands, and in some cases, packages may have also
 changed.</p>

 <p>The table below shows which libraries have moved and where they have moved
 to.  Books with stubs may continue to work until the next release, but you'll
 need to update your @('include-book')s eventually.</p>

 @({
    Stubs?     Previous Location        New Location
   ----------------------------------------------------------------------
     Yes       cutil (cutil::*)         std/util (std::*)
                                         (see also cutil/README)

     Yes       tools/defconsts          std/util/defconsts

     Yes       serialize/unsound-read   std/io/unsound-read

     No        paco                     projects/paco
     No        milawa                   projects/milawa
     No        taspi                    projects/taspi
     No        security                 projects/security
     No        security/suite-b         projects/security/sha-2
     No        wp-gen                   projects/wp-gen
     No        concurrent-programs      projects/concurrent-programs
     No        deduction/passmore       projects/equational
     No        leftist-trees            projects/leftist-trees
     No        symbolic                 projects/symbolic
     No        translators              projects/translators
     No        quadratic-reciprocity    projects/quadratic-reciprocity

     No        parallel                 misc/ or, for some books,
                                        demos/parallel or system/parallel

     No        tutorial-problems        demos/tutorial-problems

     No        workshops/2013-greve-slind    coi/defung

   ----------------------------------------------------------------------
 })

 <h3>Deprecated Books</h3>

 <p>We've deleted the RTL @('rel7') and @('rel8') directories; please upgrade to
 @('rtl/rel9').  Note that @('rel8') is essentially part of @('rel9'), so if you
 can't directly upgrade to @('rel9'), you may try replacing</p>

 @({
     (include-book \"rtl/rel8/lib/top\" :dir :system)
 })

 <p>with</p>

 @({
     (include-book \"rtl/rel9/support/lib3/top\" :dir :system)
     (include-book \"rtl/rel9/arithmetic/top\" :dir :system)
 })



 <h3>Scripts Moved</h3>

 <p>We've moved many build scripts like @(see build::cert.pl), @('clean.pl'),
 and @('critpath.pl') from the top-level @('books') directory, into a new
 @('books/build') directory.  You may need to update paths to these files in
 your Makefiles or other build scripts.</p>



 <h3>Documentation Changes</h3>

 <p>The ACL2 system documentation has been extracted from the ACL2 sources,
 converted into @(see xdoc) format, and is now located in the Community Books.
 This allows for a tighter integration between the system and book
 documentation, e.g., system topics like @(see io) can now directly link to
 related libraries like @(see std/io).  See @(see note-6-4) for details; and see
 especially the file @('system/doc/acl2-doc.lisp').</p>

 <p>A new, feature-rich Emacs-based documentation browser named @(see acl2-doc)
 has been developed by Matt Kaufmann, and has many features.</p>

 <p>We've added at least some minimal @(see xdoc) documentation for several
 @(see projects): see @(see concurrent-programs), @(see des), @(see equational),
 @(see jfkr), @(see milawa), @(see paco), @(see leftist-trees), @(see
 sha-2), @(see taspi), and @(see wp-gen).</p>

 <p>We've added significant documentation for many books and utilities,
 including at least:</p>

 <ul>
 <li>@(see build::cert.pl) - a build system for certifying ACL2 books</li>
 <li>@(see defconsts) - like @('defconst') but supports stobjs, state, and multiple values</li>
 <li>@(see defrstobj) - a macro for introducing record-like stobjs</li>
 <li>@(see bitops) - an arithmetic library especially for bit-vector arithmetic</li>
 <li>@(see def-universal-equiv) - a macro for universally quantified equivalences</li>
 <li>@(see arith-equivs) - equivalence relations for naturals, integers, and bits</li>
 <li>@(see set-max-mem) - a memory management scheme for ccl</li>
 <li>@(see str::base64) - base64 string encoding/decoding</li>
 </ul>

 <p>We've made hundreds of other minor documentation improvements, and we invite
 everyone to contribute improvements.</p>


 <h3>Enhancements to Particular Libraries</h3>

 <h4>General Libraries</h4>

 <h5>@(see std) - standard libraries</h5>
 <ul>
 <li>A new @(see std/basic) library has been added for basic definitions.</li>
 <li>Optimized bitset libraries (formerly in @(see bitops)) are now in @(see std/bitsets).</li>
 <li>@(see std/io) has a new @(see read-string) utility.</li>
 <li>@(see std::deflist) and @(see std::defprojection) macros now implement @(see std::define)-like @('///') syntax.</li>
 <li>The @(see std/util) macros now respect @(see xdoc::set-default-parents).</li>
 <li>@(see std::defaggregate) now prohibits duplicate keys in @('make-') and @('change-') macros.</li>
 <li>@(see std::defaggregate) macro now has a new @(':legiblep :ordered') option, which balances performance and legibility.</li>
 <li>@(see std::define) now saves some additional information about definitions in tables.</li>
 <li>Fixed bugs with the @(see untranslate-preprocess) support in @(see define).</li>
 </ul>

 <h5>@(see std/strings) - string library</h5>
 <ul>
 <li>Added a @('str::binify') function, similar to @(see str::hexify).</li>
 <li>Documented @('binify') and @('hexify').</li>
 </ul>

 <h5>coi - family of libraries</h5>
 <ul>
 <li>@('coi/util/defun-support') now numbers congruence theorems.</li>
 <li>@('coi/nary/nary') has been tweaked with @(see double-rewrite) and now
 has additional examples; see @('coi/nary/example2.lisp')</li>
 <li>Fixed name clashes between @('coi/generalize') and @('witness-cp')</li>
 </ul>

 <h5>@(see bitops) - arithmetic library</h5>
 <ul>
 <li>Added significant documentation, including overview documentation.</li>
 <li>Added fast @(see bitops::bitops/fast-logrev) and @(see bitops::bitops/merge) functions.</li>
 <li>Reduced dependencies and use of non-local includes.</li>
 </ul>

 <h5>@('rtl') - arithmetic library</h5>

 <ul>
 <li>@('rtl/rel9') library now certifies much faster.</li>
 <li>Clarified licensing information on RTL libraries (GPL).</li>
 </ul>

 <h5>@(see xdoc) - documentation system</h5>
 <ul>
 <li>Added support for @('<table>') tags.</li>
 <li>Added @(see xdoc::preprocessor) @('@(`...`)') syntax for Lisp evaluation within documentation strings.</li>
 <li>The @(':xdoc') command now shows where topics came from, and prints parents more nicely.</li>
 <li>@(see xdoc::save) now warns about redefined topics and broken (internal) links.</li>
 <li>@(see xdoc::save) now creates a <a href='linkcheck.html'>link checking page</a> to identify broken external links.</li>
 <li>@(see xdoc::xdoc-prepend) and @(see xdoc::xdoc-extend) now have additional error checking.</li>
 </ul>

 <h5>@(see defrstobj) - machine modeling library</h5>
 <ul>
 <li>Reimplemented defrstobj to be based on abstract stobjs.</li>
 <li>Large rstobjs are now faster to define.</li>
 <li>Good-rstobj predicates are no longer necessary.</li>
 <li>Generalized @(see def-typed-record) to support more general fixing functions,
 for better compatibility with new @(see gl) features.</li>
 <li>Moved old defrstobj code to @(see legacy-defrstobj).</li>
 </ul>


 <h5>GL and Boolean Reasoning</h5>

 <h5>@(see gl) - bit-blasting tool</h5>
 <ul>
 <li>Optimized symbolic subtraction and @(see logeqv).</li>
 <li>Optimized path condition handling in AIG modes.</li>
 <li>Added a vacuity check in AIG modes.</li>
 <li>@(see gl-mbe) has been reimplemented using @(see gl::gl-assert), a more general mechanism.</li>
 <li>A new @(see gl::gl-concretize) utility gives more control over GL in AIG modes.</li>
 <li>Added gl-force-true-strong and gl-force-false-strong.</li>
 <li>@(see logcons) can now unify with integer g-number objects.</li>
 <li>Fixed a bug with @(see gl-mbe) printing.</li>
 <li>Tweaks for better counterexample printing.</li>
 <li>Tweaks to avoid overwriting a user's gl-mode by including GL books.</li>
 </ul>

 <h5>@(see aig) and @(see aignet) - and inverter graph libraries</h5>
 <ul>
 <li>New @(see aig-constructors) ruleset.</li>
 <li>Added aignet <a href='http://fmv.jku.at/aiger/FORMAT'>aiger</a> file reader/writers.</li>
 </ul>

 <h5>@(see satlink) - interface to sat solvers</h5>
 <ul>
 <li>Improved compatibility with additional SAT solvers.</li>
 <li>Documented various @(see satlink::sat-solver-options) that are known to work.</li>
 <li>Added scripts for using solvers with (external, unverified) @(see satlink::unsat-checking) capabilities.</li>
 <li>Optimization to avoid stack overflows in @(see satlink::eval-formula).</li>
 <li>@(':verbose') mode no longer prints variable assignments (they were sometimes too long for Emacs to handle).</li>
 </ul>

 <p>@(see bed::bed) is a new, preliminary library for Boolean expression
 diagrams.</p>


 <h4>Hardware Verification Libraries</h4>

 <h5>@(see vl) - Verilog toolkit</h5>
 <ul>
 <li>Expanded @(see vl2014::always-top) with support for basic @('case') statements.</li>
 <li>Expanded @(see vl2014::expr-simp) to make more reductions and be more modular.</li>
 <li>Added new support for hierarchical identifiers.</li>
 <li>Cleaned up support for gate instances.</li>
 <li>Multiplier synthesis now better matches GL's multipliers.</li>
 <li>Modernized and documented many files.</li>
 </ul>

 <h5>@(see esim) - symbolic hardware simulator</h5>
 <ul>
 <li>Added a compiler from @(see symbolic-test-vectors) into C++ programs.</li>
 <li>Guards are now verified on @('map-aig-vars-fast').</li>
 <li>@('esim/stv/stv-decomp-proofs.lisp') adds a special theory for decomposition
 proofs; see the multiplier demo in the @(see esim-tutorial).</li>
 </ul>

 <h5>@(see 4v-sexprs) - four-valued logic of esim</h5>
 <ul>
 <li>@(see sexpr-rewriting) now works toward a fixpoint to better support decomposition proofs.</li>
 <li>Added @(see 4v-sexpr-purebool-p) for detecting pure Boolean 4v-sexprs</li>
 <li>Documented @(see sexpr-equivs).</li>
 </ul>

 <h5>@(see esim-tutorial) - ESIM hardware verification demos</h5>
 <ul>
 <li>The multiplier proof by decomposition now has comments</li>
 <li>Added a decomposition proof using rewriting, instead of by GL</li>
 </ul>


 <h4>New Tools and Examples</h4>

 <p>A new tool, @('centaur/misc/outer-local'), lets you mark events as
 local to an external context.</p>

 <p>A new tool, @('tools/last-theory-change'), lets you see when a rule was last
 enabled or disabled.</p>

 <p>A new tool, @('centaur/misc/dag-measure'), may be useful when writing
 functions that traverse directed acyclic graphs.</p>

 <p>A new book, @('misc/enumerate.lisp'), demonstrates a trick by J Moore to
 separately consider all possible cases for a particular term during a
 proof.</p>

 <p>A new book, @('misc/multi-v-uni.lisp'), includes a result from <i>A
 Mechanically Checked Proof of a Multiprocessor Result via a Uniprocessor
 View</i> by J Moore, in Formal Methods in System Design, March 1999.</p>

 <p>A new book, @('demos/patterned-congruences.lisp') demonstrates @(see
 patterned-congruence) rules.</p>


 <h4>Miscellaneous Libraries</h4>

 <p>Added some type theorems to @('regex-ui').</p>

 <p>Updated version of @('models/jvm/m1/wormhole-abstraction').</p>

 <p>@('clause-processors/magic-ev') now has special handling for OR.</p>

 <p>The @(see Cgen) library has been enhanced.</p>

 <p>@(see tshell) now has improved output-filtering capability, which @(see
 satlink) takes advantage of.</p>

 <p>@(see def-universal-equiv) now features @(see xdoc) integration.</p>

 <p>Fixed a bug related to undoing inclusion of the @('intern-debugging')
 book.</p>

 <p>Added a workaround for a program-mode bug in SULFA's
 @('sat/local-clause-simp.lisp').</p>

 <p>Fixed guard violations in @('workshops/2004/sumners-ray/support/invp.lisp')
 and @('workshops/2009/sumners/support/kas.lisp').</p>

 <p>Fixed a couple of clashes between @('arithmetic-5')/@('ihs') and @(see
 bitops).</p>

 <p>@(see milawa).  Integrated Milawa into @('books/Makefile'); fixed some
 issues with @('ccl::') prefixes and other non-portable constructs.</p>

 <p>The @('ordinals') library is now licensed under a (more permissive)
 BSD-style license.</p>


 <h3>Other Changes</h3>

 <h5>Make system</h5>
 <ul>
 <li>The Makefile has been made more robust, especially for ACL2(r).</li>
 <li>To improve the error message when attempting to use non-GNU implementations
 of @('make'), the file @('books/Makefile') has been renamed to
 @('books/GNUmakefile').  A trivial @('Makefile') which simply prints an error
 has been added for non-GNU makes.</li>
 </ul>

 <h5>XDOC Fancy Viewer - documentation web pages</h5>

 <ul>
 <li>Mostly fix back-button issues.</li>
 <li>Fixes for compatibility with Internet Explorer and Safari.</li>
 <li>Broken links now properly lead to the broken-link topic.</li>
 <li>Added \"package box\" to shows what package non-ACL2 topics are from,
     to reduce confusion.</li>
 <li>Added <a href='download/'>download this manual</a> feature.</li>
 <li>Added <a href='javascript:printer_friendly()'>printer friendly</a> feature</li>
 <li>Clarified the scope of LICENSE files in XDOC manuals.</li>
 <li>Other bugfixes and cosmetic tweaks.</li>
 </ul>")
