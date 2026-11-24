; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book only documents the differential tests.
; The scripts, and the ACL2 book that runs the lexer and tokenizer on
; the test inputs, are in tests/harness; its README.md has the commands.
; The numbers in the section on results are from 2026-11-19:
; update them, with the versions, when the comparison is run again.

(defxdoc+ differential-testing
  :parents (syntax-for-tools)
  :short "How the lexer, the tokenizer, and the token-tree builder
          are tested
          against rustc and against the Rust Reference's interpreter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about the lexer (see @(see lexer)),
     and the ones still to be proved,
     relate it to our grammar and its side conditions
     (see @(see grammar) and @(see extra-grammatical-restrictions)).
     That the grammar and the side conditions describe
     the inputs that rustc lexes is not something to prove:
     rustc is the definition of what lexes,
     and it is a program, not a specification.
     So that part is tested,
     by running our lexer, tokenizer, and token-tree builder,
     and rustc, on the same inputs
     and comparing the results.
     A test that finds a disagreement leads to a correction of ours,
     or, where the Reference had led us to the wrong behavior,
     also to an entry in @(see reference-vs-rustc).")
   (xdoc::h3 "What is compared")
   (xdoc::p
    "The comparison is with the lexing stage of rustc alone.
     rustc rejects some inputs while lexing them,
     and others only later, in its parser or after it.
     An input of the first kind, like @('0b12') or @('1e'),
     must fail in our lexer.
     An input of the second kind must lex:
     for example a string literal with a suffix, like @('\"a\"b'),
     or an integer literal too large for every integer type.")
   (xdoc::p
    "To observe that stage,
     we give rustc the input as the arguments of
     a macro that only counts its arguments.
     Then the tokens of the input never reach rustc's parser:
     rustc reports an error exactly when its lexer finds one,
     and otherwise the count says how many tokens the input has.
     The two sides agree on an input if both reject it,
     or if both accept it and count the same number of tokens.
     This is a coarse comparison:
     it does not look at the kinds of the tokens,
     or at where each token starts and ends,
     though a wrong boundary usually changes the count.
     The comparison with the second oracle, below,
     does look at the boundaries.")
   (xdoc::p
    "For the two sides to count the same things,
     the following is done.")
   (xdoc::ul
    (xdoc::li
     "Delimiters.
      rustc's lexer also groups the tokens by their delimiters,
      into token trees:
      it rejects an input whose delimiters do not match,
      and the macro counts a delimited group as one argument.
      On our side this is the token-tree builder
      (see @(see token-tree-builder)), which runs after the tokenizer.
      Since the input is between the parentheses of the macro invocation,
      the builder is given the tokens of the input
      between an opening and a closing parenthesis, as rustc has them.
      If it rejects them, rustc must reject the input,
      and the first error that rustc reports about delimiters
      must be of the kind that the builder reports
      (a closing delimiter of the wrong kind,
      a delimiter that is not closed,
      or a closing delimiter that closes nothing).
      Otherwise, what is counted is the token trees
      that the builder puts between the two parentheses.
      An input like @(') (') closes the parenthesis of the invocation
      and opens another:
      then rustc builds token trees without error
      and rejects the input in a later phase,
      and the builder must accept the tokens too.")
    (xdoc::li
     "Doc comments.
      rustc turns each doc comment into an attribute
      before the macro receives it.
      So on our side an outer doc comment counts as the two tokens
      of @('#[doc = \"...\"]') (the @('#') and the bracketed group),
      and an inner one as the three of @('#![doc = \"...\"]').")
    (xdoc::li
     "What precedes lexing.
      rustc removes a byte order mark and a shebang line
      from the start of a file,
      and turns each carriage return followed by a line feed
      into a line feed.
      Our lexer does none of this
      (it will be the task of a layer before it).
      The inputs are placed in the middle of a file,
      where rustc does not remove the first two,
      and the carriage returns are removed from such pairs
      before the inputs go to our lexer.
      A line feed is added at the end of each input, on both sides,
      so that a line comment at the end of an input
      does not take in the text after it.")
    (xdoc::li
     "Editions.
      Each input is run in the editions 2021 and 2024, on both sides.
      rustc's two editions differ on the inputs that have
      a reserved guard [SC15]
      (@('##'), or @('#') right before a string literal),
      which only edition 2024 rejects."))
   (xdoc::h3 "Oracles")
   (xdoc::p
    "The authority is rustc, at the version that the library follows,
     1.87.0 (see @(see grammar)).
     We use the released compiler, as described above.
     Other projects call rustc's lexer inside their own process,
     which gives rustc's tokens themselves
     but needs a nightly compiler and its internal interfaces;
     we have not done that.")
   (xdoc::p
    "A second oracle is the interpreter of the Rust Reference's grammar,
     which exists for the Reference's version for Rust 1.100.0
     (see @(see related-lexer-descriptions)).
     It gives, for each token, where it starts and ends
     and the rule that it matches;
     so against it we also compare the boundaries of the tokens.
     Its grammar has no editions, and corresponds to edition 2024.
     Since it describes a later version of Rust than ours,
     we also run rustc 1.100.0 on the inputs,
     to see where the two versions of rustc differ.")
   (xdoc::p
    "Two things that look like oracles are not.
     The crate @('rustc_lexer'), the first layer of rustc's lexer,
     accepts inputs that rustc's lexing stage as a whole rejects:
     it marks many errors on its tokens and leaves the rejection
     to the layer above it.
     And the crate @('proc-macro2') has a lexer of its own,
     which accepts some suffixes and exponents that rustc rejects.")
   (xdoc::h3 "Inputs")
   (xdoc::ul
    (xdoc::li
     "Short inputs, generated in categories.
      Most categories are all the strings, up to some length,
      over a small alphabet chosen for one area of the lexical grammar:
      for instance, for number literals,
      all the strings of up to five characters over
      @('1'), @('0'), @('.'), @('e'), @('+'), @('_'),
      @('a'), @('b'), and @('x').
      Other categories combine chosen pieces
      (a literal of each kind, a suffix, and something right after it),
      or list single cases.
      For the token-tree builder,
      one category is all the strings of up to five characters
      over the six delimiters and @('a').
      There are about 212,000 such inputs.")
    (xdoc::li
     "Source files of published crates,
      taken from a local cargo registry.")
    (xdoc::li
     "Cases transcribed from the tests of rustc 1.87.0.
      These are in the certified test books of this library,
      in the directory @('tests'),
      with the result that rustc gives for each."))
   (xdoc::h3 "The lexer against its specification")
   (xdoc::p
    "The same inputs serve a second purpose,
     which does not involve rustc.
     Until it is proved that the results of the lexer satisfy
     the specification @(tsee lexing-okp),
     the tests check it on each input that lexes:
     every conjunct of the specification that can be executed,
     which is all of them but maximal munch,
     must hold of the CSTs that the lexer returns.")
   (xdoc::h3 "How to run the tests")
   (xdoc::p
    "The scripts are in the directory @('tests/harness') of this library,
     with a @('README.md') that gives the commands.
     The ACL2 side is the book @('tests/harness/driver'),
     which reads a file of inputs,
     runs the lexer, the tokenizer, and the token-tree builder on each,
     and writes a file of results.
     The inputs and the results are not in the repository:
     the scripts generate them,
     and keep the results of rustc from one run to the next,
     so that after a change to the lexer
     only the ACL2 side runs again, which takes seconds.")
   (xdoc::h3 "Results")
   (xdoc::p
    "At this time of writing, on the 211,713 short inputs:")
   (xdoc::ul
    (xdoc::li
     "Our lexer, tokenizer, and token-tree builder
      agree with rustc 1.87.0,
      in each of the two editions,
      on all the inputs but 16.
      Those 16 have non-ASCII identifiers,
      which our lexer does not cover yet.
      On the 23,381 inputs where the builder reports an error,
      rustc's first error about delimiters is of the same kind.")
    (xdoc::li
     "The CSTs of the 161,919 inputs that lex
      satisfy the executable conjuncts of the specification.")
    (xdoc::li
     "rustc 1.100.0 accepts the same inputs as rustc 1.87.0,
      with the same counts,
      but for the 148 that have, in an identifier,
      a character that Unicode 17 added;
      rustc 1.87.0 uses Unicode 16.
      The two differ in the errors that they report about delimiters,
      on 7,035 inputs:
      where closing delimiters of the wrong kind
      are followed, further on, by a closing delimiter that closes nothing,
      rustc 1.87.0 reports all these errors, in that order,
      and rustc 1.100.0 leaves out some of the first ones.
      On 5,921 of those inputs it reports only the last one.
      Our builder reports the first error, as rustc 1.87.0 does.")
    (xdoc::li
     "The Reference's interpreter agrees with rustc 1.100.0
      on all the inputs but one, @('/*!/*/')
      (see @(see reference-vs-rustc)).")
    (xdoc::li
     "Our lexer puts the boundaries of the tokens
      where the Reference's interpreter does,
      on all the inputs but 165:
      the 148 above, the 16 of the first item,
      and @('/*!/*/'), which our lexer rejects, as rustc does."))
   (xdoc::p
    "On 495 source files, of 300 to 12,000 bytes each,
     36 of them with block doc comments,
     our tokenizer and rustc 1.87.0, in edition 2021,
     count the same number of tokens in every file,
     and our builder accepts the tokens of every file:
     about 285,000 tokens, in about 40,700 delimited groups.")
   (xdoc::h3 "Limits")
   (xdoc::p
    "These tests are evidence, not proof:
     they say nothing about inputs unlike the ones tried.
     When both sides reject an input,
     they may do so for different reasons,
     and the comparison does not see that.
     The comparison with rustc sees only the number of tokens,
     and the one that sees their boundaries
     is with a description of a later version of Rust.
     And the tests do not take the place of
     the proof that the lexer satisfies its specification,
     since the specification includes maximal munch,
     which they do not check.")))
