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
; The scripts, and the ACL2 book that runs the front end on
; the test inputs, are in tests/harness; its README.md has the commands.
; The numbers in the section on results are from 2026-11-23:
; update them, with the versions, when the comparison is run again.

(defxdoc+ differential-testing
  :parents (syntax-for-tools)
  :short "How the input format, the lexer, the tokenizer,
          and the token-tree builder are tested
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
      rustc removes a byte order mark from the start of a file,
      skips a shebang there,
      and turns each carriage return followed by a line feed
      into a line feed
      (see @(see input-format)).
      The inputs are placed in the middle of a file,
      where only the last of these applies;
      on our side, the function for that step,
      @(tsee normalize-crlf), is applied to each input before lexing.
      A line feed is added at the end of each input, on both sides,
      so that a line comment at the end of an input
      does not take in the text after it.
      The start of a file is tested with whole files, as said below.")
    (xdoc::li
     "Editions.
      Each input is run in the editions 2021 and 2024, on both sides.
      rustc's two editions differ on the inputs that have
      a reserved guard [SC15]
      (@('##'), or @('#') right before a string literal),
      which only edition 2024 rejects."))
   (xdoc::h3 "Whole files, for the input format")
   (xdoc::p
    "The steps that precede lexing (see @(see input-format))
     apply to a file as a whole,
     so they are tested on whole files, given as bytes,
     which rustc compiles as they are.
     Then rustc's parser and the phases after it see the tokens,
     and most of these files are not valid programs;
     but rustc reports the errors of its lexer before the others.
     So we compare the class of each file:
     its bytes are not valid UTF-8;
     or the lexer rejects it;
     or the delimiters do not match, with the kind of error;
     or none of these,
     which is the case when no error that rustc reports
     is one of its lexer's.")
   (xdoc::p
    "The class of a file shows whether the file starts with a shebang
     only when its first line has an error of the lexer.
     To see it otherwise, some of the files are probes:
     after @('#!') and a text under test,
     they continue in a way that makes rustc show
     whether it removed the first line.
     One kind continues with an inner attribute
     and the definition of a function, on the first line,
     and a call of the function on the next line:
     if the file compiles, the first line is there, as an attribute;
     if rustc does not find the function, the line was removed.
     The other kind continues with an attribute
     and the opening quote of a string that is never closed:
     if the file compiles, the line was removed;
     if rustc reports the string, and the first line holds it,
     the line was not removed.
     Any other outcome says nothing about the shebang.
     On our side, the answer is whether
     @(tsee shebang-length) is 0 for the text of the file.")
   (xdoc::p
    "Some facts about the input format involve more than one file,
     or a difference between two versions of rustc:
     which of the steps rustc does for the file of a module,
     and for a file that @('include!') or @('include_str!') names.
     For these there are cases written by hand,
     each with the result expected of rustc,
     which a script checks.")
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
     "Whole files, generated, for the input format: about 31,000.
      The probes for the shebang have, as the text under test,
      every sequence of up to two pieces out of 39
      (whitespace characters, comments of each kind,
      and other characters),
      and every sequence of three pieces out of 12 of them;
      some also have something before the @('#!'),
      such as a byte order mark or a space.
      Other files are @('#!') followed by each string
      of up to four characters over a small alphabet.
      For UTF-8, the files have, in a comment,
      each sequence of up to three bytes out of 25,
      chosen at the ends of the ranges
      that matter in the encoding,
      and some sequences of four bytes.")
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
   (xdoc::h3 "The lexemes against the text")
   (xdoc::p
    "A third use of the inputs is for the tokenizer,
     and does not involve rustc either.
     A source unit must give back its text from its lexemes
     (see @(see source-units)):
     each lexeme, from its own components,
     has the code points that are at its span.
     The functions that make source units check this,
     and it is not yet proved that the check never fails.
     So the tests run the same check on each input
     that lexes and tokenizes,
     and on the whole files, which go through the making of a source unit.
     The token boundaries that are compared
     with the Reference's interpreter are the spans of the tokens.")
   (xdoc::h3 "How to run the tests")
   (xdoc::p
    "The scripts are in the directory @('tests/harness') of this library,
     with a @('README.md') that gives the commands.
     The ACL2 side is the book @('tests/harness/driver'),
     which reads a file of inputs,
     runs the input layer (for whole files),
     the lexer, the tokenizer, and the token-tree builder on each,
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
     "The lexemes of the inputs that lex and tokenize,
      161,867 in edition 2021 and 160,086 in edition 2024,
      give back the text of the input, each lexeme at its span.")
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
     about 285,000 tokens, in about 40,700 delimited groups.
     The lexemes of every file give back its text.")
   (xdoc::p
    "On the 31,120 generated whole files, for the input format:")
   (xdoc::ul
    (xdoc::li
     "Our front end and rustc 1.87.0, in each of the two editions,
      put every file in the same class:
      16,170 files are not valid UTF-8,
      3,523 have an error of the lexer,
      1,497 have a delimiter that is not closed,
      and 9,930 have none of these.
      The 11,427 files of the last two classes are made into source units,
      and the check of each one succeeds.")
    (xdoc::li
     "Of the 7,194 probes for the shebang,
      3,343 have an outcome in rustc 1.87.0 that tells
      whether rustc took the first line as a shebang:
      it did in 2,002 and it did not in 1,341.
      On each of them @(tsee shebang-length) says the same.")
    (xdoc::li
     "rustc 1.100.0 reports the same errors as rustc 1.87.0
      on every one of these files."))
   (xdoc::p
    "The 168 cases written by hand come out as expected
     in rustc 1.87.0 and in rustc 1.100.0.
     Ten of them have a different result in the two versions,
     for two reasons (see @(see input-format)):
     a shebang in a file that @('include!') reads
     as an expression or as statements,
     which only rustc 1.87.0 skips;
     and three dashes at the start of a file,
     which rustc 1.87.0 lexes as three tokens
     and rustc 1.100.0 as the start of a frontmatter,
     a feature that it then rejects as unstable.
     In the second case both versions reject the file,
     with different errors.")
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
     On whole files the comparison sees less:
     the class of the file,
     and the shebang where a probe's outcome tells.
     And the tests do not take the place of
     the proof that the lexer satisfies its specification,
     since the specification includes maximal munch,
     which they do not check.")))
