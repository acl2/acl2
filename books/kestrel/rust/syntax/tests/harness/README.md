# Differential tests of the input layer, lexer, tokenizer, and token-tree builder

These scripts compare the ACL2 Rust input layer, lexer, tokenizer,
and token-tree builder
(the books in `kestrel/rust/syntax`) with rustc,
and with the interpreter of the Rust Reference's lexical grammar,
on generated short inputs, on generated whole files,
and on real source files.
The xdoc topic `rust$::differential-testing` says what is compared and why;
this file says how to run the comparison.

For each input, the comparison with rustc is on whether both sides accept it
and, if so, on how many token trees it has;
when the delimiters do not match, it is also on the kind of error.
The comparison with the Reference's interpreter
is also on where each token starts and ends.
For the input layer, the inputs are the bytes of whole files,
and the comparison is on the kind of error, if any,
and on whether the file starts with a shebang.

## Requirements

- rustc 1.87.0 as a rustup toolchain (`rustup toolchain install 1.87.0`).
  The version is `TOOLCHAIN` in `run_rustc.py`;
  the environment variable `RUSTC` overrides the compiler path.
- Python 3.
- ACL2, with the book `kestrel/rust/syntax/tests/harness/driver` certified.
- For the Reference's interpreter, cargo with the toolchain 1.100.0
  (`rustup toolchain install 1.100.0`), and access to GitHub when building.

## The data directory

The inputs and the results are not in the repository:
the scripts generate them, and keep the results of rustc from one run
to the next.
Choose a directory for them outside the books.
The shell commands below call it `$DATA`,
and the ACL2 commands write its full path as `/data`
(ACL2 does not expand shell variables).

    export DATA=/path/to/the/data/directory

Run the shell commands from this directory.

## Short inputs

1. Generate the inputs (only after adding a category to `gen_tests.py`):

       python3 gen_tests.py $DATA/tests

2. Run them through rustc.
   Categories that already have a result file are skipped,
   so normally this only runs new categories;
   all of them take about 10 minutes per edition.

       python3 run_rustc.py $DATA/tests $DATA/rustc-1.87.0-2021 --edition 2021
       python3 run_rustc.py $DATA/tests $DATA/rustc-1.87.0-2024 --edition 2024

3. Convert the inputs for ACL2:

       python3 to_acl2.py $DATA/tests.lsp $DATA/tests

4. Run them through the ACL2 lexer, tokenizer, and token-tree builder
   (a few seconds each):

       (include-book "kestrel/rust/syntax/tests/harness/driver" :dir :system)
       (rust$::rv-go "/data/tests.lsp" "/data/acl2-2021.lsp" (rust::edition-2021) state)
       (rust$::rv-go "/data/tests.lsp" "/data/acl2-2024.lsp" (rust::edition-2024) state)

5. Compare:

       python3 compare.py $DATA/tests $DATA/rustc-1.87.0-2021 $DATA/acl2-2021.lsp
       python3 compare.py $DATA/tests $DATA/rustc-1.87.0-2024 $DATA/acl2-2024.lsp

   The output gives the totals, then the disagreements in groups,
   with a few examples each.
   Category names after the three arguments restrict the comparison;
   `--out FILE` writes all the disagreements as JSON.

After a change to the lexer, recertify and repeat steps 4 and 5;
the rustc results stay valid.

## Whole files

    python3 gen_files.py $DATA/files.json 700
    python3 run_rustc.py $DATA/files.json $DATA/files-rustc.json --deep
    python3 to_acl2.py $DATA/files.lsp $DATA/files.json

    (rust$::rv-go-files "/data/files.lsp" "/data/files-acl2.lsp" state)

    python3 compare_files.py $DATA/files.json $DATA/files-rustc.json $DATA/files-acl2.lsp

`gen_files.py` takes the files from the crates in the local cargo
registry, or from a directory given as a third argument.
A fourth argument, a regular expression, selects only the files
that it matches; for example, files with float literals:

    python3 gen_files.py $DATA/files.json 700 ~/.cargo/registry/src '\d\.\d|\d[eE][+-]?\d|\d\.(?![.\w])'

For each file where the two sides disagree,
`compare_files.py` shows where the ACL2 lexer stopped.

## The input layer

What comes before lexing
(UTF-8 decoding, the byte order mark, CR LF, the shebang)
applies to a file as a whole,
so these tests are whole files, given as bytes.
`input_format.py` generates them (31,120 files),
runs them through rustc (about 2 minutes), and compares:

    python3 input_format.py gen $DATA/input-format
    python3 input_format.py rustc $DATA/input-format --toolchain 1.87.0 --edition 2021

    (rust$::rv-go-input "/data/input-format/cases.lsp" "/data/input-format/acl2-2021.lsp" (rust::edition-2021) state)

    python3 input_format.py compare $DATA/input-format $DATA/input-format/rustc-1.87.0-2021.json $DATA/input-format/acl2-2021.lsp

The output gives the totals, then the disagreements.
It also lists rustc's first error for each file
in which rustc found no error of its lexer:
check that none of these messages is one of the lexer's
(the script tells them by how they begin: see `LEX` in it).

The script also has hand-written cases,
each with the result expected of rustc:
that the file compiles, or the start of the first error.
They include the cases with more than one file
(a module, a file named in `include!`),
and those on which two versions of rustc differ.
This runs them and reports any that does not come out as expected:

    python3 input_format.py hand --toolchain 1.87.0 --toolchain 1.100.0

## The lexer against its specification

    (rust$::rv-go-spec "/data/tests.lsp" state)

This returns the number of inputs that lex, and the ids of those whose
lexeme CSTs violate an executable conjunct of `rust$::lexing-okp`
(every conjunct except maximal munch); there should be none.
It also takes the converted whole files.

## Another version of rustc

`run_rustc.py` takes the compiler from the environment variable `RUSTC`,
so the same inputs run through any installed toolchain.
The results of each version go in directories named after it:

    export RUSTC=$(rustup which --toolchain 1.100.0 rustc)
    python3 run_rustc.py $DATA/tests $DATA/rustc-1.100.0-2021 --edition 2021
    python3 run_rustc.py $DATA/tests $DATA/rustc-1.100.0-2024 --edition 2024

    python3 compare_results.py $DATA/tests $DATA/rustc-1.87.0-2021 $DATA/rustc-1.100.0-2021

`compare_results.py` compares any two directories of results,
on whether each input is accepted and on the counts.
It does not compare the errors.
`compare.py` does, for the errors about delimiters,
and they depend on the version of rustc:
where closing delimiters of the wrong kind are followed
by a closing delimiter that closes nothing,
rustc 1.87.0 reports all these errors,
and rustc 1.100.0 leaves out some of the first ones.
So `compare.py` with the results of rustc 1.100.0
shows `delimiter errors differ` on such inputs.

## The Reference's interpreter

Since its version for Rust 1.100.0, the Rust Reference comes with
an interpreter of its own lexical rules
(`tools/parser` in the repository `rust-lang/reference`).
`reference-driver` is a small program that runs our inputs through it.
Its `Cargo.toml` names the commit of the Reference to use:
`e24eecf` is the one that Rust 1.100.0 pins.
Build it with its output outside the books, and run it:

    cargo +1.100.0 build --release --manifest-path reference-driver/Cargo.toml --target-dir $DATA/reference-driver-target
    $DATA/reference-driver-target/release/reference-driver $DATA/tests $DATA/reference-1.100.0

    python3 compare_results.py $DATA/tests $DATA/reference-1.100.0 $DATA/rustc-1.100.0-2024

The Reference's rules have no editions and always apply the reserved
guards, so its results correspond to edition 2024.
Its results also hold where each token starts and ends.
To compare those with the ACL2 lexer:

    (rust$::rv-go-bounds "/data/tests.lsp" "/data/acl2-bounds.lsp" state)

    python3 compare_bounds.py $DATA/tests $DATA/reference-1.100.0 $DATA/acl2-bounds.lsp

One disagreement outside the known gaps is expected there: `/*!/*/`,
which the Reference's rules accept, and which rustc and the ACL2 lexer
reject as an unterminated block comment.

## How the comparison works

**rustc.**
`run_rustc.py` puts each input in the arguments of a macro that only
counts its argument tokens.
The tokens never reach the parser or later phases,
so the only errors are those of rustc's lexer
(including its building of token trees),
which is the stage that the ACL2 lexer, tokenizer,
and token-tree builder model.
(The exception is an input that closes the parenthesis of the macro
invocation, like `) (`: see `:split` below.)
The count is the number of top-level token trees:
a delimited group counts as one.
With `--deep` it is the number of all tokens,
a group counting as one plus its contents.

**ACL2.**
The driver runs the lexer, the tokenizer, and the token-tree builder.
The probe puts the input between the parentheses of a macro invocation,
so the driver gives the builder the tokens of the input
between an opening and a closing parenthesis,
and counts the token trees that the builder puts between the two.
rustc turns a doc comment into the tokens of an attribute,
so an outer doc comment counts as 2 token trees (5 tokens deep)
and an inner one as 3 (6 deep).

For each short input the driver writes one of the following.

| Result | Meaning | Agrees with rustc when |
|---|---|---|
| a number | the top-level token trees of the input | rustc accepts, with the same count |
| `:err` | the lexer or the tokenizer rejects the input | rustc rejects |
| `:mismatched`, `:unclosed`, `:unexpected` | the builder rejects the probe's tokens, with that kind of error | rustc's first error about delimiters is of that kind |
| `:split` | the input closes the probe's parenthesis before its end, as `) (` does | rustc rejects, with no error about delimiters |

The three kinds of error are rustc's
`mismatched closing delimiter`,
`this file contains an unclosed delimiter`, and
`unexpected closing delimiter`.
For whole files and for token boundaries,
the driver gives the builder the tokens of the input alone,
and writes `:unbal` if it rejects them.

**Input adjustments.**
`to_acl2.py` appends a line feed to each input,
because the probe puts one after the input.
The driver then replaces each CR LF pair with LF,
with the function of the input layer (`rust$::normalize-crlf`),
because rustc does that when it reads a file.
`reference-driver` appends the line feed and replaces the pairs itself,
and puts each input after a `;` and a line feed,
because the interpreter treats the start of its input
as the start of a file.

**The input layer.**
`input_format.py` gives rustc each file as it is, as a library crate,
so rustc's parser and later phases see the tokens,
and most files do not compile.
What is compared is the class of the file:
not valid UTF-8; an error of the lexer;
an error about delimiters, with its kind; or none of these.
rustc reports the errors of its lexer before those of its parser,
so a file is in the last class when none of rustc's errors
is one of the lexer's.
For each file the driver writes
`:utf8`, `:err`, `:mismatched`, `:unclosed`, `:unexpected`, or `:ok`,
and the length of the shebang (0 if there is none).

Whether a file starts with a shebang shows in its class
only when the first line has an error;
so some files are probes, built to show it in another way.
After `#!` and the text under test, a `kept` probe has
an inner attribute and a function on the same line,
and a call of the function on the next line:
if it compiles, the first line was not removed (no shebang);
if rustc does not find the function, the line was removed (shebang).
A `removed` probe has, after the attribute,
the opening quote of a string that is never closed:
if it compiles, the line was removed (shebang);
if rustc reports the string, and no line feed comes before it,
the line was not removed (no shebang).
Any other outcome says nothing, and is not compared.
The texts under test are sequences of up to three pieces:
whitespace characters, comments of each kind, and other characters.

**Known gaps.**
`compare.py` and `compare_bounds.py` tag a disagreement as a known gap
when the input contains something the lexer does not cover yet:
`non-ascii` (non-ASCII identifiers) is the only one left.
The tags are heuristics on the input text, in `known_gaps`;
remove each one when its gap is closed.

## Files

| File | Purpose |
|---|---|
| `gen_tests.py` | Generates the short inputs, by category |
| `gen_files.py` | Selects real source files |
| `run_rustc.py` | Runs inputs through rustc |
| `to_acl2.py` | Converts inputs to code-point lists for ACL2 |
| `input_format.py` | Whole files for the input layer: generates them, runs them through rustc, and compares |
| `driver.lisp` | Runs inputs through the ACL2 input layer, lexer, tokenizer, and token-tree builder |
| `compare.py` | Compares the results on short inputs |
| `compare_files.py` | Compares the results on whole files |
| `compare_results.py` | Compares two directories of results (two versions of rustc, or the Reference's interpreter and rustc) |
| `compare_bounds.py` | Compares the token boundaries of the ACL2 lexer with those of the Reference's interpreter |
| `reference-driver/` | Runs the short inputs through the Reference's interpreter |
