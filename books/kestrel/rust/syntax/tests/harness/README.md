# Differential tests of the lexer and tokenizer

These scripts compare the ACL2 Rust lexer and tokenizer
(the books in `kestrel/rust/syntax`) with rustc,
and with the interpreter of the Rust Reference's lexical grammar,
on generated short inputs and on real source files.
The xdoc topic `rust$::differential-testing` says what is compared and why;
this file says how to run the comparison.

For each input, the comparison with rustc is on whether both sides accept it
and, if so, on how many tokens it has.
The comparison with the Reference's interpreter
is also on where each token starts and ends.

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

4. Run them through the ACL2 lexer and tokenizer (a few seconds each):

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

`compare_results.py` compares any two directories of results.

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

## How the comparison works

**rustc.**
`run_rustc.py` puts each input in the arguments of a macro that only
counts its argument tokens.
The tokens never reach the parser or later phases,
so the only errors are those of rustc's lexer
(including its building of token trees),
which is the stage that the ACL2 lexer and tokenizer model.
The count is the number of top-level token trees:
a delimited group counts as one.
With `--deep` it is the number of all tokens,
a group counting as one plus its contents.

**ACL2.**
The driver counts the tokens of the tokenizer in the same way.
rustc turns a doc comment into the tokens of an attribute,
so an outer doc comment counts as 2 token trees (5 tokens deep)
and an inner one as 3 (6 deep).
Inputs whose delimiters do not match are reported as `:unbal`:
rustc rejects them while building token trees,
which the ACL2 side does not do yet.

**Input adjustments.**
`to_acl2.py` appends a line feed to each input,
because the probe puts one after the input,
and replaces each CR LF pair with LF,
because rustc does that when it reads a file
(in the ACL2 front end this belongs to the input layer, before lexing).
`reference-driver` makes the same two adjustments,
and puts each input after a `;` and a line feed,
because the interpreter treats the start of its input
as the start of a file.

**Known gaps.**
`compare.py` and `compare_bounds.py` tag a disagreement as a known gap
when the input contains something the lexer does not cover yet:
`block-doc`, `doc-cr` (a bare CR in a doc comment),
or `non-ascii`.
The tags are heuristics on the input text, in `known_gaps`;
remove each one when its gap is closed.
`gen_files.py` skips files with block doc comments
for the same reason.

**Edition 2024 reserved guards.**
`rv-go-2024-guard` is `rv-go` for edition 2024 plus a stand-in for the
reserved guards (`##`, and `#` before a string literal),
which the tokenizer does not implement yet:
it rejects a `#` lexeme immediately followed by a lexeme
that starts with `#` or a double quote.
`rv-go-bounds` uses the same stand-in.

    (rust$::rv-go-2024-guard "/data/tests.lsp" "/data/acl2-2024-guard.lsp" state)

## Files

| File | Purpose |
|---|---|
| `gen_tests.py` | Generates the short inputs, by category |
| `gen_files.py` | Selects real source files |
| `run_rustc.py` | Runs inputs through rustc |
| `to_acl2.py` | Converts inputs to code-point lists for ACL2 |
| `driver.lisp` | Runs inputs through the ACL2 lexer and tokenizer |
| `compare.py` | Compares the results on short inputs |
| `compare_files.py` | Compares the results on whole files |
| `compare_results.py` | Compares two directories of results (two versions of rustc, or the Reference's interpreter and rustc) |
| `compare_bounds.py` | Compares the token boundaries of the ACL2 lexer with those of the Reference's interpreter |
| `reference-driver/` | Runs the short inputs through the Reference's interpreter |
