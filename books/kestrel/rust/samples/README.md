# Rust MIR sample dumps

This directory holds serialized dumps of Rust crates, extracted with
[Charon](https://github.com/AeneasVerif/charon), that the MIR importer
(`../import/`) reads and the interpreter (`../mir/`) can run.

## RustCrypto AES

### Overview

We started with the RustCrypto `aes` crate (32-bit fixslice AES) here

    https://github.com/RustCrypto/block-ciphers/blob/507938ca7c92da77a0ded6fe9d9df6f9be112dbb/aes/src/soft/fixslice32.rs

We copied it into the package

    ghcr.io/bendyarm/aeneas-acl2-dev:aeneas-23cf8c8_charon-58b7d54_acl2-0612757

(which was built from https://github.com/bendyarm/aeneas-acl2-devenv
and archived at https://zenodo.org/records/22365956 )
at the location

    /work/aeneas/tests/src/reference/fixslice32-aes-v0.9.1.rs

We changed the following:

  - Cut to AES-128 only (AES-192/256 dropped).  Kept the encrypt path (given
    expanded key), the key schedule, and decrypt.  The round-function logic is
    copied from the original unchanged (13 debug_assert!s retained); the type,
    feature-gate, and API changes listed below are confined to the top-level
    functions.
  - Deleted the cipher-crate trait API and the wrapper layer
    (read8/write8/*_at/key_round/bitslice_into), and removed the external deps
    (crate::Block, cipher::array::Array) → monomorphic, no_std-able,
    self-contained.
  - Resolved cfg(aes_backend_soft="compact") branches to the non-compact soft
    path.
  - Replaced State::default()/BatchBlocks with explicit [u32;8] / [[u8;16];2],
    and replaced the FixsliceKeys128 alias with [u32;88].

and saved it as

    /work/aeneas/tests/src/aes_fixslice_encrypt.rs

Note, this file contains both encrypt and decrypt.  (A copy of it is committed
in this directory as `aes_fixslice_encrypt.rs`, for reference.)

We ran Charon (which invokes rustc) to extract MIR, using the commands detailed
in the section "Generating JSON" below, and got

    aes_ullbc_elaborated.json

This is the "elaborated" ULLBC dump of the vendored RustCrypto AES-128 crate.

We gzipped that to get `aes_ullbc_elaborated.json.gz` in the current directory.

Two tests use this dump, both run by the ACL2 regression (`make regression`
in `books/`) but not by the library's `top.lisp` books:

  - `../import/aes-import-test.lisp` decompresses the gzipped file with
    `gunzip -k aes_ullbc_elaborated.json.gz`, runs the importer to build the
    MIR AST in ACL2, and checks that the result equals the committed fixture
    in `../mir/tests/aes-fixslice-program.lisp` (a `defconst` holding the
    imported program).

  - `../mir/tests/aes-fixslice.lisp` runs that fixture's `encrypt` and
    `decrypt` on the MIR interpreter, checking the FIPS-197 known-answer
    vectors (reused from `../../crypto/aes/aes-spec-tests.lisp`, not
    duplicated here) and differentially against the ACL2 AES-128 spec.

So only the import test needs this gzipped dump; the interpreter test runs
from the committed fixture.

Note, the decompressed `.json` (~6.9 MB) is in `.gitignore`.

### Generating JSON

The elaborated dump is a direct Charon run on the crate (not using the Aeneas
pipeline). The rustc-side args after `--` are `--edition=2021` (puts
`TryInto` in the prelude, needed by the key schedule's `try_into()`),
`--crate-name`, and `--crate-type=rlib` (the crate has no `main`):

    docker run --rm -v "$PWD:/out" --entrypoint bash \
      ghcr.io/bendyarm/aeneas-acl2-dev:aeneas-23cf8c8_charon-58b7d54_acl2-0612757 -c '
      /work/charon/bin/charon rustc --ullbc --mir elaborated \
        --dest-file /out/aes_ullbc_elaborated.json -- \
        --edition=2021 /work/aeneas/tests/src/aes_fixslice_encrypt.rs \
        --crate-name=aes_fixslice_encrypt --crate-type=rlib \
        --allow=unused --allow=non_snake_case'
    gzip -n aes_ullbc_elaborated.json

`--mir elaborated` selects rustc's `mir_drops_elaborated_and_const_checked`
query (runtime MIR before optimization — the dialect the interpreter
models; see `../mir/abstract-syntax.lisp`), and `--ullbc` keeps the
unstructured, rustc-shaped control-flow graph the importer expects.
`monomorphize` is off (generics are finalized at the call site by the
importer) and no syntax-reshaping options are set.

### Other forms we generated but do not save here

To sanity-check the extraction we also produced two artifacts that we
have not committed to the repo, since they are not needed to test the
importer and interpreter:

- **`aes_ullbc_promoted.json`** — the same crate at Charon's default MIR
  level (`Promoted` = rustc's `mir_promoted`, analysis-phase MIR): drop
  `--mir elaborated` from the command above. Comparing it to the
  elaborated dump confirms that, on this drop-free crate, the analysis
  and runtime MIR dialects differ only where expected — the borrowck-only
  `FakeRead`s disappear and storage-dead markers are duplicated onto
  panic paths, with no `Drop`s in either.

- **`aes_llbc_aeneas_preset_carved.llbc`** — the structured LLBC form for
  the Charon &rarr; Aeneas &rarr; ACL2 cross-validation channel, built by
  the devenv's own recipe `make -C /work/aeneas/tests/acl2` (its
  `aes_fixslice_encrypt` rule adds `--preset=aeneas --monomorphize
  --monomorphize-mut=except-types --remove-adt-clauses
  --lift-associated-types='*'`). It confirms the reshaped pipeline:
  structured loops, indexing and operators lowered to calls, and asserts
  reconstructed.
