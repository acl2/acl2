# Some minimal tests of Leo compiler phases


## Update and build leo.
```
    cd leo
    git pull
    cargo build --release
```


## Compile Leo programs so that they generate JSON files for the intermediate ASTs.

The following causes the compiler to generates all the JSON files that it knows
how to generate, when building these test programs.  The JSON files are put
in the `outputs/` directory, which is now mentioned in `.gitignore` for new Leo directories.

```
    cd leo-acl2/tests/minimal/canon-self
    leo build --enable-all-theorems

    cd ../compound-assignments
    leo build --enable-all-theorems

    cd ../nested-arrays
    leo build --enable-all-theorems

    cd ../fill-function-output-type
    leo build --enable-all-theorems
```

Side note: also now written is a file `outputs/NAME.sum`
where `NAME` is the Leo program directory name.
This file contains the `sha256sum` of `src/main.leo`.

The following JSON files are currently being made:

1. `initial_ast.json` (prior to canonicalization)

2. `canonicalization_ast.json` (after canonicalization)

3. `type_inferenced_ast.json` (after canonicalization and type inference)

TODO: When we update these Leo program directories with a newer structure or with changes to JSON file format,
consider also copying gold output files to an expected-outputs directory
so we can do regression tests.


## Test theorem generation and checking

First, unzip the lisp heap file that has theorem generation and checking in it.
(Rebuild that heap file if leo-acl2 has changed.)
```
    cd leo-acl2/testing/bin
    gunzip --keep leo-acl2.lx86cl64.gz
```

Then run theorem generation and checking for canonicalization:
```
    cd leo-acl2/tests
    ../testing/bin/tgc canonicalization minimal/canon-self/outputs/initial_ast.json minimal/canon-self/outputs/canonicalization_ast.json minimal/canon-self/outputs/canonicalization-theorem.lisp
    ../testing/bin/tgc canonicalization minimal/compound-assignments/outputs/initial_ast.json minimal/compound-assignments/outputs/canonicalization_ast.json minimal/compound-assignments/outputs/canonicalization-theorem.lisp
    ../testing/bin/tgc canonicalization minimal/nested-arrays/outputs/initial_ast.json minimal/nested-arrays/outputs/canonicalization_ast.json minimal/nested-arrays/outputs/canonicalization-theorem.lisp
    ../testing/bin/tgc canonicalization minimal/fill-function-output-type/outputs/initial_ast.json minimal/fill-function-output-type/outputs/canonicalization_ast.json minimal/fill-function-output-type/outputs/canonicalization-theorem.lisp
```

## Older tests; might still be relevant.

TODO: Need to update some file names.

### Parse the Leo ASTs from the json files into abstract syntax trees in ACL2.

```
    cd leo-acl2/tests
    $ACL2

    LEO !>(include-book "top")
    LEO !>(jsonfile-to-formal "minimal/canon-self/outputs/initial.json" state)
    LEO !>(jsonfile-to-formal "minimal/canon-self/outputs/canonicalization.json" state)
    LEO !>(jsonfile-to-formal "minimal/canon-self/outputs/type_inference.json" state)

    LEO !>(jsonfile-to-formal "minimal/compound-assignments/outputs/initial.json" state)
    LEO !>(jsonfile-to-formal "minimal/compound-assignments/outputs/canonicalization.json" state)
    LEO !>(jsonfile-to-formal "minimal/compound-assignments/outputs/type_inference.json" state)

    LEO !>(jsonfile-to-formal "minimal/nested-arrays/outputs/initial.json" state)
    LEO !>(jsonfile-to-formal "minimal/nested-arrays/outputs/canonicalization.json" state)
    LEO !>(jsonfile-to-formal "minimal/nested-arrays/outputs/type_inference.json" state)

    LEO !>(jsonfile-to-formal "minimal/fill-function-output-type/outputs/initial.json" state)
    LEO !>(jsonfile-to-formal "minimal/fill-function-output-type/outputs/canonicalization.json" state)
    LEO !>(jsonfile-to-formal "minimal/fill-function-output-type/outputs/type_inference.json" state)
```

### A book that tests canonicalization phase

The book `proof-gen.lisp` loads json files for the above tests and proves that the canonicalization
was done according to spec.

```
    cd leo-acl2/acl2/tests
    cert.pl proof-gen
```
