2020-08-19 EM

The source file for this test came from
  leo/tests/compiler/array/complex_access.leo
In this case I did not bother to create the full leo directory structure.
I just put it in
  src/main.leo

The JSON files for this test came from
  cd ~/leo
  git checkout feature-tgc-ci
  git pull
  cargo build --release
  cargo run -p leo-test-framework --bin tgc -- -f compiler_array_complex_access

And then I copied
  ~/leo/tmp/tgc/compiler_array_complex_access.leo_328/*.json
to the outputs/ directory under the current directory:
  ~/leo-acl2/tests/minimal/compiler_array_complex_access/outputs/

Then I created
  outputs/type-inference-theorem.lisp
with just the minimal content to run file-typeinfp.
