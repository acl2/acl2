2020-08-22 EM

The source file for this test came from
  leo/tests/compiler/circuits/inline_member_pass.leo

In this case I did a 'leo new const-circuit-inline'
and then copied the contents of the above leo file
into
  src/main.leo
and the contents of the input comment into
  inputs/const-circuit-inline.in

The JSON files for this test came from
  leo run --enable-all-ast-snapshots

The file type-inference-theorem.lisp
was created with
  cd outputs
  tgc type-inference canonicalization_ast.json type_inferenced_ast.json type-inference-theorem.lisp
