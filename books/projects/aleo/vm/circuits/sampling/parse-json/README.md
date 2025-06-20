# Parse JSON files into ACL2 Fixtype Objects.

This directory now just has these instructions
for demonstrating how to parse JSON files
into ACL2 Fixtype Objects.

We use Eric Smith's JSON parser
(think of it as "JSON-to-S-expression"),
and Alessandro Coglio's
JSON S-expression to JSON fixtype converter.

Eric Smith's JSON parser is in the ACL2 community books
under kestrel/json-parser.

Alessandro Coglio's definition of fixtypes for JSON
and JSON S-expression to JSON fixtype converter
are in the ACL2 community books under kestrel/json.

The following example parses an example JSON Leo AST
into an S-expression and converts it to a fixtype structure.
Then we demonstrate span removal on the fixtype.

In the shell:
```
  cd leo-semantics/acl2
  cert.pl json-span-removal
  cert.pl json2ast
```
In ACL2:
```
  (include-book "kestrel/json-parser/parse-json-file" :dir :system)
  (acl2::parse-file-as-json "~/leo/typed/tests/serialization/expected_typed_ast.json" state)
```
That should print out the JSON S-expression form.<br/>
To capture that result in a constant, we can use this pattern (we are working on a simplification):
```
  (make-event
    (mv-let (j state) (acl2::parse-file-as-json "~/leo/typed/tests/serialization/expected_typed_ast.json" state)
      (acl2::value `(defconst *typed-json-sexp* ',j))))
```
Next, convert \*typed-json-sexp\* to a JSON fixtype.
```
  (include-book "kestrel/json/parser-output-to-abstract-syntax" :dir :system)
  (json::parsed-to-value *typed-json-sexp*) ; return value is (erp val) where erp is NIL
```
That should print out the Leo AST in JSON fixtype form.<br/>
Capture that result in a constant as well:
```
  (make-event
    (mv-let (erp val) (json::parsed-to-value *typed-json-sexp*)
       (declare (ignorable erp))
       (acl2::value `(defconst *typed-json-fty* ',val))))
```
Now, let's show an operation on the AST.<br/>
```
  (include-book "json-span-removal")
  (defconst *spanfree-json-fty* (leo::json-remove-spans-in-value *typed-json-fty*))
  *spanfree-json-fty*
```
That should print out the Leo AST in JSON fixtype format but with the span decorations removed.

Finally, convert the JSON version of the Leo AST to the formal version for which
we are developing an operational semantics.
```
  (include-book "json2ast")
  (mv-let (erp ast) (leo::j2f-file *spanfree-json-fty*) (declare (ignorable erp)) ast)
```
More to come.

# Parse JSON files containing R1CS into ACL2 S-expressions representing Sparse R1CS

First you will need to have a JSON file at hand, containing the circuit you are
interested in.  See the comments in `r1cs-json2acl2.lisp` for an example.  In the
following transcript, let's assume you did
```
  cd
  leo new cb3
```
and then after editing your `src/main.leo` and `inputs/cb3.in` you do
```
  leo run
```
after which the JSON file is in `outputs/cb3.json`

Now, let's convert that to Kestrel's ACL2 Sparse R1CS format.
Here it shows an interactive procedure with the intermediate forms,
in case you want to inspect them.  This can all be combined into a
single function in the future.

In the shell:
```
  cd leo-semantics/acl2/parse-json
  cert.pl r1cs-json2acl2
```

In ACL2:
```
  (in-package "ACL2")

  (include-book "r1cs-json2acl2")

  (make-event
   (mv-let (j state) (parse-file-as-json "~/cb3/outputs/cb3.json" state)
     (value `(defconst *blake2s-json-sexp* ',j))))

  (make-event
   (mv-let (erp val) (json::parsed-to-value *blake2s-json-sexp*)
     (declare (ignorable erp))
     (value `(defconst *blake2s-json-fty* ',val))))

  (make-event
   (mv-let (erp val) (jr2ar-top *blake2s-json-fty*)
     (declare (ignorable erp))
     (value `(defconst *blake2s-acl2-r1cs* ',val))))

  (include-book "std/strings/pretty" :dir :system)
  (include-book "kestrel/file-io-light/write-strings-to-file" :dir :system)

  (write-strings-to-file (list (str::pretty *blake2s-acl2-r1cs*))
                         "/tmp/blake2s-acl2.r1cs"
                         'top-level
                         state)
```
