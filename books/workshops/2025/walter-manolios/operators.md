# Documentation

## Case Sensitivity
Identifiers in SMT-LIB2 are case sensitive, but they are not when
using `cl-z3`.

## Sorts

Sorts are specified using symbols or lists of symbols. For ease of
use, `cl-z3` allows one to specify sorts using symbols in any
package - the only thing that matters is whether the `symbol-name` of
the symbol matches (case-insensitive). In general we will write the
names of sorts as symbols in the `keyword` package, e.g. they start
with a colon like `:bool`.

Note that when using `z3-assert`, `exists`, or `forall` you must provide keyword symbols for
sorts. This is what enables a terser syntax for specifying multiple
variables with the same sort: e.g. 
```
(z3-assert (x y z :int)
  (= (* x y) z))
```
is the same as:
```
(z3-assert (x :int y :int z :int)
  (= (* x y) z))
```

When using `declare-const`, `declare-fun`, or pretty much any other
context where sorts are provided, it is not necessary to use keyword
symbols to name sorts.

In the case of indexed identifiers - sorts that look like `(_ <ty>
<arg1> ... <argn>)` - `<arg1>` through `<argn>` may be integers or
symbols.

The following sort specifiers are available:
- `:bool`: Boolean
- `:int`: arbitrary-precision integer
- `:real`: real numbers (see the SMT-LIB Reals theory)
- `(_ :bv <n>)`: a bitvector of length `n`
- `(:seq <ty>)`: a sequence with elements of type `ty`
- `(:set <ty>)`: a set with elements of type `ty`
- `:string`: shorthand for `(:seq (_ :bv 8))` (a sequence of 8-bit values, e.g. ASCII characters)
- `(:regex <seq-ty>)`: a regular expression over the sequence type `seq-ty`
- `(:array <dom> <rng>)`: an array with domain `dom` and range `rng`

All of the above sort specifiers correspond to a sort from an SMT-LIB2
theory, an extension of an SMT-LIB2 theory that Z3 provides, or a new
theory that Z3 provides.

In addition, when using `z3-assert` you can provide the following
specifier:
- `(:fn (<dom1> ... <domn>) <rng>)`: a function with domain `dom1 x ... x domn` and range `rng`

`(:fn ...)` is really a shorthand for declaring that the variable
associated with this specifier should be an uninterpreted function
that has the given rank (e.g. argument types and return
types). Therefore, you cannot use the `(:fn ...)` sort specifier
inside of another sort specifier, or to constrain a variable
introduced by `forall` or `exists`.

### Enums

An enum sort consists of a finite set of elements, specified when the
enum is registered.

The following line defines an enum sort with the name `:bar` and the elements `a`, `b`, and `c`.
`(register-enum-sort :bar (a b c))`

A constant enum element can be expressed using `(enumval <ty> <el>)`.
For example, the following statement asserts that `q` is equal to the
`:bar` element `a`.

```
(z3-assert (q :bar)
           (= q (enumval :bar a)))
```

### Named tuples

A named tuple sort consists of a set of fields, each of which has a
name and a sort.

The following line defines a tuple sort with two fields, `name` (which
is a string) and `age` (which is an integer).

```
(register-tuple-sort :dog
  ((name . :string)
   (age  . :int)))
```

Values of this sort can be constructed using `(tuple-val <tuple-name> <field1> ... <fieldn>)`,
where `tuple-name` is the registered name of the tuple sort and the
fields must be provided in the same order as they appeared in the
`register-tuple-sort` form.

For example, the following statement asserts that the `:dog` value `x`
is equal to the given constant `:dog` value:
```
(z3-assert (x :dog)
           (= x (tuple-val :dog "Toto" 5)))
```

The value of a field can be accessed using `(tuple-get <tuple-name> <field-name> <val>)`,
where `tuple-name` is the registered name of the tuple sort,
`field-name` is the name of one of the fields of the tuple sort, and
`val` is a value of the tuple sort.

For example, the following statement asserts that the name of the
`:dog` value `x` is equal to `name`, and the age of `x` is greater
than 3.

```
(z3-assert (x :dog name :string)
           (and (= (tuple-get :dog name x) name)
                (> (tuple-get :dog age x) 3)))
```

Note that we do not currently support the setter/getter/constructor
notation that Z3 defines; we expect to support this in the future.

## Functions

In general, `cl-z3` aims to support a large subset of the intepreted
functions (operators) that Z3 provides, with the same semantics as Z3
provides. When we diverge from Z3's semantics (which generally
involves eliminating implicit casting behavior), we note this
alongside the operator below. We also provide 

Names in parentheses after a function call denote alternative names
for the same function. Square brackets around a parameter name
indicate that the parameter can only be a constant value (it cannot be
a Z3 variable or symbolic value, for example). Angle brackets around a
parameter name indicate that the parameter may have a symbolic value.

### Propositional Logic
- `true`: Boolean true
- `false`: Boolean false
- `(= <x> <y>)` (`equal`,`==`): true if `x` and `y` are equal under
  Z3's notion of equality.
- `(!= <x> <y>)`: Shorthand for `(not (= <x> <y>))`
- `(not <x>)`: Boolean negation
- `(and <v1> ... <vn>)`: Boolean conjunction of `v1` through `vn`
- `(or <v1> ... <vn>)`: Boolean disjunction of `v1` through `vn`
- `(xor <v1> <v2>)`: Boolean xor
- `(ite <v1> <v2> <v3>)` (`if`): Evaluates to `<v2>` if `<v1>` is true and `<v3>` if `<v1>` is false. Sorts of `<v2>` and `<v3>` must be the same.
- `(=> <v1> <v2>)` (`implies`): Boolean implication. Does not allow arbitrary arity, unlike Z3.
- `(distinct <v1> ... <vn>)`: true if none of `v1` through `vn` are equal to each other
- `((_ at-least [k]) <v1> ... <vn>)` is true if `k` or more of `v1` through `vn` are true
- `((_ at-most [k]) <v1> ... <vn>)` is true if `k` or fewer of `v1` through `vn` are true

### Arithmetic
Typically, functions with arity greater than unary require both
arguments to be of the same sort. This is not an issue at the moment,
as the interface currently does not support any numeric sorts aside
from integers.

Note that operations that may cause exceptions in other languages
(like division by zero) are underspecified in Z3. This means that Z3
treats `(/ x 0)` as an uninterpreted function that it may assign any
interpretation to. This can lead to unexpected behavior if you're not
careful.

For example, Z3 reports that the following is satisfiable, since it
can assign `x` and `y` different values, and has the flexibility to
have division by 0 for the value of `x` return 3, and division by 0
for the value of `y` return 4.

```
(z3-assert (x :int y :int)
           (and (= (/ x 0) 3)
                (= (/ y 0) 4)))
(check-sat)
```

- `(> <x> <y>)`,`(< <x> <y>)`,`(>= <x> <y>)`,`(<= <x> <y>)`: Comparisons
  between two numbers
- `(+ <v1> ... <vn>)`: Numerical (real) addition of all `vi`
- `(- <x>)`: Unary negation of the number `x`
- `(- <v1> ... <vn>)`: Numerical (real) subtraction of `v2` through `vn`
  from `v1`. More than one argument must be provided.
- `(* <v1> ... <vn>)`: Numerical (real) multiplication of all `vi`
- `(/ <x> <y>)`: division, will result in an interpretation for
  division by 0 being added. Either both `<x>` and `<y>` must have
  sort `int` or sort `real`. If both arguments have sort `int`, the
  result will be the same as `(div <x> <y>)`. If real-number division
  between two integers is desired, you will need to cast both integers
  to reals using `to_real`. This behavior is unlike Z3's.
- `(div <x> <y>)`: Integer division of `<x>` by `<y>`, will result in
  an interpretation for division by 0 being added. Both `<x>` and
  `<y>` must have sort `int`. Unlike Z3, this will not implicitly cast
  `<x>` and `<y>` to `int` if they do not already have that sort.
- `(mod <x> <y>)`: integer modulus, will result in an interpretation
  for division by 0 and modulus by 0 being added. Both `<x>` and `<y>`
  must have sort `int`. Unlike Z3, this will not implicitly cast `<x>`
  and `<y>` to `int` if they do not already have that sort.
- `(rem <x> <y>)`: Integer remainder, will result in an interpretation
  for division by 0, modulus by 0, and remainder by 0 being
  added. Both `<x>` and `<y>` must have sort `int`. Unlike Z3, this
  will not implicitly cast `<x>` and `<y>` to `int` if they do not
  already have that sort.
- `(power <x> <y>)`: raises `x` to the power of `y`
- `(to_real <x>)` (`int2real`, `int-to-real`): convert the given
  integer to a real number
- `(to_int <x>)` (`real2int`, `real-to-int`): convert the given real
  number to an integer (in short, it returns the floor, but see the
  SMT-LIB2 Reals_Ints theory for more information)
- `(is_int <x>)`: A predicate that holds iff `x` is a real number that
  is in the image of `to_real`.

### Function Application
- `(<fn> <arg1> ... <argn>)`: apply the function `fn` to the arguments
  `arg1` through `argn`

### Quantifiers
- `(exists (<v1> <v1sort> ... <vn> <vnsort>) <body>)`: true if there
  exist assignments for `v1`, ... `vn` with sorts matching sort
  specifiers `v1sort`, ... , `vnsort` respectively such that the body
  is true under the assignments

- `(forall (<v1> <v1sort> ... <vn> <vnsort>) <body>)`: true if for all
  assignments for `v1`, ... `vn` with sorts matching sort specifiers
  `v1sort`, ... , `vnsort` respectively, the body is true under the
  assignments

### Bitvectors
Note that the functions below that take in 2 bitvectors require that
those two bitvectors have the same sort (e.g. the same number of bits)
unless otherwise specified.
- `(bvnot <x>)`: bitwise negation of `x`
- `(bvredand <x>)`: takes the conjunction of all bits in `x` and
  returns a bitvector of length 1 with the result
- `(bvredor <x>)`: takes the disjunction of all bits in `x` and
  returns a bitvector of length 1 with the result
- `(bvand <x> <y>)`: bitwise and
- `(bvor <x> <y>)`: bitwise or
- `(bvxor <x> <y>)`: bitwise xor
- `(bvnand <x> <y>)`: bitwise nand
- `(bvnor <x> <y>)`: bitwise nor
- `(bvxnor <x> <y>)`: bitwise xnor
- `(bvneg <x>)`: two's complement unary negation
- `(bvadd <x> <y>)`: two's complement addition
- `(bvsub <x> <y>)`: two's complement subtraction
- `(bvmul <x> <y>)`: two's complement multiplication
- `(bvudiv <x> <y>)`: unsigned division
- `(bvsdiv <x> <y>)`: two's complement signed division
- `(bvurem <x> <y>)`: unsigned remainder
- `(bvsrem <x> <y>)`: two's complement signed remainder (sign follows
  dividend)
- `(bvult <x> <y>)`: unsigned less than
- `(bvslt <x> <y>)`: two's complement signed less than
- `(bvule <x> <y>)`: unsigned less than or equal to
- `(bvsle <x> <y>)`: two's complement signed less than or equal to
- `(bvuge <x> <y>)`: unsigned greater than or equal to
- `(bvsge <x> <y>)`: two's complement signed greater than or equal to
- `(bvugt <x> <y>)`: unsigned greater than
- `(bvsgt <x> <y>)`: two's complement signed greater than
- `(concat <x> <y>)`: concatenate two bitvectors. They can have
  different sorts
- `((_ extract [hi] [lo]) <x>)`: extract the bits from position `hi` to
  position `lo` in `x` to produce a new bitvector
- `((_ sign_extend [len]) <x>)`: sign-extend `x` to the signed equivalent
  bitvector of size `m+i` where `m` is the bitvector size of `x`
- `((_ zero_extend [len]) <x>)`: zero-extend `x` to the unsigned equivalent
  bitvector of size `m+i` where `m` is the bitvector size of `x`
- `((_ repeat [ntimes]) <x>)`: concatenate `ntimes` copies of the
  bitvector `x`
- `(bvshl <x> <y>)`: shift the bitvector `x` to the left by `y` bits
- `(bvlshr <x> <y>)`: shift the bitvector `x` to the right by `y`
  bits, with "logical shift" behavior (zero-extending)
- `(bvashr <x> <y>)`: shift the bitvector `x` to the right by `y`
  bits, with "arithmetic shift" behavior (sign-bit-copying)
- `((_ int2bv [nbits]) <val>)`: Interprets the integer `val` as a bitvector
  of length `nbits`
- `(bv2int <val> [signed?])`: Interprets the bitvector `val` as an
  integer, treating as signed if `signed?` is true.

### Sequences
Most of these functions operate on both strings and sequences (since
strings are essentially just a special case of sequences).

- `(as seq.empty <sort>)`: create an empty sequence for sequence sort
  `sort`
- `(seq.unit <val>)`/`seq.unit`: create a length-1 sequence containing
  the element `val`
- `(seq.++ <seq1> <seq2>)` (`str.++`): concatenate `seq1` and `seq2`
- `(seq.prefixof <seqp> <seq>)` (`str.prefixof`): true if `seqp` is a
  prefix of `seq`
- `(seq.contains <container> <containee>)` (`str.contains`): true if
  `container` contains the sequence `containee`
- `(str.< <x> <y>)`,`(str.<= <x> <y>)`: lexicographic comparisons of
  strings
- `(seq.extract <seq> <off> <len>)`: returns the subsequence of `seq`
  of length `len` starting at offset `off`
- `(seq.replace <seq> <src> <dst>)`: replace the first occurrence of
  `src` with `dst` in `seq`
- `(seq.at <seq> <idx>)`: get the unit sequence of `seq` at index `idx`,
  or the empty sequence if `idx` is out of bounds
- `(seq.nth <seq> <idx>)`: get the element of `seq` at index `idx`.
  Under-specified if `idx` is out of bounds
- `(seq.len <seq>)` (`str.len`): get the length of `seq`
- `(seq.indexof <seq> <subseq> <off>)` (`str.indexof`): returns the
  index of the first occurrence of the sequence `subseq` in `seq`
  starting from offset `off`, or -1 if `subseq` does not occur in
  `seq` after offset `off`
- `(seq-last-index <seq> <substr>)`: returns the index of the last
  occurrence of the sequence `substr` in `seq`, or -1 if `substr` is
  not contained in `seq`

### Conversions
- `(str.to.int <x>)`: Converts string `x` into an integer. Returns -1 if
  `x` cannot be converted into an integer.
- `(int.to.str <x>)`: Converts integer `x` into a string.

### Regular expressions
TODO

### Sets
The translation of set values reported by Z3 is currently
experimental. Z3 represents sets as arrays with a range sort of
`:bool`.

Z3 does not currently expose functions that make an empty or a full
set in its SMT-LIB2 interface. Therefore, we will use CVC5's
[experimental
syntax](https://cvc5.github.io/docs/cvc5-1.0.0/theories/sets-and-relations.html#finite-sets)
for this.

- `(as set.empty <sort>)`: create an empty set with sequence sort `sort`
- `(as set.universe <sort>)`: create a full set with sequence sort `sort`
- `(set.singleton <val>)`: create a set that contains only `val`
- `(set.insert <elt1> ... <eltn> <set>)`: Add `elt1` through `eltn` to `set`
- `(set.union <set1> <set2>)`: take the union of the two sets
- `(set.inter <set1> <set2>)`: take the intersection of the two sets
- `(set.minus <set1> <set2>)`: generate the set containing all elements from `set1` that are not in `set2`.
- `(set.complement <set>)`: complement the set `set`
- `(set.member <elt> <set>)`: returns true if `elt` is a member of set `set`
- `(set.subset <set1> <set2>)`: true if `set1` is a subset of `set2`

### Arrays
TODO
- `array-ext`: Mostly useful for internal usage, see https://github.com/Z3Prover/z3/issues/2123
