See also mem-test/README.txt and the files in that subdirectory.

This directory provides an example of the use of attachable stobjs.
Stobjs are introduced in books as follows.  It assumes familiarity
with stobjs: concrete, abstract, and nested.  Also see the paper
"Extended Abstract: Mutable Objects with Several Implementations"
by Matt Kaufmann, Warren Hunt and Yahya Sohail in the 2025 ACL2
Workshop.

The book mem.lisp introduces the following two stobjs, to model a
memory using an array.

- Stobj mem$c is an ordinary (concrete) stobj with a single field, an
  array, that is intended to model a memory.  Addresses are modeled as
  array indices and the value at an address A is stored at index A in
  the array.

- Stobj mem is an abstract stobj whose foundation is mem$c, but which
  is attachable so that it can have different foundations and
  different executions for its exports.

The book mem_ht.lisp introduces the following two stobjs, in analogy
to those above, but modeling memory using a hash table instead of an
array.  (The book would be named mem{ht}.lisp, but curly braces in
filenames can cause problems.)

- Stobj mem{ht}$c is an ordinary (concrete) stobj with a single field,
  a hash table, that is intended to model a memory by assocating
  addresses with values.

- Stobj mem{ht} is an abstract stobj whose foundation is mem{ht}$c,
  and which has the same logical fields as does mem, just with
  different :EXEC functions.

Both of the books above include the book logic.lisp, which provides
supporting definitions for the :LOGIC functions of the abstract stobjs
mem and mem{ht}.

The book mem-as-ht.lisp introduces the mem stobj with mem{ht} as its
attachment.  Thus, the instance introduced for this mem stobj is based
on a hash table.  One might imagine a case where it is more effective
to use a hash table than an array -- say, if the array is very large
and memory usage is an issue (which it could be if the constant
*mem-size*, which is the length of the array, were increased to a
large value).

The book nested.lisp introduces a stobj st whose (unique) field is a
mem stobj.  Read (lookup) and write (update) functions are "lifted"
from mem to st.

Finally, the book demo-book.lisp uses the run-script utility to
process the forms in demo-input.lsp, with expected output file
demo-log.txt.  There are comments in demo-input.lsp that explain what
is going on there.  In summary: first mem.lisp is included so that mem
exports will execute as array operations; then, after undoing that
include-book, mem-as-ht.lisp is included so that mem exports will
execute as hash-table operations.  Similar behavior is exhibited when
a mem stobj is nested in another stobj, st.
