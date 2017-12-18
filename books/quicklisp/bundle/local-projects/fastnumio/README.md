# fastnumio

We provide faster Common Lisp routines for

 - Printing natural numbers (fixnums or bignums) to output streams in
   hexadecimal format (e.g., `DEADBEEF`).

 - Reading hexadecimal numbers in from input streams.

Of course, Common Lisp provides its own built-in ways to print and read hex
numbers, e.g., `(format stream "~x" val)` and `read` with inputs like `#xF00D`.
However, for a particular application, we found that these built-in routines
were too slow and that they produced a lot of garbage when bignums were
involved.  We therefore developed faster replacements.

Ballpark speedup:

  - 3x or more on CCL (64-bit X86 Linux)
  - 2x or more on SBCL (64-bit X86 Linux)

Plus significant memory savings in many cases.

See [benchmark results](results.txt) for more details.


## API

### `(write-hex val stream) --> stream`

  - `val` must be a non-negative integer.
  - `stream` must be an output stream.

This is like `(format stream "~x" val)`.  We print a hexadecimal encoding of
`val` to `output-stream`.  Some notes:

  - The number is printed in conventional MSB-first order.
  - Digits `A`-`F` are printed in upper-case.
  - No prefixes are printed, i.e., we print `BEEF`, not `#BEEF`, `#xBEEF`, `0xBEEF`, etc.


### `(read-hex stream) --> val`

  - `val` is an integer on success or NIL on error/EOF.
  - `stream` must be an input stream.

We try to read an hex value (e.g., `FF9900`) from stream.  We succeed exactly
when the stream begins with any hex digit.  On success, we consume all leading
hex digits from the stream and return their value as an integer, leaving the
stream at the first non-hex character.  On failure (no leading hex digits or
EOF), we return NIL and leave the stream in place.  Some notes:

 - We accept hex digits in any case, e.g., `37ff` or `37FF` or `37Ff` are all
   fine.

 - Leading zeroes are accepted and ignored.

 - Prefixes are not expected or accepted.  If your stream begins with `#FF00`
   or `#xFF00`, `read-hex` will fail.  If it begins with `0xFF00`, `read-hex`
   will return 0 and the `xFF00` part will still be in the stream.


### `(scary-unsafe-write-hex val stream) --> stream`

This is a drop-in replacement for `write-hex`.  On some Lisps it may be just an
alias for `write-hex`.  On other Lisps, it may have a special implementation
that achieves faster performance or uses less memory.

This function is **scary and unsafe to use** because it makes use of internal,
non-exported functionality from CCL/SBCL.  It may therefore stop working if a
Lisp upgrades causes these implementation details to change in unexpected ways.

We do at least basic tests of this function to make sure it is working, so it
is quite unlikely that a Lisp upgrade could screw up your program.  However,
you should almost certainly NOT use this unless you need performance so badly
that you are willing to take the risk.


### `(scary-unsafe-read-hex stream) --> val`

This is a drop-in replacement for `read-hex`.  On some Lisps it may be just an
alias for `read-hex`.  On other Lisps, it may have a special implementation
that achieves faster performance or uses less memory.

This function is **scary and unsafe to use** for the same reasons as
`scary-unsafe-write-hex`.


### Authorship, License

Copyright (C) 2015 [Centaur Technology](http://www.centtech.com)

Original author: [Jared Davis](mailto:jared.c.davis@gmail.com)

MIT/X11-style [LICENSE](LICENSE).



