Yet another CL impementation of [rfc1951
deflate](https://tools.ietf.org/html/rfc1951) decompression
(optionally with [rfc1950 zlib](https://tools.ietf.org/html/rfc1950)
or [rfc1952
gzip](https://tools.ietf.org/html/rfc1952https://tools.ietf.org/html/rfc1952)
wrappers), with support for reading from foreign pointers (for use with
mmap and similar, etc), and from CL octet vectors and streams.

### Still somewhat WIP, but approaching usability.

Performance for vectors/pointers is somewhere between FFI to libz and chipz,
still needs some low-level optimization of copy routines and checksums.
Stream API is very slow, and may be replaced at some point.

API isn't completely stable yet, needs some actual use to figure out
the details.


#### API/usage

##### easy API:
`decompress-vector (compressed &key (format :zlib) output`

```lisp
;; pass a (simple-array (unsigned-byte 8) (*))
(3bz:decompress-vector (alexandria:read-file-into-byte-vector "foo.gz")
                       :format :gzip) ;; accepts :deflate, :zlib, :gzip
;; ->
#(....)
1234
;; get back decompressed data and size as 2 values

```

If decompressed size is known, you can save some copies by passing in
a pre-allocated `(simple-array (unsigned-byte 8) (*))` vector with
`:OUTPUT`.

##### full API:

Allows input and output in multiple pieces, as well as input from
vectors, FFI pointers, or streams (streams are currently very slow
though).


* step 1: make a decompression state:

    `make-deflate-state`, `make-zlib-state`, or `make-gzip-state`.
Optionally with `:output-buffer octet-vector` to provide initial
output buffer.

* step 2: make an input context

    `make-octet-vector-context`, `make-octet-stream-context`, or `with-octet-pointer`+`make-octet-pointer-context`.

    pass source of coresponding type, + optional `:start`,`:end`,`:offset`
to specify valid region within source. For FFI pointers, use
`(with-octet-pointer (octet-pointer ffi-pointer size) ...)` to wrap a
raw pointer + size into `octet-pointer` to pass to
`make-octet-pointer-context`. (If you need indefinite scope pointers,
file an issue so support that can be added to API.)

* step 3: decompress

    `(decompress context state)` returns current offset into output buffer.

* step 4: check decompression state

    * if `(finished state)`, you are done.

    * if `(input-underrun state)`, you need to supply more input by creating a new input context, and call `decompress` again with new context.

    * if `(output-overflow state)`, you need to provide a new output buffer with `(replace-output-buffer state new-buffer)` and call `decompress` again.


##### performance notes:

* Streams API is currently *very* slow, and will probably be rewritten at some point.

* Output in small pieces is slow:

    `deflate` needs to maintain a 32kb history window, so every time
output buffer overflows, it copies 32kb of history. If output buffer
is smaller than 32kb, that means more history is copied than total
output, so avoid small output buffers.

    Ideally, if output size is known in advance and output buffer never
overflows, there is no extra copies for history window.  

    If output size isn't known, if you start with something like `(min
input-size 32768)` and double (or at least scale by 1.x) on each
overflow, there will only be O(N) bytes copied to combine output
buffers, and O(lgN) byytes copied for history.  

