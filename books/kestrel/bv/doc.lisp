; Documentation for BV library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/topics" :dir :system)
(include-book "kestrel/utilities/xdoc-paras" :dir :system)
(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)

(defxdoc bv
  :short "The BV library for reasoning about bit-vectors"
  :parents (bit-vectors)
  :long
  (xdoc::topparas
   "See books/kestrel/bv/.

The BV library deals with \"bit vectors\" which are, conceptually,
finite sequences of bits (0s and 1s).  The library includes many
operations on bit vectors, including operations which interpret bit
vectors as unsigned or signed integers.

Bit vectors of size M are represented as natural numbers less than 2^M
in a straightforward way: The bits in a bit vector are numbered
starting at 0 (the least significant bit) and correspond to the bits
in the binary representation of the number.  A 1 bit in position N
contributes 2^N to the value of the number.

We usually visualize a bit vector with bit position 0 at the far
right.  For example, here is how we visualize the bit vector
represented by the number 17 (= 2^4 + 2^0):
@({value    1   0   0   0   1
index: | 4 | 3 | 2 | 1 | 0 |})
We say that a bit vector has size M if its most significant (highest
indexed) 1 bit has index at most M-1. Note that the size of a bit
vector is not unique; any bit vector of size M is also a bit vector of
size M+1 and of any larger size.  However, the operators in the BV
library take explicit size arguments.  Bit vector arguments that do
not fit into the indicated sizes are chopped down to the indicated
sizes, and the result is also chopped down (if needed) so that a bit
vector of the indicated size is always returned.

The connection between bit vectors and natural numbers is a deep one.
Indeed we use constants such as 0 and 17 to represent particular bit
vectors.  But it is sometimes helpful to view BVs and natural numbers
as two distinct types.

The standard recognizer for a bit vector is the built-in ACL2 predicate
unsigned-byte-p.

Bit vectors can also be interpreted as signed numbers using a standard
twos-complement representation.  A bit vector of size M is taken to
represent numbers in the range [-2^(M-1), 2^(M-1)-1].  This matches
the behavior of the ACL2 predicate signed-byte-p.)"))

;; (depends-on bvchop-def.lisp")
(acl2::gen-xdoc-for-file
 "bvchop-def.lisp"
 ((bvchop "Chop a value down to the given size."))
 (bv))

;; (depends-on bvplus.lisp")
(acl2::gen-xdoc-for-file
 "bvplus.lisp"
 ((bvplus "Bit-vector sum."))
 (bv))

;; TODO: Document more BV operations!
