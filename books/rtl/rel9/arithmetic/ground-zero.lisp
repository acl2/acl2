; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")
;includes changes to the default theory (mostly disabling built-in functions)

(in-theory (disable aref1))
(in-theory (disable aset1))
(in-theory (disable aref2))
(in-theory (disable aset2))
(in-theory (disable floor))
(in-theory (disable truncate))
(in-theory (disable mod))
(in-theory (disable rem))
(in-theory (disable expt))
(in-theory (disable ash))
(in-theory (disable acl2::binary-logand))
(in-theory (disable acl2::binary-logior))
(in-theory (disable acl2::binary-logxor))
(in-theory (disable acl2::binary-logeqv))
(in-theory (disable logorc1))
(in-theory (disable lognot))
(in-theory (disable evenp)) ;new
(in-theory (disable oddp)) ;new
(in-theory (disable nonnegative-integer-quotient)) ;new
;abs?

