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
(in-theory (disable binary-logand))
(in-theory (disable binary-logior))
(in-theory (disable binary-logxor))
(in-theory (disable binary-logeqv))
(in-theory (disable logorc1))
(in-theory (disable lognot))
(in-theory (disable evenp)) ;new
(in-theory (disable oddp)) ;new
(in-theory (disable nonnegative-integer-quotient)) ;new
;abs?

