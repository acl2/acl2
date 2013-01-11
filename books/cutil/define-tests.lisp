(in-package "CUTIL")

(include-book "define")

(define foo ()
  :returns (ans integerp)
  :assert (integerp)
  3)

(define foo2 ()
  :assert (integerp stringp)
  (mv 3 "hi"))

(define foo3 ()
  :assert (integerp stringp)
  (mv 3 "hi"))

(define foo4 ()
  :returns (ans integerp)
  44)
