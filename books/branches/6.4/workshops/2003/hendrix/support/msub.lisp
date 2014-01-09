;;;;; Matrix negation and subtration.
;;;;;
;;;;; Both operations are implemented as a single macro,
;;;;; so this book is really short.

(in-package "ACL2")

(include-book "mdefthms")
(include-book "madd")
(include-book "mscal")

(defmacro m- (m &optional (n 'nil binary-casep))
  (if binary-casep
      `(m+ ,m (sm* -1 ,n))
    `(sm* -1 ,m)))
