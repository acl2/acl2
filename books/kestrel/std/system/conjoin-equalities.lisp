; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "conjoin"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define conjoin-equalities ((lefts pseudo-term-listp)
                            (rights pseudo-term-listp))
  :guard (= (len lefts) (len rights))
  :returns (term pseudo-termp :hyp :guard)
  :parents (std/system/term-transformations)
  :short "Build a conjunction of equalities with the given
          left-hand and right-hand sides."
  (conjoin (conjoin-equalities-aux lefts rights))

  :prepwork
  ((define conjoin-equalities-aux ((lefts pseudo-term-listp)
                                   (rights pseudo-term-listp))
     :guard (= (len lefts) (len rights))
     :returns (equalities pseudo-term-listp :hyp :guard)
     (if (endp lefts)
         nil
       (cons `(equal ,(car lefts) ,(car rights))
             (conjoin-equalities-aux (cdr lefts) (cdr rights)))))))
