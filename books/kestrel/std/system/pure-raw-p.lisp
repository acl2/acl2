; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pure-raw-p ((fn symbolp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short "Check if a function has raw Lisp code and is pure,
          i.e. it has no side effects."
  :long
  (xdoc::topstring
   (xdoc::p
    "This utility checks whether the symbol is
     in a whitelist of function symbols that have raw Lisp code
     and that are known to be free of side effects,
     and whose @('unnormalized-body') property
     therefore accurately describes the behavior of the function
     (despite the function being implemented natively for efficiency).")
   (xdoc::p
    "The fact that a function with raw Lisp code is not in this whitelist
     does not necessarily mean that it has side effects.
     It just means that it is currently not known to be free of side effects.
     The whitelist may be extended as needed."))
  (and (member-eq fn *pure-raw-p-whitelist*) t)

  :prepwork
  ((defconst *pure-raw-p-whitelist*
     '(=
       /=
       abs
       acons
       alpha-char-p
       assoc-equal
       atom
       ash
       butlast
       ceiling
       char
       char-downcase
       char-equal
       char-upcase
       char<
       char>
       char<=
       char>=
       conjugate
       endp
       eq
       eql
       evenp
       expt
       floor
       identity
       integer-length
       hons
       hons-equal
       hons-get
       keywordp
       last
       len
       length
       listp
       logandc1
       logandc2
       logbitp
       logcount
       lognand
       lognor
       lognot
       logorc1
       logorc2
       logtest
       max
       member-equal
       min
       minusp
       mod
       nonnegative-integer-quotient
       not
       nth
       nthcdr
       null
       oddp
       plusp
       position-equal
       rassoc-equal
       rem
       remove-equal
       revappend
       reverse
       round
       signum
       standard-char-p
       string
       string-downcase
       string-equal
       string-upcase
       string<
       string>
       string<=
       string>=
       sublis
       subseq
       subsetp-equal
       subst
       substitute
       take
       truncate
       zerop
       zip
       zp))
   (assert-event (symbol-listp *pure-raw-p-whitelist*))
   (assert-event (no-duplicatesp-eq *pure-raw-p-whitelist*))))
