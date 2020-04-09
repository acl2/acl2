; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2017 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection assert?
  :parents (std/testing assert$ errors)
  :short "A variation of @(tsee assert$) with customizable context and message."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the optional context and message arguments are not supplied,
     this macro works similarly to @(tsee assert$).
     If they are supplied and the test fails,
     they are used to display the hard error.")
   (xdoc::p
    "The two optional arguments must be
     either both supplied or both not supplied.
     The guard requires that.")
   (xdoc::p
    "All the arguments of this macro are evaluated.
     The (evaluated) context must be a symbol.
     The (evaluated) message must have type @(tsee msgp).")
   (xdoc::@def "assert?"))

  (defmacro assert? (test form &optional ctx msg)
    (declare (xargs :guard (iff ctx msg)))
    `(if ,test
         ,form
       ,(if msg
            `(hard-error ,ctx
                         "~@0"
                         (list (cons #\0 ,msg)))
          `(hard-error ,(or ctx ''assert?)
                       "Assertion failed:~%~x0"
                       (list (cons #\0 '(assert? ,test ,form))))))))
