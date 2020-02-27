; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-tests-and-call-listp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-tests-and-call-listp nil))

(assert! (pseudo-tests-and-call-listp (list (make tests-and-call
                                                  :tests '((f x))
                                                  :call '(g y z))
                                            (make tests-and-call
                                                  :tests '('3 x)
                                                  :call ''#\a))))

(assert! (not (pseudo-tests-and-call-listp (list (make tests-and-call
                                                       :tests 1
                                                       :call 2)
                                                 (make tests-and-call
                                                       :tests "a"
                                                       :call "b")))))

(assert! (not (pseudo-tests-and-call-listp 88)))

(assert! (not (pseudo-tests-and-call-listp (make tests-and-call
                                                 :tests 1
                                                 :call 2))))
