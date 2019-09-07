; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "library-extensions")

(include-book "std/util/defaggregate" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-test-structures
  :parents (atj-implementation)
  :short "Structures that store user-specified tests."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atj-test
  :short "Recognize a processed test specified by the @(':tests') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each test specified by the @(':tests') input
     must the form @('(namej termj)'),
     where @('termj') must translate to @('(fn qc1 qc2 ...)'),
     as explained in the documentation.
     As the @(':tests') input is processed,
     the information about each test is stored
     into an aggregate of this type.
     This aggregate stores
     @('namej'),
     @('fn'),
     The list of values of the quoted constants @('qc1'), @('qc2'), etc.,
     and the result of the ground call @('(fn qc1 qc2 ...)')."))
  ((name "This is @('namej')." stringp)
   (function "This is @('fn')." symbolp)
   (arguments "This is the list of values of @('qc1'), @('qc2'), etc."
              true-listp)
   (result "This is the result of @('(fn qc1 qc2 ...)')."))
  :pred atj-testp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-test-listp (x)
  :short "Recognize true lists of processed tests
          specified by the @(':tests') input."
  (atj-testp x)
  :true-listp t
  :elementp-of-nil nil)
