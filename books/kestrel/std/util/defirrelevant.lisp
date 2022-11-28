; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ defirrelevant (name &key type body short)
  :parents (std/util std::std/util-extensions)
  :short "Define an irrelevant value of a type."
  `(define ,name ()
     :returns (irr ,type)
     :short ,short
     :long
     (xdoc::topstring
      (xdoc::p
       "This can be used as a dummy value of the type."))
     ,body
     ///
     (in-theory (disable (:e ,name)))))
