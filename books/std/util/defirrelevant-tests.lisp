; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defirrelevant")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-integer
  :short "An irrelevant integer."
  :type integerp
  :body 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-symbol
  :short "An irrelevant symbol."
  :type symbolp
  :body nil)
