; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../defpred")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpred unambp
  :default t
  :override
  ((expr :sizeof-ambig nil)
   (expr :cast/call-ambig nil)
   (expr :cast/mul-ambig nil)
   (expr :cast/add-ambig nil)
   (expr :cast/sub-ambig nil)
   (expr :cast/and-ambig nil)
   (type-spec :typeof-ambig nil)
   (align-spec :alignas-ambig nil)
   (stmt :for-ambig nil)))
