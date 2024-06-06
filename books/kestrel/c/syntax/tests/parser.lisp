; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../parser")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-parser (parse-fn input-string)
  `(assert-event
    (b* (((mv erp & & &)
          (,parse-fn (init-parstate (acl2::string=>nats ,input-string)))))
      (if erp
          (cw "~@0" erp) ; CW returns nil, so ASSERT-EVENT fails
        t)))) ; ASSERT-EVENT passes

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-declaration-specifier
 "struct mystruct
{
   int *val;
};")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-declaration-specifier
 "typedef void foo;
struct bar
{
 int val;
};")
