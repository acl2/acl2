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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-parser (parse-fn input-string)
  `(assert-event
    (b* ((,(if (eq parse-fn 'parse-external-declaration-list)
               '(mv erp & & & &)
             '(mv erp & & &))
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
 parse-external-declaration-list
 "typedef void foo;
struct bar
{
 int val;
};")
