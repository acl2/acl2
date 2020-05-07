; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmacro-plus")

(include-book "std/testing/must-succeed" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents nil
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :parents nil))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :parents (some-parent)))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent another-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :parents (some-parent another-parent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents nil
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents nil
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents nil))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents (some-parent)))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent another-parent)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent another-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents (some-parent another-parent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents nil
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents nil
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   :parents nil
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)
   :parents nil))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)
   :parents (some-parent)))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent another-parent)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent another-parent)
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   :parents (some-parent another-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)
   :parents (some-parent another-parent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :short "a short string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :short "a short string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)
   :short "a short string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   (declare (xargs :guard (stringp y)))
   `(list ,x ,y)
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   `(list ,x ,y)
   :short "a short string"))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :parents (some-parent)
   :short "a short string"))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   `(list ,x ,y)
   :parents (some-parent)))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :short "a short string"
   :parents (some-parent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :short "a short string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   `(list ,x ,y)
   :short "a short string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents (some-parent)
   :short "a short string"))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents (some-parent)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   `(list ,x ,y)
   :parents (some-parent)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :short "a short string"
   :parents (some-parent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :parents (some-parent)
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   `(list ,x ,y)
   :parents (some-parent)))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :long "a long string"
   :parents (some-parent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents (some-parent)
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents (some-parent)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   :parents (some-parent)
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   `(list ,x ,y)
   :parents (some-parent)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :long "a long string"
   :parents (some-parent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :short "a short string"
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   `(list ,x ,y)
   :short "a short string"))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :long "a long string"
   :short "a short string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :short "a short string"
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :short "a short string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   :short "a short string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   `(list ,x ,y)
   :short "a short string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :long "a long string"
   :short "a short string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :short "a short string"
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :short "a short string"
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   `(list ,x ,y)
   :short "a short string"
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   `(list ,x ,y)
   :parents (some-parent)
   :short "a short string"
   :long "a long string"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :short "a short string"
   :long "a long string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   :short "a short string"
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   :parents (some-parent)
   (declare (xargs :guard (symbolp x)))
   :short "a short string"
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   :short "a short string"
   :long "a long string"
   `(list ,x ,y)))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   :short "a short string"
   `(list ,x ,y)
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   :parents (some-parent)
   `(list ,x ,y)
   :short "a short string"
   :long "a long string"))

(must-succeed
 (defmacro+ mac (x y)
   (declare (xargs :guard (symbolp x)))
   `(list ,x ,y)
   :parents (some-parent)
   :short "a short string"
   :long "a long string"))
