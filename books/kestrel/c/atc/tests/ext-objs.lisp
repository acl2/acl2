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

(include-book "../defobject")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some tests of DEFOBJECT.

(c::defobject |arr|
  :type (c::sint 5)
  :init ((c::sint-dec-const 1)
         (c::sint-dec-const 2)
         (c::sint-dec-const 3)
         (c::sint-dec-const 4)
         (c::sint-dec-const 5)))

(c::defobject |perm|
    :type (c::uchar 3)
    :init ((c::uchar-from-sint (c::sint-hex-const 17))
           (c::uchar-from-sint (c::sint-hex-const 2))
           (c::uchar-from-sint (c::sint-oct-const 22))))
