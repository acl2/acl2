; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/defstruct" :dir :system)

(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some tests for DEFSTRUCT.

(c::defstruct |point2D|
  (|x| c::sint)
  (|y| c::sint))

(c::defstruct |point3D|
  (|x| c::slong)
  (|y| c::slong)
  (|z| c::slong))

(c::defstruct |integers|
  (|uchar| c::uchar)
  (|schar| c::schar)
  (|ushort| c::ushort)
  (|sshort| c::sshort)
  (|uint| c::uint)
  (|sint| c::sint)
  (|ulong| c::ulong)
  (|slong| c::slong)
  (|ullong| c::ullong)
  (|sllong| c::sllong))

(c::defstruct |scalar_and_array|
  (|scalar| c::sint)
  (|aggreg| (c::uchar 10)))

(c::defstruct |flex|
  (|fixed| (c::uchar 5))
  (|filler| c::uint)
  (|last| (c::uchar)))

(encapsulate ()
  (local (in-theory ()))
  (c::defstruct |big_struct|
    (|a| c::uint)
    (|b| (c::uint 5))
    (|c| (c::sllong 200))
    (|d| c::slong)
    (|e| c::ulong)
    (|f| c::schar)
    (|g| c::ushort)
    (|h| c::sshort)
    (|i| c::uint)
    (|j| c::sint)
    (|k| (c::uchar))))

(c::defstruct |two_arrays|
  (|foo| (c::uchar 2))
  (|bar| (c::uchar 2)))

(must-fail
 (c::defstruct |empty|))

(must-fail
 (c::defstruct |only_flexible_array_member|
   (|fam| (c::sllong))))
