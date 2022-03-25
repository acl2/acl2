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

(include-book "../defstruct")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This just tests DEFSTRUCT for now.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
