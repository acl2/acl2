; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../pointed-integers")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-pointed-integer-rules
  :short "Rules about pointed-to integers."

  (defruled schar-read-when-scharp
    (implies (scharp x)
             (equal (schar-read x)
                    x))
    :in-theory '(schar-read
                 schar-fix-when-scharp))

  (defruled uchar-read-when-ucharp
    (implies (ucharp x)
             (equal (uchar-read x)
                    x))
    :in-theory '(uchar-read
                 uchar-fix-when-ucharp))

  (defruled sshort-read-when-sshortp
    (implies (sshortp x)
             (equal (sshort-read x)
                    x))
    :in-theory '(sshort-read
                 sshort-fix-when-sshortp))

  (defruled ushort-read-when-ushortp
    (implies (ushortp x)
             (equal (ushort-read x)
                    x))
    :in-theory '(ushort-read
                 ushort-fix-when-ushortp))

  (defruled sint-read-when-sintp
    (implies (sintp x)
             (equal (sint-read x)
                    x))
    :in-theory '(sint-read
                 sint-fix-when-sintp))

  (defruled uint-read-when-uintp
    (implies (uintp x)
             (equal (uint-read x)
                    x))
    :in-theory '(uint-read
                 uint-fix-when-uintp))

  (defruled slong-read-when-slongp
    (implies (slongp x)
             (equal (slong-read x)
                    x))
    :in-theory '(slong-read
                 slong-fix-when-slongp))

  (defruled ulong-read-when-ulongp
    (implies (ulongp x)
             (equal (ulong-read x)
                    x))
    :in-theory '(ulong-read
                 ulong-fix-when-ulongp))

  (defruled sllong-read-when-sllongp
    (implies (sllongp x)
             (equal (sllong-read x)
                    x))
    :in-theory '(sllong-read
                 sllong-fix-when-sllongp))

  (defruled ullong-read-when-ullongp
    (implies (ullongp x)
             (equal (ullong-read x)
                    x))
    :in-theory '(ullong-read
                 ullong-fix-when-ullongp))

  (defval *atc-pointed-integer-rules*
    '(schar-read-when-scharp
      uchar-read-when-ucharp
      sshort-read-when-sshortp
      ushort-read-when-ushortp
      sint-read-when-sintp
      uint-read-when-uintp
      slong-read-when-slongp
      ulong-read-when-ulongp
      sllong-read-when-sllongp
      ullong-read-when-ullongp)))
