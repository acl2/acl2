; FTY -- Standard Unsigned Byte Fixtype Instance Generator
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "defbyte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defubyte
  :parents (defbyte-standard-instances)
  :short "Specialized form of @(tsee defbyte) for generating
          standard fixtypes of unsigned bytes of explicit integer sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro just takes a positive integer as input.")
   (xdoc::p
    "This macro generates fixtypes called @('acl2::ubyte<size>'),
     where @('<size>') consists of the decimal digits of the size.
     The recognizer, fixer, and equivalence are called
     @('acl2::ubyte<size>p'),
     @('acl2::ubyte<size>-fix'), and
     @('acl2::ubyte<size>-equiv').")
   (xdoc::p
    "This macro also generates
     some standardized XDOC parents and short, and no XDOC long.")
   (xdoc::@def "defubyte"))

  (defmacro defubyte (size)
    (declare (xargs :guard (posp size)))
    `(defbyte
       ,(acl2::packn (list 'acl2::ubyte size))
       :size ,size
       :signed nil
       :pred ,(acl2::packn (list 'acl2::ubyte size 'p))
       :fix ,(acl2::packn (list 'acl2::ubyte size '-fix))
       :equiv ,(acl2::packn (list 'acl2::ubyte size '-equiv))
       :parents (defbyte-standard-instances)
       :short ,(concatenate
                'string
                "Fixtype of unsigned bytes of size "
                (coerce (explode-nonnegative-integer size 10 nil) 'string)
                "."))))
