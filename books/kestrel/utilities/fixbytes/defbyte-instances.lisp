; Fixtypes of Unsigned and Signed Bytes of Various Sizes
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

(defxdoc defbyte-instances
  :parents (defbyte)
  :short "Fixtypes of unsigned and signed bytes of various sizes,
          with some accompanying theorems."
  :long
  (xdoc::topapp
   (xdoc::p
    "These are all generated via @(tsee defbyte).")
   (xdoc::p
    "If fixtypes of unsigned or signed bytes of a certain size
     are needed but are not among the ones defined here,
     they can be added here.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defubyte
  :parents (defbyte-instances)
  :short "Specialized form of @(tsee defbyte)
          for ``standard'' unsigned bytes of explicit integer sizes."
  :long
  (xdoc::topapp
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
   (xdoc::def "defubyte"))

  (defmacro defubyte (size)
    (declare (xargs :guard (posp size)))
    `(defbyte
       ,size
       :signed nil
       :type ,(acl2::packn (list 'acl2::ubyte size))
       :pred ,(acl2::packn (list 'acl2::ubyte size 'p))
       :fix ,(acl2::packn (list 'acl2::ubyte size '-fix))
       :equiv ,(acl2::packn (list 'acl2::ubyte size '-equiv))
       :parents (defbyte-instances)
       :description ,(concatenate
                      'string
                      "unsigned bytes of size "
                      (coerce (explode-nonnegative-integer size 10 nil)
                              'string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defsbyte
  :parents (defbyte-instances)
  :short "Specialized form of @(tsee defbyte)
          for ``standard'' signed bytes of explicit integer sizes."
  :long
  (xdoc::topapp
   (xdoc::p
    "This macro just takes a positive integer as input.")
   (xdoc::p
    "This macro generates fixtypes called @('acl2::sbyte<size>'),
     where @('<size>') consists of the decimal digits of the size.
     The recognizer, fixer, and equivalence are called
     @('acl2::sbyte<size>p'),
     @('acl2::sbyte<size>-fix'), and
     @('acl2::sbyte<size>-equiv').")
   (xdoc::p
    "This also generates
     some standardized XDOC parents and short, and no XDOC long.")
   (xdoc::def "defsbyte"))

  (defmacro defsbyte (size)
    (declare (xargs :guard (posp size)))
    `(defbyte
       ,size
       :signed t
       :type ,(acl2::packn (list 'acl2::sbyte size))
       :pred ,(acl2::packn (list 'acl2::sbyte size 'p))
       :fix ,(acl2::packn (list 'acl2::sbyte size '-fix))
       :equiv ,(acl2::packn (list 'acl2::sbyte size '-equiv))
       :parents (defbyte-instances)
       :description ,(concatenate
                      'string
                      "signed bytes of size "
                      (coerce (explode-nonnegative-integer size 10 nil)
                              'string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defubyte 1)
(defubyte 2)
(defubyte 3)
(defubyte 4)
(defubyte 8)
(defubyte 16)
(defubyte 32)
(defubyte 64)
(defubyte 128)
(defubyte 256)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsbyte 1)
(defsbyte 2)
(defsbyte 3)
(defsbyte 4)
(defsbyte 8)
(defsbyte 16)
(defsbyte 32)
(defsbyte 64)
(defsbyte 128)
(defsbyte 256)
