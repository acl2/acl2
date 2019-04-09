; FTY -- Byte List Fixtype Instances
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "defbytelist")
(include-book "defbyte-instances")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbytelist-instances
  :parents (fty-extensions specific-types defbytelist)
  :short "Fixtypes of true lists of unsigned and signed bytes of various sizes,
          with some accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all generated via @(tsee defbytelist).")
   (xdoc::p
    "If fixtypes of true lists of unsigned or signed bytes of a certain size
     are needed but are not among the ones defined here,
     they can be added here.")
   (xdoc::p
    "These fixtypes are based on
     <see topic='@(url defbyte-instances)'>these fixtypes</see>.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defubytelist
  :parents (defbytelist-instances)
  :short "Specialized form of @(tsee defbytelist)
          for ``standard'' true lists of
          unsigned bytes of explicit integer sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro just takes a positive integer as input.")
   (xdoc::p
    "This macro generates fixtypes called @('acl2::ubyte<size>-list'),
     where @('<size>') consists of the decimal digits of the size.
     The recognizer, fixer, and equivalence are called
     @('acl2::ubyte<size>-listp'),
     @('acl2::ubyte<size>-list-fix'), and
     @('acl2::ubyte<size>-list-equiv').")
   (xdoc::p
    "This macro also generates
     some standardized XDOC parents and short, and no XDOC long.")
   (xdoc::@def "defubytelist"))

  (defmacro defubytelist (size)
    (declare (xargs :guard (posp size)))
    `(defbytelist
       ,(acl2::packn (list 'acl2::ubyte size '-list))
       :elt-type ,(acl2::packn (list 'acl2::ubyte size))
       :pred ,(acl2::packn (list 'acl2::ubyte size '-listp))
       :fix ,(acl2::packn (list 'acl2::ubyte size '-list-fix))
       :equiv ,(acl2::packn (list 'acl2::ubyte size '-list-equiv))
       :parents (defbytelist-instances)
       :short ,(concatenate
                'string
                "Fixtype of true lists of unsigned bytes of size "
                (coerce (explode-nonnegative-integer size 10 nil) 'string)
                "."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defsbytelist
  :parents (defbytelist-instances)
  :short "Specialized form of @(tsee defbytelist)
          for ``standard'' true lists of
          signed bytes of explicit integer sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro just takes a positive integer as input.")
   (xdoc::p
    "This macro generates fixtypes called @('acl2::sbyte<size>-list'),
     where @('<size>') consists of the decimal digits of the size.
     The recognizer, fixer, and equivalence are called
     @('acl2::sbyte<size>-listp'),
     @('acl2::sbyte<size>-list-fix'), and
     @('acl2::sbyte<size>-list-equiv').")
   (xdoc::p
    "This also generates
     some standardized XDOC parents and short, and no XDOC long.")
   (xdoc::@def "defsbytelist"))

  (defmacro defsbytelist (size)
    (declare (xargs :guard (posp size)))
    `(defbytelist
       ,(acl2::packn (list 'acl2::sbyte size '-list))
       :elt-type ,(acl2::packn (list 'acl2::sbyte size))
       :pred ,(acl2::packn (list 'acl2::sbyte size '-listp))
       :fix ,(acl2::packn (list 'acl2::sbyte size '-list-fix))
       :equiv ,(acl2::packn (list 'acl2::sbyte size '-list-equiv))
       :parents (defbytelist-instances)
       :short ,(concatenate
                'string
                "Fixtype of true lists of signed bytes of size "
                (coerce (explode-nonnegative-integer size 10 nil) 'string)
                "."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defubytelist 1)
(defubytelist 2)
(defubytelist 3)
(defubytelist 4)
(defubytelist 8)
(defubytelist 16)
(defubytelist 32)
(defubytelist 64)
(defubytelist 128)
(defubytelist 256)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsbytelist 1)
(defsbytelist 2)
(defsbytelist 3)
(defsbytelist 4)
(defsbytelist 8)
(defsbytelist 16)
(defsbytelist 32)
(defsbytelist 64)
(defsbytelist 128)
(defsbytelist 256)
