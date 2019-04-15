; FTY -- Standard Unsigned Byte List Fixtype Instance Generator
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "defbytelist")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defubytelist
  :parents (defbytelist-standard-instances)
  :short "Specialized form of @(tsee defbytelist)
          for generating standard fixtypes
          of true lists of unsigned bytes of explicit integer sizes."
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
       :parents (defbytelist-standard-instances)
       :short ,(concatenate
                'string
                "Fixtype of true lists of unsigned bytes of size "
                (coerce (explode-nonnegative-integer size 10 nil) 'string)
                "."))))
