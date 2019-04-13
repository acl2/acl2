; FTY -- Standard Signed Byte List Fixtype Instance Generator
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

(defsection defsbytelist
  :parents (defbytelist-standard-instances)
  :short "Specialized form of @(tsee defbytelist)
          for generating standard fixtypes
          of true lists of signed bytes of explicit integer sizes."
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
       :parents (defbytelist-standard-instances)
       :short ,(concatenate
                'string
                "Fixtype of true lists of signed bytes of size "
                (coerce (explode-nonnegative-integer size 10 nil) 'string)
                "."))))
