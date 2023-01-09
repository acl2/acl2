; Standard System Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the community-books file 3BSD-mod.txt.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/good-atom-listp
  :parents (std/system)
  :short "Theorems about @(tsee good-atom-listp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('good-atom-listp-of-cons') theorem is useful
     to verify the guards of calls of @(tsee packn) or @(tsee packn-pos)
     on lists of good atoms, as these functions are often used.
     We order the disjuncts in the right side of this rewrite rule
     roughly according to the supposed relative frequency
     of the different types of good atoms:
     it seems that symbols would be the most common,
     followed by numbers (e.g. for indices),
     then strings (which can be often avoided, using symbols instead),
     then characters (which may be just written as symbols or strings).
     Note that we expect the @('nil') case to be taken care of by
     the executable counterpart of @(tsee good-atom-listp)."))

  (defthm good-atom-listp-of-cons
    (equal (good-atom-listp (cons x y))
           (and (or (symbolp x)
                    (acl2-numberp x)
                    (stringp x)
                    (characterp x))
                (good-atom-listp y)))
    :hints (("Goal" :in-theory (enable state-p)))))

(in-theory (disable good-atom-listp))
