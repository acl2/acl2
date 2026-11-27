; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing author: J David Taylor (jdavidtaylor1@outlook.com)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set
  :parents (fty::fty-extensions fty::specific-types std/osets)
  :short
  (xdoc::topstring "A "
                   (xdoc::seetopic "fty::fty" "fixtype")
                   " of "
                   (xdoc::seetopic "std/osets" "osets")
                   ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "The fixing function used here is @(tsee sfix).")
   (xdoc::p
    "The name @('sequiv') of the equivalence relation introduced here
     is ``structurally similar'' to
     the name @('sfix') of the fixing function."))

  (fty::deffixtype set
    :pred setp
    :fix sfix
    :equiv sequiv
    :define t
    :forward t)

  (defcong sequiv equal (emptyp x) 1
    :hints (("Goal" :in-theory (enable emptyp))))

  (defcong sequiv equal (head x) 1
    :hints (("Goal" :in-theory (enable head))))

  (defcong sequiv equal (tail x) 1
    :hints (("Goal" :in-theory (enable tail))))

  (defcong sequiv equal (insert a x) 2
    :hints (("Goal" :in-theory (enable insert))))

  (defcong sequiv equal (cardinality x) 1
    :hints (("Goal" :in-theory (enable cardinality))))

  (defcong sequiv equal (delete a x) 2
    :hints (("Goal" :in-theory (enable delete))))

  (defcong sequiv equal (difference x y) 1
    :hints (("Goal" :in-theory (enable difference))))

  (defcong sequiv equal (difference x y) 2
    :hints (("Goal" :in-theory (enable difference))))

  (defcong sequiv equal (in a x) 2
    :hints (("Goal" :in-theory (enable in))))

  (defcong sequiv equal (intersect x y) 1
    :hints (("Goal" :in-theory (enable intersect))))

  (defcong sequiv equal (intersect x y) 2
    :hints (("Goal" :in-theory (enable intersect))))

  ;; While `INTERSECTP' is typically enabled, these two congruences avoid
  ;; `DOUBLE-REWRITE' warnings for some theorem statements.
  (defcong sequiv equal (intersectp x y) 1)

  (defcong sequiv equal (intersectp x y) 2)

  (defcong sequiv equal (subset x y) 1
    :hints (("Goal" :in-theory (enable subset))))

  (defcong sequiv equal (subset x y) 2
    :hints (("Goal" :in-theory (enable subset))))

  (defcong sequiv equal (union x y) 1
    :hints (("Goal" :in-theory (enable union))))

  (defcong sequiv equal (union x y) 2
    :hints (("Goal" :in-theory (enable union)))))
