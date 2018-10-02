; Bitcoin Library -- Extensions of Other Libraries
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/digits-any-base/pow2-8" :dir :system)
(include-book "kestrel/utilities/lists/index-of-theorems" :dir :system)
(include-book "kestrel/utilities/lists/rev-theorems" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These will be moved to the appropriate libraries.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ubyte8-fix-rewrite-dab-digit-fix-256
  (equal (ubyte8-fix digits)
         (dab-digit-fix 256 digits))
  :enable (ubyte8-fix dab-digit-fix dab-digitp ubyte8p))

(defruled ubyte8-list-fix-rewrite-dab-digit-list-fix-256
  (equal (ubyte8-list-fix digits)
         (dab-digit-list-fix 256 digits))
  :enable (dab-digit-list-fix
           ubyte8-list-fix
           ubyte8-fix-rewrite-dab-digit-fix-256))

(defcong ubyte8-list-equiv ubyte8-list-equiv (append x y) 1)

(defcong ubyte8-list-equiv ubyte8-list-equiv (append x y) 2)
