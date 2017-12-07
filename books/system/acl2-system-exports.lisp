; Copyright (C) 2017, ForrestHunt, Inc.
; Matt Kaufmann, October, 2017
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines two constants, *acl2-system-export-additions* and
; *acl2-system-exports*.  See :doc *acl2-system-exports*.  It also defines a
; corresponding package, so all of these definitions are in
; acl2-system-exports.acl2, not below.  All we do here is check that the (list)
; values of *acl2-system-exports* and *acl2-exports* are disjoint.  This
; probably isn't necessary; it just seems cleaner.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc *acl2-system-exports*
   :parents (packages)
   :short "An extension of @(tsee *acl2-exports*) that includes the names of
 many system-level ACL2 functions."

   :long "<p>It is common practice to import all symbols from @(tsee
 *acl2-exports*) into one's package; see @(see defpkg).  However, those who
 write ACL2 system-level programming utilities may prefer to import the symbols
 from the list @('*acl2-system-exports*'), which is a superset of
 @('*acl2-exports*') that includes the names of some useful system constants,
 functions, and macros; in particular, it includes the list of functions
 documented in @(see system-utilities).  Here are the symbols added to
 @('*acl2-exports*') to produce @('*acl2-system-exports*').</p>

 @(`(:code *acl2-system-exports-additions*)`)")
