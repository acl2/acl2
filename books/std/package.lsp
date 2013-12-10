; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

; We load these here now so we can import their symbols into std/util as desired.
(include-book "str/portcullis" :dir :system)
(include-book "xdoc/portcullis" :dir :system)
(include-book "osets/portcullis")
(include-book "bitsets/portcullis" )

(defconst *std-pkg-symbols*
  (set-difference-eq
   (union-eq (union-eq sets::*sets-exports*
                       (union-eq *acl2-exports*
                                 *common-lisp-symbols-from-main-lisp-package*))
             '(std ; Makes ":xdoc std" do the right thing.
               std/util ;; likewise

; Things I want to "export" to the ACL2 package.
;
; Should we export deflist, defalist, etc.?  On one hand, it would be nice NOT
; to export them since this makes these parts of the std library incompatible
; with books like data-structures/deflist.  On the other hand, it is ugly to
; type (std::deflist ...) instead of just deflist.
;
; I've gone back and forth on it.  I guess exporting them is bad.  I'll
; continue to export defsection and defmvtypes since they're unusually named
; and convenient, but for consistency all of the data-type introduction macros
; will be kept in the std package.

               __function__
               raise
               tag
               tag-reasoning
               defsection
               defsection-progn
               defmvtypes
               defrule
               defruled
               define
               defconsts
               xdoc
;               defaggregate
;               defenum
;               defprojection
;               defmapappend
;               defalist
;               deflist

               ;; Things I want to "import" from ACL2 into the STD package.
               assert!
               b*
               progn$
               simpler-take
               repeat
               list-fix
               rev
               rcons
               revappend-without-guard
               value
               two-nats-measure
               make-fal
               xdoc-extend
               legal-variablep
               set-equiv
               list-equiv
               never-memoize

               ;; BOZO consider moving these to std?
               defconsts
               definline
               definlined

               ;; BOZO why aren't these imported?
               strip-cadrs
               defxdoc

               uniquep
               duplicated-members

               alists-agree
               alist-keys
               alist-vals
               alist-equiv
               sub-alistp
               hons-rassoc-equal

               def-ruleset
               def-ruleset!
               add-to-ruleset
               add-to-ruleset!
               get-ruleset
               ruleset-theory

               ;; Stuff I moved into xdoc:
               xdoc::extract-keyword-from-args
               xdoc::throw-away-keyword-parts
               xdoc::mksym
               xdoc::mksym-package-symbol
               undocumented
               ))
   ;; Things to remove:
   '(string-trim
     true-list-listp
     substitute
     union
     delete
     nat-listp ; included 12/4/2012 by Matt K., for addition to *acl2-exports*
     )))

(defpkg "STD" *std-pkg-symbols*)

#!STD
(defconst *std-exports*
  '(std
    tag
    tag-reasoning
    defprojection
    deflist
    defalist
    defenum
    defaggregate
    defmapappend
    defmvtypes
    defsection
    defsection-progn
    define
    defrule
    defruled
    raise
    __function__))

(assign acl2::verbose-theory-warning nil)

