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

;; Must be included here, not in other-packages.lsp, for sets:: stuff
(ld "finite-set-theory/osets/sets.defpkg" :dir :system)

; We don't include deflist, etc., because even though writing cutil::defblah is
; ugly, it is more compatible with other books like data-structures/deflist
; that the user might also be using, whether directly or indirectly.

(defpkg "CUTIL"
  (set-difference-eq
   (union-eq (union-eq sets::*sets-exports*
              (union-eq *acl2-exports*
                        *common-lisp-symbols-from-main-lisp-package*))

             '(tag
               tag-reasoning
               cutil ; Makes ":xdoc cutil" do the right thing.
               defsection

               ;; Things I want to "import" from ACL2 into the CUTIL package.
               assert!
               b*
               progn$
               simpler-take
               repeat
               list-fix
               rev
               revappend-without-guard
               value
               two-nats-measure
               make-fal

               ;; BOZO consider moving these to cutil?
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

               ))
   ;; Things to remove:
   '(string-trim
     true-list-listp
     substitute
     union
     delete

     )))

#!CUTIL
(defconst *cutil-exports*
  '(tag
    tag-reasoning
    cutil
    defprojection
    deflist
    defalist
    defenum
    defaggregate
    defmapappend
    defmvtypes
    defsection))

(assign acl2::verbose-theory-warning nil)

