; ACL2 Getopt Library
; Copyright (C) 2013 Centaur Technology
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

(include-book "cutil/portcullis" :dir :system)

(defpkg "GETOPT"
  (union-eq (set-difference-eq
             (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*)
             '(union delete))
            sets::*sets-exports*
            cutil::*cutil-exports*
            '(;; Things we want to "export", for nicer use from other
              ;; packages.
              getopt
              defoptions
              ;; Things we want to "import"
              quit
              exit
              b*
              getopt
              assert!
              list-fix
              rcons
              prefixp
              lnfix
              lifix
              lbfix
              xdoc
              defxdoc
              defsection
              definline
              definlined
              unsigned-byte-p
              signed-byte-p
              str::explode
              str::implode
              str::cat
              str::natstr
              str::join
              uniquep
              duplicated-members
              msg
              value
              def-ruleset
              enable*
              disable*
              e/d*
              cutil::formal
              cutil::formal-p
              cutil::formal->opts
              cutil::formal->name
              cutil::formallist-p
              cutil::formallist->names
              cutil::look-up-formals
              cutil::look-up-return-vals
              cutil::tuplep)))

#!GETOPT
(defconst *getopt-exports*
  '(getopt defoptions))

(defpkg "GETOPT-DEMO"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            getopt::*getopt-exports*
            '(acl2::rcons)))

