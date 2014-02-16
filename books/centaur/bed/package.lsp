; Centaur BED Library
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
; Original authors: Jared Davis <jared@centtech.com>

(include-book "std/portcullis" :dir :system)

(defpkg "BED"
  (set-difference-eq
   (union-eq std::*std-exports*
             set::*sets-exports*
             acl2::*acl2-exports*
             acl2::*common-lisp-symbols-from-main-lisp-package*
             '(set::enable
               set::disable
               set::e/d
               str::cat
               str::natstr
               str::implode
               str::explode
               enable*
               disable*
               e/d*

               b*

               bitp
               bfix
               lnfix
               lifix
               lbfix
               nat-equiv
               int-equiv
               bit-equiv
               bool->bit

               b-not
               b-eqv
               b-xor
               b-ior
               b-nor
               b-and
               b-nand
               b-orc2
               b-orc1
               b-andc1
               b-andc2

               logcar
               logcdr
               loghead
               logtail
               arith-equiv-forwarding

               aig-eval
               aig-env-lookup
               aig-not
               aig-iff
               aig-xor
               aig-and
               aig-or
               aig-ite
               aig-vars
               aig-vars-1pass
               ))
   '(acl2::union
     acl2::delete
     acl2::enable
     acl2::disable
     acl2::e/d
     )))
