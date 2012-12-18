; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
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

(ld "xdoc/package.lsp" :dir :system)

(defpkg "STR"
  (set-difference-eq
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*
             '(quit exit simpler-take list-fix prefixp str b* assert!
                    a b c d e f g h i j k l m n o p q r s t u v w x y z)
             '(defxdoc defsection lnfix definlined definline))

   ;; Remove some "bad" acl2 string functions to try to prevent users from
   ;; accidentally using them.
   '(upper-case-p
     lower-case-p
     char-upcase
     char-downcase
     string-upcase1
     string-downcase1
     string-upcase
     string-downcase)))
