; Centaur Lexer Library
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
(include-book "str/portcullis" :dir :system)

(defpkg "CLEX"
  (set-difference-eq
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*
             cutil::*cutil-exports*
             '(quit
               exit
               b*
               clex ;; for xdoc listings
               list-fix prefixp sublistp listpos
               assert!
;               a b c d e f g h i j k l m n o p q r s t u v w x y z
               lnfix lifix lbfix
               defxdoc defsection definline definlined
               defabsstobj-events
               unsigned-byte-p signed-byte-p
               unsigned-byte-listp
               explode implode
               str::cat str::natstr
               nat-equiv int-equiv))
   '(number-char-p digit-char-p sin)))

#!CLEX
(defconst *clex-exports*
  '(;; Sin and its accessors, since the user will need them
    sin
    sin-init
    sin-line
    sin-col
    sin-file
    sin-endp
    sin-len
    sin-car
    sin-nth
    sin-firstn
    sin-cdr
    sin-nthcdr
    sin-matches-p
    sin-imatches-p
    sin-count-charset
    sin-find

    ;; Matching function stuff, expected to be used by the user
    sin-match-everything
    sin-match-lit
    sin-match-some-lit
    sin-match-charset*
    sin-match-until-lit
    sin-match-through-lit

    ;; Basic charset stuff (but not more advanced, custom functions)
    defcharset
    charset-p
    char-in-charset-p
    code-in-charset-p
    chars-in-charset-p

    ;; For lexer progress properties
    strin-left
    def-sin-progress
    ))
