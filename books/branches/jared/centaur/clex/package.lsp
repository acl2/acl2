; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

(defpkg "CLEX"
  (set-difference-eq
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*
             std::*std-exports*
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
               nat-equiv int-equiv

               str::defcharset
               str::charset-p
               str::char-in-charset-p
               str::code-in-charset-p
               str::chars-in-charset-p
               str::count-leading-charset
               str::str-count-leading-charset
               str::str-count-leading-charset-fast

               ))
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

    ;; For lexer progress properties
    strin-left
    def-sin-progress
    ))
