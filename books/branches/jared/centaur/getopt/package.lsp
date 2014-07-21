; ACL2 Getopt Library
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
(include-book "oslib/portcullis" :dir :system)

(defpkg "GETOPT"
  (union-eq (set-difference-eq
             (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*)
             '(union delete))
            set::*sets-exports*
            std::*std-exports*
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
              std::formal
              std::formal-p
              std::formal->opts
              std::formal->name
              std::formallist-p
              std::formallist->names
              std::look-up-formals
              std::look-up-return-vals
              std::tuplep)))

#!GETOPT
(defconst *getopt-exports*
  '(getopt defoptions))

(defpkg "GETOPT-DEMO"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            getopt::*getopt-exports*
            '(acl2::rcons xdoc::defsection xdoc::defxdoc
                          b* oslib::argv)))

