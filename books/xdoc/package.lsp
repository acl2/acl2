; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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

;; Truly gross hack.  For the bookdoc stuff to work, we need to have all of
;; the packages available.

(ld "cowles/packages.lsp" :dir :system)
(ld "clause-processors/SULFA/books/sat/sat-package.acl2" :dir :system)
(ld "data-structures/define-u-package.lsp" :dir :system)
(ld "data-structures/define-structures-package.lsp" :dir :system)
(ld "data-structures/memories/package.lsp" :dir :system)
(ld "hacking/hacker-pkg.lsp" :dir :system)
(ld "cutil/package.lsp" :dir :system)
(ld "serialize/package.lsp" :dir :system)
(ld "str/package.lsp" :dir :system)
(ld "tools/flag-package.lsp" :dir :system)

(defpkg "XDOC"
  (set-difference-eq
   (union-eq (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*)
             ;; Things to add:
             '(b* quit exit value defxdoc defxdoc-raw macro-args
                  getprop formals justification def-bodies current-acl2-world def-body
                  access theorem untranslated-theorem guard xdoc xdoc! unquote))
   ;; Things to remove:
   '(
     )))
