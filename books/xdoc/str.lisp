; XDOC Documentation System for ACL2
; Copyright (C) 2009-2014 Centaur Technology
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

; str.lisp
;
; This is basically similar to books such as std/strings/defs.lisp or
; std/strings/defs-program.lisp.  However, instead of trying to comprehensively
; load the whole string library, we only load a few definitions that we
; actually need.  This helps to avoid horrible circularities in the
; dependencies of various files.

(in-package "XDOC")
(include-book "tools/bstar" :dir :system)
(include-book "std/basic/defs" :dir :system)
(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "make-event/acl2x-help" :dir :system))
; (include-book "std/lists/list-defuns" :dir :system)
(program)
; cert_param (acl2x)
; cert_param (acl2xskip)

(acl2::acl2x-replace (include-book
                      "std/strings/cat" :dir :system)
                     (value-triple :invisible)
                     :outside-certification
                     (include-book
                      "std/strings/cat" :dir :system))

(acl2::acl2x-replace (include-book
                      "std/strings/case-conversion" :dir :system)
                     (value-triple :invisible)
                     :outside-certification
                     (include-book
                      "std/strings/case-conversion" :dir :system))

(acl2::acl2x-replace (include-book
                      "std/strings/strsubst" :dir :system)
                     (value-triple :invisible)
                     :outside-certification
                     (include-book
                      "std/strings/strsubst" :dir :system))

(acl2::acl2x-replace (include-book
                      "std/strings/decimal" :dir :system)
                     (value-triple :invisible)
                     :outside-certification
                     (include-book
                      "std/strings/decimal" :dir :system))

(program)

(make-event
 (b* ((events (std::defredundant-fn '(str::cat
                                      str::implode
                                      acl2::implode$inline
                                      str::explode
                                      acl2::explode$inline
                                      str::rchars-to-string
                                      str::fast-concatenate
                                      str::fast-string-append
                                      str::fast-string-append-lst
                                      str::revappend-chars-aux
                                      str::revappend-chars
                                      str::revappend-chars$inline
                                      str::little-a
                                      str::little-z
                                      str::big-a
                                      str::big-z
                                      str::down-alpha-p
                                      str::down-alpha-p$inline
                                      str::up-alpha-p
                                      str::up-alpha-p$inline
                                      str::charlist-has-some-up-alpha-p
                                      str::charlist-has-some-down-alpha-p
                                      str::string-has-some-down-alpha-p
                                      str::string-has-some-up-alpha-p
                                      str::case-delta
                                      str::downcase-char
                                      str::downcase-char$inline
                                      str::downcase-charlist-aux
                                      str::downcase-charlist
                                      str::downcase-string-aux
                                      str::downcase-string
                                      str::upcase-char
                                      str::upcase-char$inline
                                      str::upcase-charlist-aux
                                      str::upcase-charlist
                                      str::upcase-string-aux
                                      str::upcase-string
                                      str::strprefixp-impl
                                      str::strsubst-aux
                                      str::strsubst
                                      str::make-upcase-first-strtbl
                                      str::*upcase-first-strtbl*
                                      str::upcase-first-charlist
                                      str::upcase-char-str$inline
                                      str::upcase-char-str
                                      str::upcase-first
                                      str::join-aux
                                      str::join
                                      str::join$inline
                                      str::basic-natchars
                                      str::natchars-aux
                                      str::natchars
                                      str::natchars$inline
                                      str::natstr
                                      str::natstr$inline
                                      )
                t
                state)))
   (acl2::value events)))




