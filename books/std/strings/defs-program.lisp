; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>
; mostly copied from defs.lisp by Jared Davis <jared@centtech.com>
;
; Modified by Jared to pull out the common part into defs-aux.lisp

(in-package "STR")
(include-book "std/basic/defs" :dir :system)
(include-book "tools/bstar" :dir :system)
;(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "make-event/acl2x-help" :dir :system))
; (include-book "std/lists/list-defuns" :dir :system)
(local (include-book "defs-aux"))
(program)
; cert_param (acl2x)
; cert_param (acl2xskip)

; (depends-rec "top")
(acl2::acl2x-replace (include-book
                      "top")
                     (value-triple :invisible)
                     :outside-certification
                     (include-book
                      "top"))

(program)

(make-event
 (b* ((events (std::defredundant-fn *str-library-basic-defs* t state)))
   (acl2::value events)))

