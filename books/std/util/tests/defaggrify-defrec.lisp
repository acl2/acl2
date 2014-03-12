; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

; Tests for defaggrify-defrec utility.

(in-package "ACL2")
(include-book "../defaggrify-defrec")

;; Just a handful of defrec from the ACL2 sources.

(std::defaggrify-defrec rewrite-rule)
(std::defaggrify-defrec def-body)
(std::defaggrify-defrec io-record)
(std::defaggrify-defrec state-vars)
(std::defaggrify-defrec gag-info)
(std::defaggrify-defrec rewrite-constant)
(std::defaggrify-defrec attachment)
(std::defaggrify-defrec clause-id)
(std::defaggrify-defrec assumption)
(std::defaggrify-defrec justification)





