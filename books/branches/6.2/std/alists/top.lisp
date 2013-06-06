; Standard Association Lists Library
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
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")

; This is Jared's preferred way to load the alist library and get a decent
; theory.  If you want to keep functions like ALISTP and STRIP-CARS enabled,
; you can include the individual books, which mostly try to leave the default
; theory alone.

(include-book "../lists/top")

(include-book "alist-defuns")
(include-book "alistp")
(include-book "alist-keys")
(include-book "alist-vals")
(include-book "alist-equiv")
(include-book "alists-compatible")
(include-book "fal-extract")
(include-book "fal-extract-vals")
(include-book "hons-assoc-equal")
(include-book "hons-rassoc-equal")
(include-book "strip-cars")
(include-book "strip-cdrs")
(include-book "pairlis")


(in-theory (disable alistp
                    hons-assoc-equal
                    strip-cars
                    strip-cdrs
                    pairlis$
                    ))


