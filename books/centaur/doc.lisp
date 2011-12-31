; Centaur Book Documentation
; Copyright (C) 2008-2011 Centaur Technology
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

(include-book "vl/top")
(include-book "vl/lint/lint")

(include-book "aig/aig-equivs")
(include-book "aig/aig-vars")
(include-book "aig/base")
(include-book "aig/bddify")
(include-book "aig/bddify-correct")
(include-book "aig/eval-restrict")
(include-book "aig/g-aig-eval")
(include-book "aig/induction")
(include-book "aig/misc")
(include-book "aig/three-four")
(include-book "aig/witness")

(include-book "ubdds/lite")
(include-book "ubdds/param")

(include-book "bitops/top")

(include-book "misc/alist-defs")
(include-book "misc/alist-equiv")
(include-book "misc/defapply")
(include-book "misc/equal-sets")
(include-book "misc/evaluator-metatheorems")
(include-book "misc/fast-alists")
(include-book "misc/f-put-global")
(include-book "misc/hons-extra")
(include-book "misc/hons-sets")
(include-book "misc/interp-function-lookup")
(include-book "misc/ls")
(include-book "misc/memory-mgmt-raw")
(include-book "misc/sneaky-load")
(include-book "misc/universal-equiv")
(include-book "misc/vecs-ints")
(include-book "misc/witness-cp")

(include-book "gl/gl")
(include-book "gl/bfr-aig-bddify")

; The following are included automatically by the xdoc::save command below, but
; we include them explicitly to support the hons `make' target in the books/
; directory (and hence the regression-hons `make' target in the acl2-sources
; directory).
(include-book "../xdoc-impl/save")
(include-book "../xdoc/defxdoc-raw")
(include-book "../xdoc-impl/mkdir-raw")
(include-book "../xdoc-impl/topics")
(include-book "../xdoc-impl/extra-packages")

(make-event
; xdoc::save is an event, so we might have just called it directly.  But for
; reasons Jared doesn't understand this is screwing up the extended manual we
; build at Centaur.  So, I'm putting the save event into a make-event to try
; to localize its effects to just this book's certification.
  (er-progn (xdoc::save "./manual")
            (value `(value-triple :manual))))
