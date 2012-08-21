; VL Verilog Toolkit
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

(in-package "VL")
(include-book "defs")
(include-book "misc/hons-help" :dir :system)
(local (include-book "arithmetic"))


(defund clean-alist (x)
  (declare (xargs :guard t))
  (b* ((fal    (acl2::make-fal x nil))
       (shrink (hons-shrink-alist fal nil))
       (-      (flush-hons-get-hash-table-link fal))
       (-      (flush-hons-get-hash-table-link shrink)))
      shrink))

(local (in-theory (enable clean-alist)))

(defthm alistp-of-clean-alist
  (alistp (clean-alist x)))

(defthm hons-assoc-equal-of-clean-alist
  (equal (hons-assoc-equal a (clean-alist x))
         (hons-assoc-equal a x)))


