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
(local (include-book "arithmetic"))

(defsection vl-nat-values-p

  (defund vl-nat-values-p (x)
    (declare (xargs :guard t))
    (or (atom x)
        (and (consp (car x))
             (natp (cdar x))
             (vl-nat-values-p (cdr x)))))

  (local (in-theory (enable vl-nat-values-p)))

  (defthm vl-nat-values-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-nat-values-p x)
                    t)))

  (defthm vl-nat-values-p-of-cons
    (equal (vl-nat-values-p (cons a x))
           (and (natp (cdr a))
                (vl-nat-values-p x))))

  (defthm vl-nat-values-p-of-hons-shrink-alist
    (implies (and (vl-nat-values-p x)
                  (vl-nat-values-p ans))
             (vl-nat-values-p (hons-shrink-alist x ans)))
    :hints(("Goal" :in-theory (e/d (hons-shrink-alist)
                                   ((force))))))

  (defthm natp-of-cdr-of-hons-assoc-equal-when-vl-nat-values-p
    (implies (vl-nat-values-p x)
             (equal (natp (cdr (hons-assoc-equal a x)))
                    (if (hons-assoc-equal a x)
                        t
                      nil)))))
