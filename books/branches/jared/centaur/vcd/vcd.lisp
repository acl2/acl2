; VCD Generator for ESIM
; Copyright (C) 2010-2012 Centaur Technology
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
(include-book "vcd-stub")
(include-book "esim-snapshot")

; This elaborate stub and redefinition nonsense lets the user include the vcd
; book without getting all the VL theory stuff.

#||
(include-book "vcd-impl") ;; for the dependency scanner
||#

(make-event
 (let ((vcd-impl (extend-pathname (cbd) "vcd-impl" state)))
   `(defconst *vcd-impl* ',vcd-impl)))

(defmacro install-vcd-dump ()
  `(include-book ,*vcd-impl*))

(defmacro vcd-dump (filename snapshots
                             &key (viewer '"gtkwave")
                             emap)
  `(encapsulate
     ()
     (local (include-book ,*vcd-impl*))
     (make-event
      (let ((state (vl::vcd-dump-fn ,filename ,snapshots ,viewer ,emap state)))
        (value '(value-triple :invisible))))))


