; Proof Script Using :Type-prescription Rules
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
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
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

; The below example answers the question, "Can type-prescription rules with a
; conjunction of consequences be used effectively?"  When used in a simple
; example like this, the answer appears to be "yes".

(in-theory
; Tau will prove whatever simple tests we concoct, so we disable it.
 (disable (tau-system)))

(in-theory
; To reduce the amount of things we need to think about.
 (disable natp))

(defund foo (x)
  (* (nfix x) 2))

(defund bar (x)
  (* (nfix x) 4))

(defthm my-foo-type
  (and (natp (foo x))
       (integerp (foo x)))
  :rule-classes :type-prescription)

(defthm call-of-bar
  (implies (natp x)
           (natp (bar x))))

(in-theory
; Disable the automatically generated type-prescription rules.  We do this
; now instead of earlier, because we needed the :type-prescription for bar to
; prove call-of-bar.
 (disable (:type-prescription foo) (:type-prescription bar)))


(defthm use-foo-app
; Proving this theorem in the current theory requires using call-of-bar.  When
; call-of-bar goes to relieve its hypothesis, it will use the
; :type-prescription rule my-foo-type.  Thus, we know ACL2 is able to use
; conclusions that have more than one type description.
  (natp (bar (foo x))))
