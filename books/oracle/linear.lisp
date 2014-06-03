; Proof Script Using :Linear Rules
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

; The below example answers the question, "Can :linear rules with a
; conjunction of consequences be used effectively?"  When used in a simple
; example like this, the answer appears to be yes.

(in-theory
; Tau has some ability to reason about intervals, so we disable it.
 (disable (tau-system)))

(in-theory
; To reduce the amount of things we need to think about.
 (disable natp))

(defun foo (x)
  (min (expt 2 32) (+ (nfix x) (nfix x))))

(defun bar (x)
  (min (expt 2 64) (* (nfix x) 4)))


(defthm my-foo-bar-linear
  (and (<= (foo x) (expt 2 32))
       (<= (bar x) (expt 2 64)))
  :rule-classes :linear)

(in-theory (disable foo bar))

(defthm call-of-foo
; Uses my-foo-bar-linear
  (<= (foo x) (expt 2 40)))


; We've demonstrated the point, but our proof for baz-linear is slightly more
; fun, so we include it anyway.

(defun baz (x)
  (* (bar x) 2))

(defthm baz-linear
; Uses my-foo-bar-linear
  (<= (baz x) (expt 2 130)))
