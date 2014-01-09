; CUTIL - Centaur Basic Utilities
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

(in-package "STD")
(include-book "defmapappend")
(include-book "misc/assert" :dir :system)

(deflist my-nat-listp (x)
  (natp x)
  :elementp-of-nil nil)

(defund nats (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons n (nats (- n 1)))))

(defthm my-nat-listp-of-nats
  (my-nat-listp (nats n))
  :hints(("Goal" :in-theory (enable nats))))

(defprojection map-nats (x)
  (nats x)
  :guard (my-nat-listp x)
  :optimize nil)

(defmapappend append-nats (x)
  (nats x)
  :guard (my-nat-listp x))

(value-triple (map-nats (nats 5)))
(value-triple (append-nats (nats 5)))



(defmapappend m0 (x)
  (nats x)
  :guard (my-nat-listp x))

(assert! (let ((topic (xdoc::find-topic 'm0 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(acl2::undocumented)))))

(xdoc::set-default-parents foo bar)

(defmapappend m1 (x)
  (nats x)
  :guard (my-nat-listp x))

(assert! (let ((topic (xdoc::find-topic 'm1 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(foo bar)))))

(defmapappend m2 (x)
  (nats x)
  :guard (my-nat-listp x)
  :parents (bar))

(assert! (let ((topic (xdoc::find-topic 'm2 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(bar)))))


(defmapappend m3 (x)
  (nats x)
  :guard (my-nat-listp x)
  :parents nil)

(assert! (let ((topic (xdoc::find-topic 'm3 (xdoc::get-xdoc-table (w state)))))
           (not topic)))


