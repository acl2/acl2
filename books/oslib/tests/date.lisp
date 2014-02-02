; OSLIB -- Operating System Utilities
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
(include-book "../date")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/strings/defs" :dir :system)
(include-book "misc/assert" :dir :system)

(defconsts (*date* state)
  (oslib::date))

(assert! (stringp *date*))

(defconst *tokens* (str::strtok *date* '(#\Space #\, #\:)))

(assert! (equal (len *tokens*) 6))

(defconst *months* '("January" "February" "March" "April" "May" "June"
                     "July" "August" "September" "October" "November" "December"))

(defconsts (*month* *day* *year* *hour* *minute* *second*)
  (mv (first *tokens*)
      (str::strval (second *tokens*))
      (str::strval (third *tokens*))
      (str::strval (fourth *tokens*))
      (str::strval (fifth *tokens*))
      (str::strval (sixth *tokens*))))

(assert! (member-equal *month* *months*))
(assert! (and (natp *day*) (<= *day* 31)))
(assert! (and (natp *year*) (<= 2014 *year*)))
(assert! (and (natp *hour*) (<= *hour* 23)))
(assert! (and (natp *minute*) (<= *minute* 59)))
(assert! (and (natp *second*) (<= *second* 59)))


