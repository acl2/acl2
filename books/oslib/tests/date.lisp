; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "../date")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/strings/defs" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

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


(defconsts (*time1* state)
  (oslib::universal-time))

(value-triple (sleep 4))

(defconsts (*time2* state)
  (oslib::universal-time))

(assert! (let ((elapsed (- *time2* *time1*)))
           (or (and (<= 2 elapsed)
                    (<= elapsed 6))
               (cw "Slept for 4 seconds, but ~x0 seconds passed?  Error with universal-time or sleep?"
                   elapsed))))
