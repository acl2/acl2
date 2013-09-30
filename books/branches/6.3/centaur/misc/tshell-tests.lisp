; Centaur Miscellaneous Books
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
(include-book "tshell")

; Well, this is pretty pathetic.  But it's hard to test much here, e.g., how
; can we emulate interrupts, etc.?

(value-triple (tshell-ensure))

(defmacro test-tshell (&key cmd save print okp lines)
  (declare (ignorable cmd save print okp lines))
  #-(and Clozure (not mswindows))
  `(value-triple :invisible)
  #+(and Clozure (not mswindows))
  `(make-event
    (b* (((mv $finishedp $status $lines)
          (tshell-call ,cmd :save ,save :print ,print)))
      (and (or (equal $finishedp t)
               (er hard? 'test-tshell "Error: finished was ~x0~%" $finishedp))
           (or (equal (equal $status 0) ,okp)
               (er hard? 'test-tshell "Error: status was ~x0~%" $status))
           (or (equal ,lines :skip)
               (equal $lines ,lines)
               (er hard? 'test-tshell "Error: lines were ~x0~%" $lines)))
      '(value-triple :success))))

(test-tshell :cmd "echo hello"
             :save t
             :print t
             :okp t
             :lines '("hello"))

(test-tshell :cmd "echo hello"
             :save t
             :print nil
             :okp t
             :lines '("hello"))

(test-tshell :cmd "echo hello"
             :save nil
             :print nil
             :okp t
             :lines nil)

(test-tshell :cmd "ls -1 tshell-tests.lisp"
             :save t
             :print t
             :okp t
             :lines '("tshell-tests.lisp"))

; Matt K., 8/11/2013: Commenting out the following test, at Jared's suggestion,
; since it is failing on a Mac.
#||
(test-tshell :cmd "ls -1 tshell.lisp tshell-tests.lisp"
             :save t
             :print t
             :okp t
             :lines '("tshell.lisp" "tshell-tests.lisp"))
||#

(test-tshell :cmd "ls file-that-should-not-exist.txt"
             :save t
             :print t
             :okp nil
             :lines :skip)

(test-tshell :cmd "ls file-that-should-not-exist.txt"
             :save nil
             :print t
             :okp nil
             :lines nil)
