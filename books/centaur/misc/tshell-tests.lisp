; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "tshell")
(include-book "std/strings/defs" :dir :system) ; for str::strprefixp

; Well, this is pretty pathetic.  But it's hard to test much here, e.g., how
; can we emulate interrupts, etc.?

(defttag :custom-printing)

(progn!
 (set-raw-mode t)
 (defun my-print (line rlines stream)
   (declare (ignorable rlines))
   (if (str::strprefixp "(test-tshell" line)
       (progn (write-line line stream)
              (force-output stream))
     nil)))

(value-triple (tshell-ensure))

(defmacro test-tshell (&key cmd save print okp lines)
  (declare (ignorable cmd save print okp lines))
  `(make-event
    (b* (((mv $status $lines)
          (tshell-call ,cmd :save ,save :print ,print)))
      (and (or (equal (equal $status 0) ,okp)
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

;; Switching to shellpool broke this.  BOZO Reinstate this once the bug is fixed.
;;   http://github.com/jaredcdavis/shellpool/issues/11
;;
;; (test-tshell :cmd "echo -n hello"
;;              :save t
;;              :print t
;;              :okp t
;;              :lines '("hello"))

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

;; This should just print a few (test-shell ...) lines.

(test-tshell :cmd "cat tshell-tests.lisp"
             :save t
             :print 'my-print
             :okp t
             :lines :skip)
