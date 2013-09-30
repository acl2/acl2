; Intern Debugging
; Copyright (C) 2010 Centaur Technology
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
(include-book "tools/include-raw" :dir :system)
; (depends-on "intern-debugging-raw.lsp")


(defxdoc intern-debugging
  :parents (intern-in-package-of-symbol intern$)
  :short "A debugger that can warn you about slow @('intern')ing. (CCL only)"

  :long "<p>Jared once spent many hours trying to figure out why some
computation was slow, only to discover that he was getting bitten by repeatedly
growing a package by small amounts.  This performance problem is hard to debug
because it is hard to reproduce (once the package has been grown, the same
computation you are debugging suddenly runs much faster), and also because it
is unusual: you would generally expect @('intern') to be a constant-time, cheap
operation.</p>

<p>The book @('centaur/misc/intern-debugging') is a debugger that can notice
and report on slow calls of @('intern') due to package growth.  It only works
on CCL.</p>

<p>The book redefines the primitive Common Lisp function @('intern') so that
some debugging messages are printed when the package is resized.  Obviously
this requires a ttag.  Redefining core Common Lisp functions like @('intern')
is slightly insane, and we might run into trouble if CCL is changed.  But this
is a really valuable debugging message to have, so it seems worthwhile.</p>

<p>Note that the debugger slows down interning by some small amount (on the
order of 1.5 to 5%).</p>

<p>If you find out that slow interning is the cause of your problems, consider
tweaking the @('ACL2_SIZE') parameter you use when you build ACL2 (which can
help for symbols interned in the ACL2 package only).</p>")


(defsection inspect-package
  :parents (intern-debugging)
  :short "Print some basic information about a package. (CCL only)"
  :long "<p>@(call ccl-inspect-package) is given the name of a package, e.g.,
@('\"ACL2\"') or @('\"VL\"').  It prints out some low-level information about
the current number of symbols that are in the package and how many will fit
before it needs to be resized.  This is occasionally useful for figuring out
whether your packages are large enough, but usually the passive @(see
intern-debugging) monitoring is more useful.</p>"

  (defun inspect-package (name)
    (declare (xargs :guard (stringp name))
             (ignorable name))
    (cw "inspect-package not yet redefined.~%")))

(defttag intern-debugging)

(include-raw "intern-debugging-raw.lsp")



#|
; These tests were with ACL2_SIZE = 3,000,000.

(include-book
 "intern-debugging")

(include-book
 "str/top" :dir :system)



; Performance test.  The extra expensive of debugging should be most severe
; when we're interning an already-interned symbol (and hence don't need to
; actually insert anything into the hash table).

(time (loop for i from 1 to 10000000 do   ;; test 1: repeated symbols
            (intern "FOO" "ACL2")))

(defconst *strs*
  (loop for i from 1 to 1000000 collect (str::cat "foo_" (str::natstr i))))

(time (loop for str in *strs* do (intern str "ACL2"))) ;; test 2: fresh symbols


; TEST1: about 5% slowdown
;   - Without intern-debugging:  3.140 seconds
;   - With intern-debugging:     3.303 seconds
;
; TEST2: about 1.5% slowdown
;   - Without intern-debugging, .879 seconds
;   - With intern-debugging: .893 seconds


; Functionality test.  Okay, so does it work?  I set ACL2_SIZE to 3 million,
; but actually its size seems to be around 2.65 million.  Since the following
; loop requires the interning of 3 million new symbols, it will need at least a
; resize.

(defconst *strs*
  (loop for i from 1 to 3000000 collect (str::cat "foo_" (str::natstr i))))

(time (loop for str in *strs* do (intern str "ACL2")))


; Without intern-debugging, in a fresh session, this loop takes 64 seconds (246
; MB) and doesn't give you any idea that the reason this is taking so long is
; that the package is being resized.

; With intern-debugging, in a fresh session, the loop again takes 64 seconds
; and 246 MB, so the performance hasn't really changed, but it prints several
; useful messages that warn you the package is being resized.  You can see that
; there are two resizes which collectively cost 17 seconds of execution time.

; Note: we may be about to resize the ACL2 package.
; Before interning foo_2611853:
; - Current count: 2,625,000
; - Current limit: 2,625,001
(CCL::%INTERN STR
              PKG) took 10,066,616 microseconds (10.066616 seconds) to run 
                    with 8 available CPU cores.
During that period, 10,036,474 microseconds (10.036474 seconds) were spent in user mode
                    26,996 microseconds (0.026996 seconds) were spent in system mode
 26,249,968 bytes of memory allocated.
 12,878 minor page faults, 0 major page faults, 0 swaps.
; After interning foo_2611853:
; - Current count: 2,624,987
; - Current limit: 2,871,083


; Note: we may be about to resize the ACL2 package.
; Before interning foo_2857949:
; - Current count: 2,871,082
; - Current limit: 2,871,083
(CCL::%INTERN STR
              PKG) took 7,238,270 microseconds (7.238270 seconds) to run 
                    with 8 available CPU cores.
During that period, 7,223,902 microseconds (7.223902 seconds) were spent in user mode
                    13,998 microseconds (0.013998 seconds) were spent in system mode
 28,710,928 bytes of memory allocated.
 14,019 minor page faults, 0 major page faults, 0 swaps.
; After interning foo_2857949:
; - Current count: 2,871,083
; - Current limit: 3,140,250

|#