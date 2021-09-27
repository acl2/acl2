; watch.lisp
; Copyright (C) 2013, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This file was originally part of the HONS version of ACL2.  The original
; version of ACL2(h) was contributed by Bob Boyer and Warren A. Hunt, Jr.  The
; design of this system of Hash CONS, function memoization, and fast
; association lists (applicative hash tables) was initially implemented by
; Boyer and Hunt.

(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)

; [Jared]: I pulled the WATCH related functionality out of ACL2(h) and into
; this ttag-based book.  In the process I ripped out the previous if-profiling
; stuff, which made it much easier to disentangle watch from memoize.

; Matt K., 12/26/14: Thanks to very recent mods from Bob Boyer, this code seems
; to work.

(defttag :watch)

; Originally we had this:

; (include-raw "output-raw.lsp")

; But profile.lisp has that form, too, and we have see compilation fail (using
; ANSI GCL) when parallel `make' was causing the file to be compiled twice in
; parallel.  So we avoid this double-compilation by including profile.lisp
; instead.

(include-book "profile")

(include-raw "watch-raw.lsp")

(include-book "xdoc/top" :dir :system)

(defxdoc watch
  :parents (debugging)
  :short "Initiate the printing of profiling information to view in Emacs"
  :long "<p>The following example from Bob Boyer shows how to use this
 feature.</p>

 @({
 acl2
 (include-book \"centaur/memoize/old/watch\" :dir :system :ttags :all)
 :q
 (watch)
 })

 <p>The output at the terminal will show a file name such as
 @('\"watch-output-temp-8916.lsp\"').  Bring that file into an Emacs buffer and
 evaluate m-x auto-revert-mode.  Then, back in ACL2:</p>

 @({
 (lp)
 (defun foo (x) (declare (xargs :guard t)) x)
 (memoize 'foo)
 (foo 1)
 (foo 1)
 (foo 2)
 })

 <p>You can look at the above ``temporary'' file and see some interesting
 information related to features provided by your @(see hons-enabled) ACL2
 executable.  For a further experiment, continue in ACL2 as follows.</p>

 @({
 :q
 (profile-acl2) ; could take a minute or more
 (lp)
 :mini-proveall
 })

 <p>The buffer for the above file will now provide reports on the 20 functions
 that used the most time during the @(':mini-proveall') evaluation, among the
 newly-profiled ACL2 functions.  In raw Lisp, you can evaluate @('(setq
 *memoize-summary-limit* 100)') to see the most time-using 100 functions (for
 example).</p>

 <p>The documentation below was directly derived from a Lisp documentation
 string formerly in @('books/centaur/memoize/old/watch-raw.lsp').  The ACL2
 community is invited to format it, modify it, etc.  More documentation may be
 found in the above @('watch-raw.lsp') file.</p>

 @({
 WATCH is a raw Lisp function that initiates the printing of
 profiling information.  (WATCH) sets *WATCH-FILE* to the string that
 results from the evaluation of *WATCH-FILE-FORM*, a string that is
 to be the name of a file we call the 'watch file'.

 In Clozure Common Lisp, (WATCH) also initiates the periodic
 evaluation of (WATCH-DUMP), which evaluates the members of the list
 *WATCH-FORMS*, but diverts characters for *STANDARD-OUTPUT* to the
 watch file.  The value of *WATCH-FILE* is returned by both (WATCH)
 and (WATCH-DUMP).  (WATCH-KILL) ends the periodic printing to the
 watch file.

 You are most welcome to, even encouraged to, change the members of
 *WATCH-FORMS* to have your desired output written to the watch file.

 Often (MEMOIZE-SUMMARY) is a member of *WATCH-FORMS*.  It prints
 information about calls of memoized and/or profiled functions.

 Often (PRINT-CALL-STACK) is a member of *WATCH-FORMS*.  It shows the
 names of memoized and/or profiled functions that are currently in
 execution and how long they have been executing.

 We suggest the following approach for getting profiling information
 about calls to Common Lisp functions:

   0. Invoke (WATCH).

   1. Profile some functions that have been defined.

      For example, call (PROFILE-FN 'foo1), ...

      Or, for example, call PROFILE-FILE on the name of a file that
      contains the definitions of some functions that have been
      defined.

      Or, as a perhaps extreme example, invoke
      (PROFILE-ACL2), which will profile many of the functions that
      have been introduced to ACL2, but may take a minute or two.

      Or, as a very extreme example, invoke
      (PROFILE-ALL), which will profile many functions, but may take
      a minute or two.

   2. Run a Lisp computation of interest to you that causes some of
      the functions you have profiled to be executed.

   3. Invoke (WATCH-DUMP).

   4. Examine, perhaps in Emacs, the watch file, whose name was
      returned by (WATCH-DUMP).  The watch file contains information
      about the behavior of the functions you had profiled or
      memoized during the computation of interest.

 From within ACL2, you may MEMOIZE any of your ACL2 Common Lisp
 compliant ACL2 functions.  One might MEMOIZE a function that is
 called repeatedly on the exact same arguments.  Deciding which
 functions to memoize is tricky.  The information from (WATCH-DUMP)
 helps.  Sometimes, we are even led to radically recode some of our
 functions so that they will behave better when memoized.

 In Emacs, the command 'M-X AUTO-REVERT-MODE' toggles auto-revert
 mode, i.e., causes a buffer to exit auto-revert mode if it is in
 auto-revert mode, or to enter auto-revert mode if it is not.  In
 other words, to stop a buffer from being auto-reverted, simply
 toggle auto-revert mode; toggle it again later if you want more
 updating.  'M-X AUTO-REVERT-MODE' may be thought of as a way of
 telling Emacs, 'keep the watch buffer still'.

 In Clozure Common Lisp, if the FORCE-DOG argument to WATCH (default
 NIL) is non-NIL or if (LIVE-TERMINAL-P) is non-NIL a 'watch dog'
 thread is created to periodically call (WATCH-DUMP).  The thread is
 the value of *WATCH-DOG-PROCESS*.

 See documentation strings in file
 books/centaur/memoize/old/watch-raw.lsp for further details.
 })")
