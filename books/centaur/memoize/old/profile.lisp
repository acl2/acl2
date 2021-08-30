; profile.lisp
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

; [Jared]: I pulled PROFILE-ACL2, PROFILE-ALL, and PROFILE-FILE, and related
; functionality out of ACL2(h) and into this ttag-based book.  They are not
; core memoize functionality.

; WARNING: We rarely use these features.  It is somewhat likely that this code
; may stop working.

; (depends-on "output-raw.lsp")
; (depends-on "profile-raw.lsp")

(include-book "xdoc/top" :dir :system)

(defn profile-acl2-fn (start lots-of-info forget)
  (declare (ignore start lots-of-info forget))
  (prog2$
   (er hard? 'profile-acl2
       "Under-the-hood definition not yet installed")
   nil))

(defmacro profile-acl2 (&key (start '0)
                             (lots-of-info 't)
                             forget)
  `(profile-acl2-fn ,start ,lots-of-info ,forget))

(defn profile-all-fn (lots-of-info forget pkg)
  (declare (ignore lots-of-info forget pkg))
  (prog2$
   (er hard? 'profile-all
       "Under-the-hood definition not yet installed")
   nil))

(defmacro profile-all (&key (lots-of-info 't) forget pkg)
  `(profile-all-fn ,lots-of-info ,forget ,pkg))

(defxdoc profile-acl2
  :parents (debugging profile memoize time$)
  :short "@(tsee profile) essentially all ACL2 functions"
  :long "<p>Evaluating @('(profile-acl2)') profiles each function symbol
 admitted to ACL2 unless it is</p>

 <ul>

 <li>@(tsee memoize)d,</li>

 <li>@(tsee trace)d,</li>

 <li>in the package @('\"COMMON-LISP\"'), or</li>

 <li>otherwise illegal to memoize or profile (as per raw Lisp variables
 @('*never-memoize-ht*') and @('*profile-reject-ht*')).</li>

 </ul>

 <p>When @('profile-acl2') is invoked, it calls @(tsee clear-memoize-statistics)
 to remove all profiling info displayed by @(tsee memoize-summary).</p>

 <p>Also see @(see profile-all), which is similar but is not restricted to
 functions defined in the ACL2 loop.</p>

 <p>General form:</p>

 @({
 (profile-acl2 :start start                ; default 0
               :lots-of-info lots-of-info  ; default t
               :forget forget              ; default nil
               )
 })

 <p>where all keywords are evaluated and optional, and:</p>

 <ul>

 <li>@('start') (default: @('0')) is either an event name or a natural number,
 to restrict to functions admitted after the given event or after the given
 number of @(see events), respectively;</li>

 <li>@('lots-of-info') (default: @('t')) determines whether the usual profiling
 information is recorded (when @('lots-of-info') is true) or not (when
 @('lots-of-info') is false); and</li>

 <li>@('forget') (default: @('nil')) is passed as the @(':forget') argument for
 each generated call of @(tsee profile).</li>

 </ul>

 <p>Note that @('profile-acl2') has an under-the-hood definition in raw Lisp,
 and thus a trust tag (see @(see defttag)) is temporarily introduced while
 loading its definition.</p>")

(defxdoc profile-all
  :parents (debugging profile memoize time$)
  :short "@(tsee profile) essentially all functions"
  :long "<p>Evaluating @('(profile-all)') profiles each function symbol
 in a package known to ACL2 unless it is</p>

 <ul>

 <li>@(tsee memoize)d,</li>

 <li>@(tsee trace)d,</li>

 <li>in the package @('\"COMMON-LISP\"'), or</li>

 <li>otherwise illegal to memoize or profile (as per raw Lisp variables
 @('*never-memoize-ht*') and @('*profile-reject-ht*')).</li>

 </ul>

 <p>When @('profile-all') is invoked, it calls @(tsee clear-memoize-statistics)
 to remove all profiling info displayed by @(tsee memoize-summary).</p>

 <p>Also see @(see profile-acl2), which is similar but is restricted to
 functions defined in the ACL2 loop.</p>

 <p>General form:</p>

 @({
 (profile-all :lots-of-info lots-of-info  ; default t
              :forget forget              ; default nil
              :pkg    pkg                 ; default nil
              )
 })

 <p>where all keywords are evaluated and optional, and:</p>

 <ul>

 <li>@('lots-of-info') (default: @('t')) determines whether the usual profiling
 information is recorded (when @('lots-of-info') is true) or not (when
 @('lots-of-info') is false).</li>

 <li>@('forget') (default: @('nil')) is passed as the @(':forget') argument for
 each generated call of @(tsee profile); and</li>

 <li>@('pkg'), when supplied, is a package name or list of package names to use
 in place of the default, which is the list of names of all packages known to
 ACL2 except for packages @('\"ACL2-INPUT-CHANNEL\"'),
 @('\"ACL2-OUTPUT-CHANNEL\"'), @('\"COMMON-LISP\"'), and @('\"KEYWORD\"').</li>

 </ul>

 <p>Note that @('profile-all') has an under-the-hood definition in raw Lisp,
 and thus a trust tag (see @(see defttag)) is temporarily introduced while
 loading its definition.</p>")

; Note: It might be good here to handle profile-file, as we do above for
; profile-acl2 and profile-all, since  also is defined in
; profile-raw.lsp.  However, it's not clear that profile-file has been used
; much and, hence, it's not clear that it works well.  So we leave that task
; for another day.  Actually, it might make more sense simply to add a :file
; keyword argument to each of profile-acl2 and profile-all.

(defttag :profile)
(include-raw "output-raw.lsp")
(include-raw "profile-raw.lsp")
