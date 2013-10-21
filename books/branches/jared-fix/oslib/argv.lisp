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
; Original author: Jared Davis <jared@centtech.com>

(in-package "OSLIB")
(include-book "oslib/read-acl2-oracle" :dir :system)
(include-book "cutil/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(local (include-book "std/typed-lists/string-listp" :dir :system))
; (depends-on "argv-raw.lsp")

(define argv (&optional (state 'state))
  :returns (mv (arguments string-listp)
               (state state-p1 :hyp (force (state-p1 state))))
  :parents (oslib)
  :short "Get the \"application level\" command line arguments passed to ACL2."

  :long "<p>Typically, @('(argv)') is useful for writing command-line programs
atop ACL2, e.g., using @(see save-exec).</p>

<p>In the logic, this function reads from the ACL2 oracle and coerces
whatever it finds into a @(see string-listp).  In the execution, we use
whatever mechanism the host Lisp provides for reading the command line
arguments that were given to ACL2.</p>

<p>Dead simple, right?  Well, not really.</p>

<p>Usually ACL2 itself, or any custom program you build atop ACL2 using @(see
save-exec), is really just an <i>image</i> that is executed by the
<i>runtime</i> for the host Lisp.  For instance, when you build ACL2 on CCL,
you get:</p>

<ul>

<li>An ACL2 image named @('saved_acl2.lx86cl64') or similar</li>

<li>A script named @('saved_acl2') that is something like this:

@({
#!/bin/sh
export CCL_DEFAULT_DIRECTORY=/path/to/ccl
exec /path/to/ccl/lx86cl64 \
  -I /path/to/saved_acl2.lx86cl64 \
  -K ISO-8859-1 \
  -e \"(acl2::acl2-default-restart)\"
  -- \"$@\"
})</li>

</ul>

<p>So this script is invoking the Lisp runtime, named @('lx86cl64'), and
telling it to execute the ACL2 image, @('saved_acl2.lx86cl64').</p>

<p>The important thing to note here is that command-line options like @('-I'),
@('-K'), and @('-e'), are arguments <b>to the runtime</b>, not to ACL2.  These
runtime options vary wildly from Lisp to Lisp.  So for @('argv') to be portable
and make any sense at all, we really want to exclude these Lisp-runtime
options, and only give you the \"real\", application-level options for this
invocation of your program.</p>

<p>Fortunately, most Lisps have a special mechanism to separate their runtime
options from the application options.  In Allegro, CCL, CLISP, and CMUCL, this
is done with a special @('--') option.  SBCL uses a slightly more elaborate
syntax but it's the same basic idea.</p>

<p>So on these Lisps, as long as you are running ACL2 or your save-image using
a \"proper\" shell script, @('(argv)') will work perfectly and give you exactly
the arguments to your program, no matter what options you are using, and no
matter whether the host Lisp runtime takes options with the same names.  For
details about what a \"proper\" script means, see the comments for your
particular Lisp in @('oslib/argv-raw.lsp').</p>

<p>Unfortunately, GCL and LispWorks do not have such an option, so on these
Lisps we do something very half-assed:</p>

<ul>
<li>We still expect that a \"proper\" shell script will put in a @('--') option
to separate the runtime options from the program options.</li>
<li>@('(argv)') just excludes will everything before the @('--').</li>
</ul>

<p>So even though the Lisp doesn't know about @('--') in this case, we can at
least keep the Lisp specific options out of your program.</p>

<p>But this isn't perfect.  Since the Lisp doesn't know to stop processing
options when it sees @('--'), there is a possibility of conflict if your
program happens to use the same options as the Lisp.  I don't know how to do
any better, so that's just how it is.</p>"

  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state)))
    (if (and (not err)
             (string-listp val))
        (mv val state)
      (mv nil state)))

  ///
  (defthm true-listp-of-argv
    (true-listp (mv-nth 0 (argv)))
    :rule-classes :type-prescription))

(defttag oslib)
(include-raw "argv-raw.lsp")

