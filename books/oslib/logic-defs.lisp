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
(include-book "std/util/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (xdoc::set-default-parents oslib))

(define argv (&optional (state 'state))
  :returns (mv (arguments string-listp)
               (state state-p1 :hyp (force (state-p1 state))))
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


(define date (&optional (state 'state))
  :returns (mv (datestamp stringp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get the current datestamp, like \"November 17, 2010 10:25:33\"."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we use Common Lisp's @('get-decoded-time') function to figure out
what the current date and time is.  We think this <i>should</i> work on any
Common Lisp system.</p>"

  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state)))
    (if (and (not err)
             (stringp val))
        (mv val state)
      (mv "Error reading date." state))))


(define getpid (&optional (state 'state))
  :returns (mv (pid "The Process ID for this ACL2 session on success, or
                     @('nil') on failure."
                    (or (natp pid)
                        (not pid))
                    :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get the current process identification (PID) number."

  :long "<p>This will just fail if called on an unsupported Lisp.</p>"

  (b* ((- (raise  "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       ((when err)
        (mv nil state)))
    (mv (nfix val) state)))


(define remove-nonstrings (x)
  :returns (filtered- string-listp)
  (cond ((atom x)
         nil)
        ((stringp (car x))
         (cons (car x) (remove-nonstrings (cdr x))))
        (t
         (remove-nonstrings (cdr x)))))

(define ls-subdirs ((path "Directory to list files in.  May or may not include
                           a trailing slash.  May use standard idioms like
                           @('~') or @('~jared').  The empty string means the
                           current directory."
                          stringp)
                    &optional
                    (state 'state))
  :returns (mv (error "Success indicator.  We can fail if @('path') does not
                       exist or isn't readable, etc."
                      booleanp :rule-classes :type-prescription)
               (val   "On success: a list of subdirectory names (excludes files).
                       On failure: an error message explaining the problem."
                      (and (equal (stringp val) error)
                           (equal (string-listp val) (not error))))
               (state state-p1
                      :hyp (force (state-p1 state))))
  :short "Get a subdirectory listing."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we query the file system to obtain a listing of the
<b>subdirectories</b> (not ordinary files) of the given @('path').</p>

<p>The subdirectory names returned are <b>not</b> complete paths.  For
instance, if @('/home/users/jared') contains directories named @('foo') and
@('bar'), then the resulting @('val') will have @('\"foo\"') and @('\"bar\"'),
not full paths like @('\"/home/users/jared/foo\"').</p>"

  :ignore-ok t
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       ((when err)
        (mv t (if (stringp val) val "error") state)))
    (mv nil (remove-nonstrings val) state)))

(define ls-files ((path "Directory to list files in.  May or may not include
                         a trailing slash.  May use standard idioms like
                         @('~') or @('~jared').  The empty string means the
                         current directory."
                        stringp)
                  &optional
                  (state 'state))
  :returns (mv (error "Success indicator.  We can fail if @('path') does not
                       exist or isn't readable, etc."
                      booleanp :rule-classes :type-prescription)
               (val "On success: a list of file names (excluding directories).
                     On failure: an error message explaining the problem."
                    (and (equal (stringp val) error)
                         (equal (string-listp val) (not error))))
               (state state-p1
                      :hyp (force (state-p1 state))))
  :short "Get a file listing."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we query the file system to obtain a listing of the <b>files</b> (not
subdirectories) of the given @('path').</p>

<p>The file names returned are <b>not</b> complete paths.  For instance, if
@('/home/users/jared') contains @('foo.txt'), then @('val') will contain
@('\"foo.txt\"') instead of @('\"/home/users/jared/foo.txt\"').</p>"

  :ignore-ok t
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       ((when err)
        (mv t (if (stringp val) val "error") state)))
    (mv nil (remove-nonstrings val) state)))




(define mkdir ((dir "The path that you want to create, e.g., @('./foo/bar')"
                    stringp)
               &optional
               (state 'state))
  :returns (mv (successp booleanp
                         :rule-classes :type-prescription
                         "Success indicator.  We might fail due to file system
                          permissions, illegal file names, etc.")
               (state state-p1
                      :hyp (force (state-p1 state))))
  :short "Make new directories if they don't already exist, like @('mkdir -p'),
and return a success indicator so you can recover from errors."

  :long "<p>In the logic this function reads from the ACL2 oracle to determine
if it succeeds.  In the execution, we attempt to create directories using the
Common Lisp function @('ensure-directories-exist'), and capture any
errors.</p>"

  :ignore-ok t
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       (okp (and (not err)
                 (booleanp val)
                 val)))
    (mv okp state)))


(define mkdir! ((dir "The path that you want to create, e.g., @('./foo/bar')"
                     stringp)
               &optional
               (state 'state))
  :returns (state state-p1 :hyp (force (state-p1 state)))
  :short "Make new directories if they don't already exist, like @('mkdir -p'),
or cause a hard error if there is any problem."

  :long "<p>This is just a wrapper for @(see mkdir) that causes an error on any
failure.</p>"

  (b* (((mv successp state) (mkdir dir state))
       ((unless successp)
        (raise "Failed to create ~s0." dir)
        state))
    state))



(define rmtree ((dir "The path that you want to remove, e.g., @('./foo/bar')"
                     stringp)
               &optional
               (state 'state))
  :returns (mv (successp booleanp
                         :rule-classes :type-prescription
                         "Success indicator.  We might fail due to file system
                          permissions, illegal file names, etc.")
               (state state-p1
                      :hyp (force (state-p1 state))))
  :short "Recursively delete files, like the shell command @('rm -rf'), and
return a success indicator so you can recover from errors."

  :long "<p>In the logic this function reads from the ACL2 oracle to determine
if it succeeds.  In the execution, we attempt to delete the requested path, and
detect errors.</p>"

  :ignore-ok t
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       (okp (and (not err)
                 (booleanp val)
                 val)))
    (mv okp state)))


(define lisp-type (&optional (state 'state))
  :returns (mv (description stringp :rule-classes :type-prescription
                            "E.g., @('\"Clozure Common Lisp\").")
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get a host-Lisp specific string describing what kind of Common Lisp
implementation this is."
  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution, we call the Common Lisp function @('lisp-implementation-type').
When this produces a string, we return it.</p>

<p>Note that the Common Lisp @('lisp-implementation-type') function is
technically allowed to return @('nil'); in this case we return the empty
string.</p>"

  (b* (((mv err val state) (read-acl2-oracle state))
       (description (if (and (not err)
                             (stringp val))
                        val
                      "")))
    (mv description state)))

(define lisp-type (&optional (state 'state))
  :returns (mv (description stringp :rule-classes :type-prescription
                            "E.g., @('\"Clozure Common Lisp\").")
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get a host-Lisp specific string describing what kind of Common Lisp
implementation this is."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution, we call the Common Lisp function @('lisp-implementation-type'), and
return whatever string it produces.</p>

<p>Note that the Common Lisp @('lisp-implementation-type') function is
technically allowed to return @('nil'); in this case we return the empty
string.</p>"

  (b* (((mv err val state) (read-acl2-oracle state))
       (description (if (and (not err)
                             (stringp val))
                        val
                      "")))
    (mv description state)))

(define lisp-version (&optional (state 'state))
  :returns (mv (description stringp :rule-classes :type-prescription
                            "E.g., @('\"Version 1.9-r15996  (LinuxX8664)\").")
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get a host-Lisp specific string describing the version number for
this Common Lisp implementation."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution, we call the Common Lisp function @('lisp-implementation-version'),
and return the string it produces.</p>

<p>Note that the Common Lisp @('lisp-implementation-type') function is
technically allowed to return @('nil'); in this case we return the empty
string.</p>"

  (b* (((mv err val state) (read-acl2-oracle state))
       (description (if (and (not err)
                             (stringp val))
                        val
                      "")))
    (mv description state)))
