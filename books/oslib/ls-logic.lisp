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

(in-package "OSLIB")
(include-book "catpath")
(include-book "read-acl2-oracle")
(include-book "std/util/define" :dir :system)
(local (xdoc::set-default-parents oslib))

(define remove-nonstrings (x)
  :returns (filtered-x string-listp)
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
