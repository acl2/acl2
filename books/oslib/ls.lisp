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

(in-package "OSLIB")
(include-book "read-acl2-oracle")
(include-book "cutil/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
; (depends-on "ls-raw.lsp")

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
                           @('~') or ~('~jared').  The empty string means the
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
  :parents (oslib)
  :short "Get a subdirectory listing."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we query the file system to obtain a listing of the
<b>subdirectories</b> (not ordinary files) of the given @('path').</p>

<p>The subdirectory names returned are <b>not</b> complete paths.  For
instance, if @('/home/users/jared') contains directories named @('foo') and
@('bar'), then the resulting @('val') will have @('\"foo\"') and @('\"bar\"'),
not full paths like @('\"/home/users/jared/foo\"').</p>"

  :ignore-ok t
  (b* ((- (er hard? __function__ "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       ((when err)
        (mv t (if (stringp val) val "error") state)))
    (mv nil (remove-nonstrings val) state)))

(define ls-files ((path "Directory to list files in.  May or may not include
                         a trailing slash.  May use standard idioms like
                         @('~') or ~('~jared').  The empty string means the
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
  :parents (oslib)
  :short "Get a file listing."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we query the file system to obtain a listing of the <b>files</b> (not
subdirectories) of the given @('path').</p>

<p>The file names returned are <b>not</b> complete paths.  For instance, if
@('/home/users/jared') contains @('foo.txt'), then @('val') will contain
@('\"foo.txt\") instead of @('\"/home/users/jared/foo.txt\"').</p>"

  :ignore-ok t
  (b* ((- (er hard? __function__ "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       ((when err)
        (mv t (if (stringp val) val "error") state)))
    (mv nil (remove-nonstrings val) state)))

(defttag oslib)
(include-raw "ls-raw.lsp")

