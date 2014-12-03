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
(include-book "file-types-logic")
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

(define ls
  :short "Get a (full) directory listing."
  ((path stringp "Directory to list files in.")
   &key (state 'state))
  :returns (mv (error "NIL on success or an error @(see msg) on failure.")
               (val   "On success: a list of names of files (and directories)
                       within this directory."
                      string-listp)
               (state state-p1
                      :hyp (force (state-p1 state))))

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we query the file system to obtain a listing of the files within the
given @('path').  This listing can contain the names of any kind of file, e.g.,
it may contain ordinary files, directories, and special files such as block
devices and symbolic links.</p>

<p>The names returned are <b>not</b> complete paths.  For instance, if
@('/home/users/jared') contains directories named @('foo') and @('bar'), then
the resulting @('val') will have @('\"foo\"') and @('\"bar\"'), not full paths
like @('\"/home/users/jared/foo\"').</p>"

  :ignore-ok t
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv ?err1 val1 state) (read-acl2-oracle state))
       ((mv ?err2 val2 state) (read-acl2-oracle state))
       ((when val1)
        (mv val1 nil state)))
    (mv nil (remove-nonstrings val2) state)))


(define ls!
  :short "Get a (full) directory listing or cause a hard error."
  ((path stringp) &key (state 'state))
  :returns (mv (val string-listp)
               (state state-p1 :hyp (force (state-p1 state))))
  :long "<p>This is just a wrapper for @(see ls) that causes a hard error if
there are any problems.</p>"
  (b* (((mv err val state) (ls path))
       ((when err)
        (er hard? 'ls! "~@0" err)
        (mv nil state)))
    (mv val state)))


(define ls-files-aux
  :parents (ls-files)
  :short "Collect regular files for @(see ls-files)."
  ((path  stringp      "Path where the files came from.")
   (names string-listp "Names found within this path.")
   (state))
  :returns (mv error
               (regular string-listp)
               (state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom names))
        (mv nil nil state))
       (name1 (acl2::str-fix (car names)))
       (path1 (catpath path name1))
       ((mv err1 regular-p state) (regular-file-p path1))
       ((when err1) (mv err1 nil state))
       ((unless regular-p)
        (ls-files-aux path (cdr names) state))
       ((mv err2 rest state) (ls-files-aux path (cdr names) state))
       ((when err2) (mv err2 nil state)))
    (mv nil (cons name1 rest) state)))

(define ls-files
  :short "Get a listing of only the regular files within a directory."

  ((path stringp "Directory whose files you want to list.")
   &key (state 'state))
  :returns (mv (error "NIL on success or an error @(see msg) on failure.")
               (regular "On success: a list of names of files in @('path')."
                        string-listp)
               (state state-p1 :hyp (force (state-p1 state))))

  :long "<p>The notion of regular file is governed by @(see regular-file-p).
It includes, for instance, symbolic links to regular files.</p>"

  (b* (((mv err all-files state) (ls path))
       ((when err) (mv err nil state)))
    (ls-files-aux path all-files state)))

(define ls-files!
  :short "Get a listing of only the regular files within a directory, or cause
a hard error."
  ((path stringp) &key (state 'state))
  :returns (mv (val string-listp)
               (state state-p1 :hyp (force (state-p1 state))))
  :long "<p>This is just a wrapper for @(see ls-files) that causes a hard error
if there are any problems.</p>"
  (b* (((mv err val state) (ls-files path))
       ((when err)
        (er hard? 'ls-files! "~@0" err)
        (mv nil state)))
    (mv val state)))

(define ls-subdirs-aux
  :parents (ls-files)
  :short "Collect directories for @(see ls-subdirs)."
  ((path  stringp      "Path where the files came from.")
   (names string-listp "Names found within this path.")
   (state))
  :returns (mv error
               (subdirs string-listp)
               (state state-p1 :hyp (force (state-p1 state))))
  (b* (((when (atom names))
        (mv nil nil state))
       (name1 (acl2::str-fix (car names)))
       (path1 (catpath path name1))
       ((mv err1 directory-p state) (directory-p path1))
       ((when err1) (mv err1 nil state))
       ((unless directory-p)
        (ls-subdirs-aux path (cdr names) state))
       ((mv err2 rest state) (ls-subdirs-aux path (cdr names) state))
       ((when err2) (mv err2 nil state)))
    (mv nil (cons name1 rest) state)))

(define ls-subdirs
  :short "Get a listing of the subdirectories of a directory."
  ((path stringp "Directory whose subdirectories you want to list.")
   &key (state 'state))
  :returns (mv (error "NIL on success or an error @(see msg) on failure.")
               (subdirs "On success: a list of the subdirectories of @('path')."
                        string-listp)
               (state state-p1 :hyp (force (state-p1 state))))

  :long "<p>The notion of regular file is governed by @(see directory-p).  It
includes, for instance, symbolic links to directories.</p>"

  (b* (((mv err all-files state) (ls path))
       ((when err) (mv err nil state)))
    (ls-subdirs-aux path all-files state)))

(define ls-subdirs!
  :short "Get a listing of the subdirectories of a directory, or cause a hard
error."
  ((path stringp) &key (state 'state))
  :returns (mv (val string-listp)
               (state state-p1 :hyp (force (state-p1 state))))
  :long "<p>This is just a wrapper for @(see ls-subdirs) that causes a hard error
if there are any problems.</p>"
  (b* (((mv err val state) (ls-subdirs path))
       ((when err)
        (er hard? 'ls-subdirs! "~@0" err)
        (mv nil state)))
    (mv val state)))
