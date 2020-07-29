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
(include-book "std/util/define" :dir :system)
(include-book "std/strings/cat" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))

(define catpath ((basedir stringp
                          "Directory whose name should be extended, which may
                           or may not end with a slash.  Idioms like @('~'),
                           @('~jared'), and @('..') will be preserved.  The
                           empty string means the current directory.")
                 (filename stringp
                           "File or subdirectory name to append to @('basedir')"))
  :returns (path "A new string like @('basedir/filename').  We only insert a
                  slash if @('basedir') does not end with a slash.  We don't
                  normalize the path by collapsing @('..')."
                 stringp)
  :parents (oslib)
  :short "Basic concatenation operation for paths."

  :long "<p>ACL2 includes a built-in function named @('extend-pathname') that
is similar to @('catpath').  In some ways ACL2's version is nicer than
@('catpath').  It sometimes cleans up the path and gets rid of @('..')
characters.  But it also sometimes expands away symlinks, which you may not
want to do.  At the time of this writing, @('extend-pathname') is not easy to
effectively bring into logic mode, but that may change in the future.</p>

<p>Our @('catpath') function is comparatively primitive.  It doesn't try to
simplify the path in any way.</p>

<p>We assume Unix style paths, i.e., @('/') is the path separator.  It's not
clear what we should do to support other systems like Windows.</p>"

  (b* ((len (length basedir))
       ((when (or (int= len 0)
                  (eql (char basedir (- len 1)) #\/)))
        (cat basedir filename)))
    (cat basedir "/" filename)))

(local
 (progn
   ;; Basic examples
   (assert! (equal (catpath "" "foo.txt") "foo.txt"))
   (assert! (equal (catpath "/" "foo.txt") "/foo.txt"))
   (assert! (equal (catpath "~/" "foo.txt") "~/foo.txt"))
   (assert! (equal (catpath "~/../" "foo.txt") "~/../foo.txt"))
   (assert! (equal (catpath "~/../" "../") "~/../../"))
   (assert! (equal (catpath "/home/jared" "foo.txt")
                   "/home/jared/foo.txt"))
   (assert! (equal (catpath "/home/jared/" "foo.txt")
                   "/home/jared/foo.txt"))
   ))


(define catpaths
  :parents (oslib)
  :short "Extend a base directory with many file names."
  ((basedir   stringp      "Directory whose name should be extended, which may
                            or may not end with a slash.")
   (filenames string-listp "Names of files to append to @('basedir')."))
  :returns (paths string-listp "Extended paths.")
  (if (atom filenames)
      nil
    (cons (catpath basedir (car filenames))
          (catpaths basedir (cdr filenames)))))
