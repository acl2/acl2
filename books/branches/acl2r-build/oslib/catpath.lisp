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
(include-book "std/util/define" :dir :system)
(local (include-book "misc/assert" :dir :system))

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

