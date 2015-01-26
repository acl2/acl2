; Centaur Miscellaneous Books
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/strings/strrpos" :dir :system)

; This is a horrible hack for disconnecting and reconnecting shared libraries
; from CCL.
;
; Goal: prevent your "released" application from depending on temporary files
; in your working area, which you might clobber after the release.
;
; Mechanism:
;
;  1. Disconnect-shared-libs tells CCL to unload any shared libraries that it
;     has loaded from absolute paths.  It simultaneously copies these shared
;     libraries into your current location.
;
;  2. Use save-exec to build your application.
;
;  3. Move the resulting image and all of the copies of the .so files into
;     the "final" release area where your application will permanently live
;
;  4. Edit your application's startup files so that they start with:
;        export LD_LIBRARY_PATH=/path/to/your/app/release:$LD_LIBRARY_PATH
;
;  5. At startup time, your application should (as its first task) call
;     reconnect-shared-libs, to reload the shared libraries.  If all is well,
;     it will load the libraries from its own release area, instead of from
;     wherever you were loading them from when you were developing the program.
;
; If anyone knows how to do this better, we would very much like to print this
; code out, mush it up, and throw it in a fire.  So please let us know.
;
; For a working example of this mechanism, see:
;
;    centaur/misc/sharedlibstest
;
; and specifically see test.sh.  (Note that running test.sh will delete your
; Quicklisp files and you'll potentially need to rebuild!)

(defun filename-part (abs-path)
  (declare (xargs :guard (and (stringp abs-path)
                              (not (equal abs-path "")))))
  (b* ((last-slash (str::strrpos "/" abs-path))
       ((unless last-slash)
        ;; I guess it's relative or something?
        abs-path))
    (subseq abs-path (+ 1 last-slash) nil)))

(defun disconnect-shared-libs ()
  ;; We assume you call this right before save-exec.
  ;; We assume you're in the directory you want all the .so files copied to.
  (declare (xargs :guard t))
  #+Clozure
  (er hard? 'disconnect-shared-libs
      "Error: under the hood redefinition not installed?")
  #-Clozure
  (cw "; disconnect-shared-libs not implemented on this lisp.~%"))

(defun reconnect-shared-libs ()
  ;; We assume your LD_LIBRARY_PATH has all the .so files you copied.
  (declare (xargs :guard t))
  #+Clozure
  (er hard? 'reconnect-shared-libs
      "Error: under the hood redefinition not installed?")
  #-Clozure
  (cw "; reconnect-shared-libs not implemented on this lisp.~%"))

(defttag :sharedlibs)

#+Clozure
(include-raw "sharedlibs-raw.lsp")

