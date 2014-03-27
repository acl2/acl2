; Centaur Miscellaneous Books
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "ACL2")
; cert_param: (ccl-only)
(include-book "tools/include-raw" :dir :system)
(include-book "tools/bstar" :dir :system)
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
  (er hard? 'disconnect-shared-libs
      "Error: under the hood redefinition not installed?"))

(defun reconnect-shared-libs ()
  ;; We assume your LD_LIBRARY_PATH has all the .so files you copied.
  (declare (xargs :guard t))
  (er hard? 'reconnect-shared-libs
      "Error: under the hood redefinition not installed?"))

(defttag :sharedlibs)
(include-raw "sharedlibs-raw.lsp")

