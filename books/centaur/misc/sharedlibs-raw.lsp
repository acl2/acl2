; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")

(defparameter *shared-libs-list* nil)

(defun disconnect-shared-libs ()
  (cw "Disconnecting shared libraries.~%")
  (when *shared-libs-list*
    (error "Already have disconnected shared libs?"))
  (let ((state acl2::*the-live-state*)
        (info (loop for lib in ccl::*shared-libraries* collect
                    (cons (ccl::shlib.soname lib)
                          (ccl::shlib.opencount lib)))))
    (loop for (soname . count) in info do
          (b* (((unless (and (stringp soname)
                             (not (equal soname ""))
                             (eql (char soname 0) #\/)))
                (cw "Skipping ~f0.~%" soname))
               ((unless (equal count 1))
                ;; Probably just paranoia
                (er hard? 'magically-grab-abs-shared-libs
                    "Don't know what to do with ~f0 since its count is ~x1.~%"
                    soname count))
               (filename (filename-part soname))
               (- (cw "Copying ~f0 to ~f1.~%" soname filename))
               ((mv erp ?val ?state)
                (sys-call+ "cp" (list soname filename) state))
               ((when erp)
                (er hard? 'magically-grab-abs-shared-libs
                    "Failed to copy ~f0 to ~f1.~%" soname filename)))
            (cw "Closing old shared library.~%")
            (ccl::close-shared-library soname)
            (push filename *shared-libs-list*))))
  (cw "Disconnected shared libraries: ~x0." *shared-libs-list*))

(defun reconnect-shared-libs ()
  (cw "Reconnecting shared libraries.~%")
  (loop for lib in *shared-libs-list* do
        (cw "Opening ~s0.~%" lib)
        (ccl::open-shared-library lib))
  (cw "Done reconnecting shared libraries.~%"))
