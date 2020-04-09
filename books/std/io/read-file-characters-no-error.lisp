; Standard IO Library
; read-file-characters-no-errors.lisp
; Copyright (C) 2013 David Rager
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
; Original author: David Rager <ragerdl@defthm.com>

(in-package "ACL2")
(include-book "read-file-characters")
(local (include-book "tools/mv-nth" :dir :system))

(defund read-file-characters-no-error (filename state)
  (declare (xargs :guard (and (stringp filename)
                              (state-p state))))
  (declare (xargs :stobjs (state)))
  (b* (((mv data state)
        (read-file-characters filename state))
       ((when (stringp data))
        (mv (er hard? 'read-file-characters-no-error data) state)))
    (mv data state)))

(local (in-theory (enable read-file-characters-no-error)))

(defthm state-p1-of-read-file-characters-no-error
  (implies (and (force (state-p1 state))
                (force (stringp filename)))
           (state-p1 (mv-nth 1 (read-file-characters-no-error filename state)))))

(defthm read-file-characters-no-error-returns-character-list
  (character-listp (mv-nth 0 (read-file-characters-no-error filename state))))
