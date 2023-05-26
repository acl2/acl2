; cert.pl build system
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "ACL2")

(program)
(set-state-ok t)


(defun include-events-fn (fname dir encapsulate state)
  (declare (xargs :mode :program :stobjs state))
  (let ((ctx `(include-events ,fname)))
    (er-let* ((dir-value (if dir
                             (include-book-dir-with-chk soft ctx dir)
                           (value (cbd)))))
      (let* ((full-fname (extend-pathname dir-value fname state))
             (file-dir (get-directory-of-file full-fname)))
        (er-let* ((contents (read-object-file full-fname ctx state)))
          ;; first form is always in-package due to the way read-object-file works
          (let* ((event-contents (cdr contents))
                 (package (cadr (car contents))))
            (value `(with-cbd ,file-dir
                      (with-current-package ,package
                        (,@(if encapsulate
                               '(encapsulate nil)
                             '(progn))
                         . ,event-contents))))))))))

(defmacro include-src-events (fname &key dir encapsulate)
  `(make-event (include-events-fn ,fname ,dir ,encapsulate state)))

(defmacro include-events (fname &key dir encapsulate)
  `(make-event (include-events-fn ,(concatenate 'string fname ".lisp") ,dir ,encapsulate state)))
