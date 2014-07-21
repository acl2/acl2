; OSLIB -- Operating System Utilities
; Copyright (C) 2013 Centaur Technology
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

(defun ls-subdirs-fn (path state)

  #-(and Clozure Unix)
  (mv t "ls-subdirs: not yet implemented on this lisp." state)

  #+(and Clozure Unix)
  (let* ((step 0)
         (results (handler-case
                   (let* ((truename (truename (parse-namestring path)))
                          (pattern  (progn (incf step)
                                           (concatenate 'string (namestring truename) "*.*")))
                          (files    (progn (incf step)
                                           (directory pattern
                                                      :directories t
                                                      :files nil
                                                      :all t
                                                      :follow-links nil)))
                          (names    (progn (incf step)
                                           (loop for f in files
                                                 collect
                                                 (car (last (pathname-directory f)))))))
                     (incf step)
                     names)
                   (error (condition)
                          (format nil "ls-subdirs on ~a, step ~a: ~a" path
                                  step condition)))))
    (cond ((stringp results)
           (mv t results state))
          ((string-listp results)
           (mv nil results state))
          (t
           (mv nil (format nil "Expected string list, found ~a.~%" results)
               state)))))


(defun ls-files-fn (path state)

  #-(and Clozure Unix)
  (mv t "ls-files: not yet implemented on this lisp." state)

  #+(and Clozure Unix)
  (let* ((step 0) cond done results)
    ;; BOZO wtf?  primitive NFS lag prevention?
    (loop for i from 1 to 5 while (not done) do
          (handler-case
           (let* ((truename (truename (parse-namestring path)))
                  (pattern  (progn (incf step)
                                   (concatenate 'string (namestring truename)
                                                "*.*")))
                  (files    (progn (incf step)
                                   (directory pattern
                                              :directories nil
                                              :files t
                                              :all t
                                              :follow-links nil)))
                  (names    (progn (incf step)
                                   (loop for f in files
                                         collect
                                         (ccl::native-translated-namestring
                                          (file-namestring f))))))
             (incf step)
             (setq done t)
             (setq results names))
           (error (condition)
                  (cw "ls-files on ~x0: failed try ~x1, step ~x2, condition ~s3~%"
                      path i step (format nil "~a" condition))
                  (sleep 1)
                  (setq step 0)
                  (setq cond condition))))
    (unless done
      (setq results cond))
    (cond ((stringp results)
           (mv t results state))
          ((string-listp results)
           (mv nil results state))
          (t
           (mv nil (format nil "Expected string list, found ~a.~%" results)
               state)))))
