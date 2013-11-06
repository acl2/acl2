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
