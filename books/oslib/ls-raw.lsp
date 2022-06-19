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

(defun ls-fn (path state)
  (b* (((unless (live-state-p state))
        (error "LS can only be called on a live state.")
        (mv "ERROR" nil state))
       ((unless (stringp path))
        (error "LS called on a non-stringp dir?")
        (mv "ERROR" nil state)))

    (handler-case
      (let* ((dir       (uiop:ensure-directory-pathname (uiop:parse-native-namestring path)))
             (pathnames (osicat:list-directory dir))
             (names     nil))
        (loop for pathname in pathnames do
              ;; Uiop:native-namestring produces an error on filenames that
              ;; have wildcard characters in them.  This used to mean that we'd
              ;; fail to list directories that had any such files in them. Now
              ;; we handle this by trying instead to push the namestring.  If
              ;; somehow this fails too, then we just ignore that particular
              ;; pathname and don't include it in the directory listing.
              (handler-case
                  (push (uiop:native-namestring pathname) names)
                (error (condition)
                       (declare (ignore condition))
                       (handler-case
                           (push (namestring pathname) names)
                         (error (condition)
                                (declare (ignore condition))
                                nil)))))
        (basenames names))
      (error (condition)
             (let ((condition-str (format nil "~a" condition)))
               (mv (msg "~s0: error listing ~s1: ~s2."
                        'ls path condition-str)
                   nil state))))))




;; (defun ls-files-core (dir)
;;   (let* ((dir (uiop:ensure-directory-pathname
;;                (uiop:parse-native-namestring dir)))
;;          (pathnames (osicat:list-directory dir))
;;          (files      nil))
;;     (loop for pathname in pathnames do
;;           (unless (osicat:directory-pathname-p pathname)
;;             (push (namestring pathname) files)))
;;     files))

;; (ls-subdirs-core "./")
;; (ls-files-core "./")

;; #||
;; (defun ls-subdirs-fn (path state)
  
          




;; (defun ls-subdirs-fn (path state)
  

;;   (let* ((step 0)
;;          (results (handler-case
;;                    (let* ((truename (truename (parse-namestring path)))
;;                           (pattern  (progn (incf step)
;;                                            (concatenate 'string (namestring truename) "*.*")))
;;                           (files    (progn (incf step)
;;                                            (directory pattern
;;                                                       :directories t
;;                                                       :files nil
;;                                                       :all t
;;                                                       :follow-links nil)))
;;                           (names    (progn (incf step)
;;                                            (loop for f in files
;;                                                  collect
;;                                                  (car (last (pathname-directory f)))))))
;;                      (incf step)
;;                      names)
;;                    (error (condition)
;;                           (format nil "ls-subdirs on ~a, step ~a: ~a" path
;;                                   step condition)))))
;;     (cond ((stringp results)
;;            (mv t results state))
;;           ((string-listp results)
;;            (mv nil results state))
;;           (t
;;            (mv nil (format nil "Expected string list, found ~a.~%" results)
;;                state)))))


;; (defun ls-files-fn (path state)

;;   #-(and Clozure Unix)
;;   (mv t "ls-files: not yet implemented on this lisp." state)

;;   #+(and Clozure Unix)
;;   (let* ((step 0) cond done results)
;;     ;; BOZO wtf?  primitive NFS lag prevention?
;;     (loop for i from 1 to 5 while (not done) do
;;           (handler-case
;;            (let* ((truename (truename (parse-namestring path)))
;;                   (pattern  (progn (incf step)
;;                                    (concatenate 'string (namestring truename)
;;                                                 "*.*")))
;;                   (files    (progn (incf step)
;;                                    (directory pattern
;;                                               :directories nil
;;                                               :files t
;;                                               :all t
;;                                               :follow-links nil)))
;;                   (names    (progn (incf step)
;;                                    (loop for f in files
;;                                          collect
;;                                          (ccl::native-translated-namestring
;;                                           (file-namestring f))))))
;;              (incf step)
;;              (setq done t)
;;              (setq results names))
;;            (error (condition)
;;                   (cw "ls-files on ~x0: failed try ~x1, step ~x2, condition ~s3~%"
;;                       path i step (format nil "~a" condition))
;;                   (sleep 1)
;;                   (setq step 0)
;;                   (setq cond condition))))
;;     (unless done
;;       (setq results cond))
;;     (cond ((stringp results)
;;            (mv t results state))
;;           ((string-listp results)
;;            (mv nil results state))
;;           (t
;;            (mv nil (format nil "Expected string list, found ~a.~%" results)
;;                state)))))

;; ||#
