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

(table include-events-table
       :include-command-names
       '(include-book
         include-events
         include-src-events))

(defmacro add-include-command-names (&rest names)
  `(table include-events-table
          :include-command-names
          (append ',names (cdr (assoc-eq :include-command-names
                                         (table-alist 'include-events-table world))))))

(defun include-events-rewrite-base-include (event dir state)
  ;; returns  new-event-or-nil
  ;; dir should be an absolute path
  (and (consp event)
       (member-eq (car event) (cdr (assoc :include-command-names (table-alist 'include-events-table (w state)))))
       (not (assoc-keyword :dir (cddr event)))
       (let* ((cmd (car event))
              (fname (cadr event))
              (args (cddr event))
              (full-fname (extend-pathname dir fname state))
              (sys-name (filename-to-book-name full-fname (w state)))
              ;; sys-name is either a sysfile, i.e. (dir . relative-path), or absolute path (because dir is absolute)
              (file-args (if (stringp sys-name)
                             (list sys-name)
                           `(,(cdr sys-name) :dir ,(car sys-name)))))
         `(,cmd ,@file-args . ,args))))
      

(mutual-recursion
 (defun include-events-rewrite-includes (event dir state)
   (or (include-events-rewrite-base-include event dir state)
       (and (consp event)
            (or (and (eq (car event) 'encapsulate)
                     (list* (car event)
                            (cadr event) ;; signatures
                            (include-events-rewrite-includes-list (cddr event) dir state)))
                (and (member-eq (car event) '(progn progn!))
                     (cons (car event)
                           (include-events-rewrite-includes-list (cdr event) dir state)))
                (and (member-eq (car event)
                                '(with-output
                                   with-prover-step-limit
                                   with-prover-time-limit))
                     (append (butlast 1 event)
                             (list (include-events-rewrite-includes (car (last event)) dir state))))
                (and (member-eq (car event) '(local skip-proofs))
                     (list (car event)
                           (include-events-rewrite-includes (cadr event) dir state)))))
       event))
 (defun include-events-rewrite-includes-list (events dir state)
   (if (atom events)
       nil
     (cons (include-events-rewrite-includes (car events) dir state)
           (include-events-rewrite-includes-list (cdr events) dir state)))))


(defun include-events-fn (fname dir encapsulate state)
  (declare (xargs :mode :program :stobjs state))
  (let ((ctx `(include-events ,fname)))
    (er-let* ((dir-value (if dir
                             (include-book-dir-with-chk soft ctx dir)
                           (value (cbd)))))
      (let* ((full-fname (extend-pathname dir-value fname state))
             (file-dir (get-directory-of-file full-fname)))
        (er-let* ((contents (read-object-file full-fname ctx state)))
          ;; first form is always in-package
          (let ((rw-contents (include-events-rewrite-includes-list (cdr contents) file-dir state)))
            (value `(,@(if encapsulate
                           '(encapsulate nil)
                         '(progn))
                     . ,rw-contents))))))))

(defmacro include-src-events (fname &key dir encapsulate)
  `(make-event (include-events-fn ,fname ,dir ,encapsulate state)))

(defmacro include-events (fname &key dir encapsulate)
  `(make-event (include-events-fn ,(concatenate 'string fname ".lisp") ,dir ,encapsulate state)))
