; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "top")
(include-book "tools/bstar" :dir :system)

(defun delete-topic-fn (name all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'delete-topic-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (delete-topic-fn name (cdr all-topics)))))
    (cdr all-topics)))

(defmacro delete-topic (name)
  `(table xdoc 'doc
          (delete-topic-fn ',name (get-xdoc-table world))))

(defun change-parents-fn (name new-parents all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'change-parents-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (change-parents-fn name new-parents (cdr all-topics))))
       (topic (cons (cons :parents new-parents)
                    (delete-assoc-equal :parents topic))))
    (cons topic (cdr all-topics))))

(defmacro change-parents (name new-parents)
  `(table xdoc 'doc
          (change-parents-fn ',name ',new-parents
                             (get-xdoc-table world))))

(defun change-short-fn (name new-short all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'change-short-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (change-short-fn name new-short (cdr all-topics))))
       (topic (cons (cons :short new-short)
                    (delete-assoc-equal :short topic))))
    (cons topic (cdr all-topics))))

(defmacro change-short (name new-short)
  `(table xdoc 'doc
          (change-short-fn ',name ',new-short
                             (get-xdoc-table world))))


(defun change-long-fn (name new-long all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'change-long-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (change-long-fn name new-long (cdr all-topics))))
       (topic (cons (cons :long new-long)
                    (delete-assoc-equal :long topic))))
    (cons topic (cdr all-topics))))

(defmacro change-long (name new-long)
  `(table xdoc 'doc
          (change-long-fn ',name ',new-long
                             (get-xdoc-table world))))


