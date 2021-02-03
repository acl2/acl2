; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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
(include-book "std/util/bstar" :dir :system)

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
                    (remove1-assoc-equal :parents topic))))
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
                    (remove1-assoc-equal :short topic))))
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
                    (remove1-assoc-equal :long topic))))
    (cons topic (cdr all-topics))))

(defmacro change-long (name new-long)
  `(table xdoc 'doc
          (change-long-fn ',name ',new-long
                             (get-xdoc-table world))))


(defun change-base-pkg-fn (name pkg all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'change-base-pkg-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (change-base-pkg-fn name pkg (cdr all-topics))))
       (topic (cons (cons :base-pkg (acl2::pkg-witness pkg))
                    (remove1-assoc-equal :base-pkg topic))))
    (cons topic (cdr all-topics))))

(defmacro change-base-pkg (name pkg)
  `(table xdoc 'doc
          (change-base-pkg-fn ',name ',pkg
                              (get-xdoc-table world))))




;; Idea:
;;   (without-xdoc (defun foo ...)
;;                 (defxdoc bar...)
;;                 (defxdoc baz ...)
;;                 (defun gah ...))
;;
;; should act like:
;;   (defun foo ...)
;;   (defun gah ...)
;;
;; Implementation: save the xdoc table aside at the start, do all the forms,
;; then smash the xdoc table with whatever we've saved.  This nicely stays
;; make-event free and doesn't, e.g., smash the xdoc table in any kind of
;; permanent or include-book hostile way.
;;
;; By treating the backups as a stack, we can even get this stuff to be
;; properly nestable.

(defun get-xdoc-backup-stack (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'xdoc-backup-stack (table-alist 'xdoc world))))

(defmacro without-xdoc (&rest forms)
  `(progn
     ;; Push current documentation onto the backup stack
     (table xdoc 'xdoc-backup-stack
            (cons (get-xdoc-table world)
                  (get-xdoc-backup-stack world)))
     ;; Do all forms.  They may alter the doc table however they like
     ,@forms
     ;; Restore the doc table from the backup stack, smashing whatever
     ;; the forms did to it.
     (table xdoc 'doc (car (get-xdoc-backup-stack world)))
     ;; Pop the backup stack so that we don't have extra giant tables around
     ;; and for proper nesting stuff.
     (table xdoc 'xdoc-backup-stack (cdr (get-xdoc-backup-stack world)))))

(local (progn

(include-book "std/testing/assert-bang" :dir :system)

(table xdoc 'doc nil)
(defxdoc foo :short "test topic")
(assert! (equal (len (get-xdoc-table (w state))) 1))

(without-xdoc
  (defun xyz (x) x)
  (defxdoc xyz :short "xyz is great!")
  (defun abc (x) x)
  (defxdoc abc :short "abc is great!"))

(assert! (equal (fgetprop 'xyz 'acl2::formals :blah (w state)) '(x))) ;; xyz should be defined
(assert! (equal (fgetprop 'abc 'acl2::formals :blah (w state)) '(x))) ;; abc should be defined
(assert! (equal (len (get-xdoc-table (w state))) 1)) ;; still should just have doc foo

(without-xdoc
  (defxdoc xyz2 :short "xyz is great!")
  (without-xdoc
    (defxdoc abc2 :short "abc is great!")))

(assert! (equal (len (get-xdoc-table (w state))) 1)) ;; still should just have doc foo

))
