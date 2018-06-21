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

; base.lisp -- This file is only intended mainly to avoid a circular dependence
; between top.lisp and topics.lisp.  Ordinary users should include top.lisp
; instead.

(in-package "XDOC")
(set-state-ok t)

(table xdoc 'doc nil)
(table xdoc 'default-parents nil)
(table xdoc 'post-defxdoc-event nil)
(table xdoc 'resource-dirs nil)

(defun get-xdoc-table (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'doc (table-alist 'xdoc world))))

(defmacro set-default-parents (&rest parents)
  `(table xdoc 'default-parents
          (let ((parents ',parents))
            (cond ((symbol-listp parents)
                   parents)
                  ((and (consp parents)
                        (atom (cdr parents))
                        (symbol-listp (car parents)))
                   (car parents))
                  (t
                   (er hard? 'set-default-parents
                       "Expected a symbol-listp, but found ~x0" parents))))))

(defun get-default-parents (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'default-parents (table-alist 'xdoc world))))

(defun check-defxdoc-args (name parents short long pkg)
  (declare (xargs :guard t))
  (or (and (not (symbolp name))
           "name is not a symbol!")
      (and (not (symbol-listp parents))
           ":parents are not a symbol list")
      (and short (not (stringp short))
           ":short is not a string (or nil)")
      (and long (not (stringp long))
           ":long is not a string (or nil)")
      (and pkg (or (not (stringp pkg)) (equal pkg "") (not (pkg-witness pkg)))
           ":pkg is not a string that is a known package (or nil)")))

(defun guard-for-defxdoc (name parents short long pkg)
  (declare (xargs :guard t))
  (let* ((err (check-defxdoc-args name parents short long pkg)))
    (or (not err)
        (cw "~s0~%" err))))

(local (defthm state-p1-implies-all-boundp
         (implies (state-p1 st)
                  (all-boundp acl2::*initial-global-table* (global-table st)))
         :hints(("Goal" :in-theory (enable state-p1)))
         :rule-classes nil))

(defun normalize-bookname (bookname state)
  (declare (xargs :stobjs (state)
                  :guard-hints (("goal" :use ((:instance state-p1-implies-all-boundp
                                               (st state)))
                                 :in-theory (disable all-boundp assoc)
                                 :expand ((:free (a b x) (all-boundp (cons a b) x)))))
                  :guard t))  ;; WAHJr. added guard (see original below)
  (let ((dir-system (acl2::f-get-global 'acl2::system-books-dir state)))
    (if (not (and (stringp dir-system) (stringp bookname)))
        bookname
      (let ((lds (length dir-system)))
        ;; Eventually we could do something fancier to support
        ;; add-include-book-dirs, but this is probably fine for the
        ;; Community Books, at least.
        (if (and (<= lds (length bookname))
                 (equal dir-system (subseq bookname 0 lds)))
            (concatenate 'string "[books]/"
                         (subseq bookname lds nil))
          bookname)))))

(defun defxdoc-fn (name parents short long pkg no-override state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((err (check-defxdoc-args name parents short long pkg)))
    (if err
        (er hard? 'defxdoc
            "Bad defxdoc arguments: ~s0" err)
      (let* ((world (w state))
             (pkg   (or pkg (acl2::f-get-global 'acl2::current-package state)))
             (info  (acl2::f-get-global 'acl2::certify-book-info state))
             (bookname (if info
                           (acl2::access acl2::certify-book-info info :full-book-name)
                         "Current Interactive Session"))
             (bookname (normalize-bookname bookname state))
             (parents (or parents (get-default-parents (w state))))
             (entry (list (cons :name name)
                          (cons :base-pkg (acl2::pkg-witness pkg))
                          (cons :parents parents)
                          (cons :short short)
                          (cons :long long)
                          (cons :from bookname)))
             (table-event
              `(table xdoc 'doc
                      ,(if no-override
                           `(let ((topics (get-xdoc-table world)))
                              (if (find-topic ',name topics)
                                  topics
                                (cons ',entry topics)))
                         `(cons ',entry (get-xdoc-table world)))))
             (post-event
              (cdr (assoc-eq 'post-defxdoc-event (table-alist 'xdoc world)))))
        `(progn
           ,table-event
           ,@(and post-event (list post-event))
           (value-triple '(defxdoc ,name)))))))

(defmacro defxdoc (name &key parents short long pkg no-override)
  `(with-output :off (event summary)
     (make-event
      (defxdoc-fn ',name ',parents ,short ,long ,pkg ,no-override state))))

(defun defxdoc-raw-fn (name parents short long pkg)
  (declare (xargs :guard t)
           (ignore name parents short long pkg))
  (er hard? 'defxdoc-raw-fn
      "Under-the-hood definition of defxdoc-raw-fn not installed.  You ~
       probably need to load the defxdoc-raw book."))

(defun defxdoc-raw-after-check (name parents short long pkg)
  (declare (xargs :guard t))
  (let* ((err (check-defxdoc-args name parents short long pkg)))
    (if err
        (er hard? 'defxdoc-raw
            "Bad defxdoc-raw arguments: ~s0~%" err)
      (defxdoc-raw-fn name parents short long pkg))))

(defmacro defxdoc-raw (name &key parents short long pkg)
  `(defxdoc-raw-after-check ',name ',parents ,short ,long ,pkg))

(defun find-topic (name x)
  (declare (xargs :mode :program))

; Look up a particular topic by name in the list of topics.

  (if (atom x)
      nil
    (if (equal (cdr (assoc :name (car x))) name)
        (car x)
      (find-topic name (cdr x)))))


(defun gather-topic-names (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (cons (cdr (assoc :name (car x)))
          (gather-topic-names (cdr x)))))

(defun topics-fal (x)
  (declare (xargs :mode :program))
  (make-fast-alist (pairlis$ (gather-topic-names x) x)))
