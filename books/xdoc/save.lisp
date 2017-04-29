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

; Save used to be part of xdoc/top.lisp, but eventually it seemed better to
; move it out into its own book, so that its includes can be handled normally,
; and we can make sure that everything it depends on really is included.
(include-book "import-acl2doc")
(include-book "defxdoc-raw")
(include-book "save-fancy")
(include-book "xdoc-error")
(include-book "oslib/mkdir" :dir :system)
(include-book "oslib/copy" :dir :system)
(include-book "oslib/rmtree" :dir :system)
(program)

#|
(include-book "topics")  ;; Fool dependency scanner, since we may include it
|#


(defun collect-multiply-defined-topics (x seen-fal)
  (b* (((when (atom x))
        (fast-alist-free seen-fal)
        nil)
       (name1 (cdr (assoc :name (car x))))
       ((when (hons-get name1 seen-fal))
        (cons name1 (collect-multiply-defined-topics (cdr x) seen-fal))))
    (collect-multiply-defined-topics (cdr x) (hons-acons name1 t seen-fal))))

(defun make-redef-error (name x)
  (b* (((when (atom x))
        nil)
       (topic1 (car x))
       ((unless (equal name (cdr (assoc :name topic1))))
        (make-redef-error name (cdr x)))
       (report-line
        (list :from (cdr (assoc :from topic1))
              :short (cdr (assoc :short topic1)))))
    (cons report-line (make-redef-error name (cdr x)))))

(defun make-redef-errors (names x)
  (if (atom names)
      nil
    (cons (cons (car names) (make-redef-error (car names) x))
          (make-redef-errors (cdr names) x))))

(defun redef-errors (x)
  (make-redef-errors
   (mergesort (collect-multiply-defined-topics x (len x)))
   x))

(defmacro save (dir &key
                    (redef-okp  'nil)
                    (zip-p      't)
                    (logo-image 'nil)
                    (error      'nil)
                    (broken-links-limit 'nil))
  (declare (xargs :guard (booleanp error))) ; probably incomplete
  `(progn
     ;; ugh, stupid stupid writes-ok stupidity
     (defttag :xdoc)
     (remove-untouchable acl2::writes-okp nil)
     ;; b* should have been included by the above includes
     (make-event
      (b* ((- (initialize-xdoc-errors ,error))
           ((mv ? all-xdoc-topics state) (all-xdoc-topics state))
           (- (cw "(len all-xdoc-topics): ~x0~%" (len all-xdoc-topics)))
           (redef-report
            ;; To support special cases (for instance, "locally" including a
            ;; book to extract its documentation, then perhaps later
            ;; re-including that book), it seems pretty reasonable not to warn
            ;; or complain about topics that are exact duplicates of one
            ;; another.  So, we create our redefinition report from sorted
            ;; topics.
            (redef-errors (mergesort all-xdoc-topics)))
           (- (or (not redef-report)
                  (cw "Redefined topics report: ~x0.~%" redef-report)))
           (- (or ,redef-okp
                  (not redef-report)
                  (er hard? 'save
                      "Some XDOC topics have multiple definitions.  The above ~
                       report may help you to fix these errors.  Or, you can ~
                       just call XDOC::SAVE with :REDEF-OKP T to bypass this ~
                       error (and use the most recent version of each topic.)")))

           ;; Now remove all shadowed topics before doing anything more.
           ((mv & & state) (assign acl2::writes-okp t))
           (- (acl2::tshell-ensure))
           (state (save-fancy all-xdoc-topics ,dir ,zip-p ,logo-image
                              ,broken-links-limit state))
           (- (report-xdoc-errors 'save)))
        (value '(value-triple :invisible))))))
