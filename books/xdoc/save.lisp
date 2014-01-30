; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")

; Save used to be part of xdoc/top.lisp, but eventually it seemed better to
; move it out into its own book, so that its includes can be handled normally,
; and we can make sure that everything it depends on really is included.
(include-book "import-acl2doc")
(include-book "defxdoc-raw")
(include-book "save-fancy")
(include-book "save-classic")
(include-book "oslib/mkdir" :dir :system)
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
                    (type      ':fancy)
                    (import    't)
                    (redef-okp 'nil)
                    (zip-p     't)
                    ;; Classic options (ignored for type :fancy)
                    (index-pkg 'acl2::foo)
                    (expand-level '1))
  `(progn
     ;; ugh, stupid stupid writes-ok stupidity
     (defttag :xdoc)
     (remove-untouchable acl2::writes-okp nil)
     ,@(and import
            `((include-book
               "xdoc/topics" :dir :system)
              (import-acl2doc)))
     ;; b* should have been included by the above includes
     (make-event
      (b* (((mv all-xdoc-topics state) (all-xdoc-topics state))
           (- (cw "(len all-xdoc-topics): ~x0~%" (len all-xdoc-topics)))
           (redef-report (redef-errors (mergesort all-xdoc-topics)))
           (- (or (not redef-report)
                  (cw "Redefined topics report: ~x0.~%" redef-report)))
           (- (or ,redef-okp
                  (not redef-report)
                  (er hard? 'save
                      "Some XDOC topics have multiple definitions.  The above ~
                       report may help you to fix these errors.  Or, you can ~
                       just call XDOC::SAVE with :REDEF-OKP T to bypass this ~
                       error (and use the most recent version of each topic.)")))
           ((mv & & state) (assign acl2::writes-okp t))
           (state
            ,(if (eq type :fancy)
                 `(save-fancy all-xdoc-topics ,dir ',zip-p state)
               `(save-topics all-xdoc-topics ,dir ',index-pkg ',expand-level state))))
        (value '(value-triple :invisible))))))

