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


; top.lisp -- most end users should include this book directly.  If you are
; new to xdoc, you can try running:
;
;  (include-book "xdoc/top" :dir :system)
;  :xdoc xdoc

(in-package "XDOC")
(include-book "base")

(make-event `(defconst *xdoc-dir/save*
               ,(acl2::extend-pathname *xdoc-dir* "save" state)))
(make-event `(defconst *xdoc-dir/display*
               ,(acl2::extend-pathname *xdoc-dir* "display" state)))
(make-event `(defconst *xdoc-dir/topics*
               ,(acl2::extend-pathname *xdoc-dir* "topics" state)))
(make-event `(defconst *xdoc-dir/defxdoc-raw*
               ,(acl2::extend-pathname *xdoc-dir* "defxdoc-raw" state)))
(make-event `(defconst *xdoc-dir/mkdir-raw*
               ,(acl2::extend-pathname *xdoc-dir* "mkdir-raw" state)))



(defmacro xdoc (name)
  (declare (xargs :guard (or (symbolp name)
                             (and (quotep name)
                                  (symbolp (unquote name))))))
  (let ((name (if (symbolp name)
                  name
                (unquote name))))
    `(with-output :off (summary event)
       (progn
         (include-book ,*xdoc-dir/defxdoc-raw* :ttags :all)
         (include-book ,*xdoc-dir/topics*)
         (include-book ,*xdoc-dir/display*)
         (import-acl2doc)
         (maybe-import-bookdoc)
         (make-event
          (b* (((mv all-xdoc-topics state) (all-xdoc-topics state))
               ((mv & & state) (colon-xdoc-fn ',name all-xdoc-topics state)))
            (value '(value-triple :invisible))))))))

(defmacro save (dir &key
                    (index-pkg 'acl2::foo)
                    (import 't))
  `(progn
     (include-book ,*xdoc-dir/defxdoc-raw* :ttags :all)
     (include-book ,*xdoc-dir/mkdir-raw* :ttags :all)
     (include-book ,*xdoc-dir/save*)

     ;; ugh, stupid stupid writes-ok stupidity
     (defttag :xdoc)
     (remove-untouchable acl2::writes-okp nil)
     ,@(and import
            `((include-book ,*xdoc-dir/topics*)
              (import-acl2doc)
              (maybe-import-bookdoc)))
     (make-event
      (b* (((mv all-xdoc-topics state) (all-xdoc-topics state))
           (- (cw "(len all-xdoc-topics): ~x0~%" (len all-xdoc-topics)))
           ((mv & & state) (assign acl2::writes-okp t))
           (state (save-topics all-xdoc-topics ,dir ',index-pkg state)))
        (value '(value-triple :invisible))))))

(defmacro xdoc-just-from-events (events)
  `(encapsulate
     ()
     (local (include-book ,*xdoc-dir/topics*))
     (local ,events)
     (make-event
      (mv-let (er val state)
        (let ((state (acl2::f-put-global 'acl2::xdoc-alist nil state)))
          (time$ (acl2::write-xdoc-alist :skip-topics xdoc::*acl2-ground-zero-names*)
                 :msg "; Importing :doc topics took ~st sec, ~sa bytes~%"
                 :mintime 1))
        (declare (ignore er val))
        (b* ((topics (acl2::f-get-global 'acl2::xdoc-alist state))
             (- (cw "(len topics): ~x0~%" (len topics))))
          (value `(table xdoc 'doc ',topics)))))))


