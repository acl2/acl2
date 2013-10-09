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

#|
(include-book "topics")  ;; Fool dependency scanner, since we may include it
|#

(defmacro save (dir &key
                    (type ':fancy)
                    (import 't)
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
           ((mv & & state) (assign acl2::writes-okp t))
           (state
            ,(if (eq type :fancy)
                 `(save-fancy all-xdoc-topics ,dir state)
               `(save-topics all-xdoc-topics ,dir ',index-pkg ',expand-level state))))
        (value '(value-triple :invisible))))))

