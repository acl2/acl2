; ACL2 Event Origin
; Copyright (C) 2013 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759
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
; Original authors: Jared Davis <jared@kookamara.com>

; Modified by Matt Kaufmann 8/28/2013 to avoid command world errors.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(set-state-ok t)
(program)

(defxdoc origin
  :parents (acl2::pe)
  :short "Returns a summary of where a @(see logical-name) originates from."
  :long "<p>Examples:</p>
@({
  (include-book \"system/origin\" :dir :system)

  ;; built-in names get a return value of :built-in
  (origin 'consp)    --> (value :built-in)
  (origin 'car-cons) --> (value :built-in)

  ;; include-book path is reported for events included from other books
  (origin 'xdoc::save) --> (value (\"/home/jared/acl2/books/system/origin.lisp\"
                                   \"/home/jared/acl2/books/xdoc/top.lisp\"))

  (origin 'lnfix) --> (value (\"/home/jared/acl2/books/system/origin.lisp\"
                              \"/home/jared/acl2/books/xdoc/top.lisp\"
                              \"/home/jared/acl2/books/xdoc/base.lisp\"))

  ;; some definitions are from the current session, e.g.:
  (defun f (x) x)
  (origin 'f)     --> (value :TOP-LEVEL)

  ;; bad names
  (mv-let (er val state)               ;; ((:er (\"Not a logical name: ~x0\"
          (origin 'not-defined-thing)  ;;        (#\0 . NOT-DEFINED-THING))
   (mv (list :er er :val val)          ;;   :val nil)
       state))                         ;;  <state>)

})")

(defun origin-fn (logical-name state)
  (let* ((wrld (w state)))
    (cond
     ((acl2-system-namep logical-name wrld)
      (value :built-in))
     (t
      (let ((ev-wrld (decode-logical-name logical-name wrld)))
        (cond (ev-wrld
               (value (let ((book-path (global-val 'include-book-path ev-wrld)))
                        (cond (book-path
                               (reverse book-path))
                              (t
                               :top-level)))))
              (t (mv (msg "Not logical name: ~x0." logical-name) nil state))))))))

(defmacro origin (logical-name)
  `(origin-fn ,logical-name state))

