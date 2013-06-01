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

  ;; certain built-in commands don't have a command number
  (origin 'consp)    --> (value (:built-in nil))

  ;; other built-in ACL2 commands have command numbers
  (origin 'car-cons) --> (value (:built-in -936))

  ;; include-book path is reported for events included from other books
  (origin 'xdoc::save) --> (value (\"/home/jared/acl2/books/system/origin.lisp\"
                                   \"/home/jared/acl2/books/xdoc/top.lisp\"))

  (origin 'lnfix) --> (value (\"/home/jared/acl2/books/system/origin.lisp\"
                              \"/home/jared/acl2/books/xdoc/top.lisp\"
                              \"/home/jared/acl2/books/xdoc/base.lisp\"))

  ;; some definitions are from the current session, e.g.:
  (defun f (x) x)
  (origin 'f)     --> (value 3)

})")


(defun origin-fn1 (wrld ev-wrld cmd-wrld)
  ;; Styled after PE-FN1.  I have no idea what I'm doing.
  (cond
   ((equal (access-event-tuple-form (cddar ev-wrld))
           (access-command-tuple-form (cddar cmd-wrld)))
    ;; This handles two kinds of things:
    ;;  (1) built-in things with a defining event, and
    ;;  (2) things from the current session (not an include-book)
    ;; :pe-fn1 would do a print-ldd of a make-command-ldd here, which, if you work out
    ;; the cases, seems to be just doing this:
    (absolute-to-relative-command-number
     (access-command-tuple-number (cddar cmd-wrld))
     wrld))
   (t
    (let ((book-path (global-val 'include-book-path ev-wrld)))
      (cond (book-path
             (reverse book-path))
            (t
             :session?))))))

(defun origin-fn (logical-name ctx state)
  ;; Styled after PE-FN.  I have no idea what I'm doing.
  (let ((wrld (w state)))
    (cond
     ((and (symbolp logical-name)
           (not (eq logical-name :here))
           (zp (getprop logical-name 'absolute-event-number nil 'current-acl2-world wrld)))
      ;; Things that are built into ACL2 without a defining event
      (value (list :built-in nil)))
     (t
      (er-let*
       ((ev-wrld  (er-decode-logical-name logical-name wrld ctx state))
        (cmd-wrld (superior-command-world ev-wrld wrld ctx state)))
       (value (origin-fn1 wrld ev-wrld cmd-wrld)))))))

(defmacro origin (logical-name)
  `(origin-fn ,logical-name 'origin state))

