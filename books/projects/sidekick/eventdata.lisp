; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows, Austin TX, 78759, USA.
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")
(include-book "lock")
(include-book "tools/bstar" :dir :system)
(include-book "std/strings/defs-program" :dir :system)
(program)

(defun sidekick-eventdata-push (data)
  (declare (ignorable data))
  (declare (xargs :guard t
                  :mode :logic))
  (er hard? 'sidekick-eventdata-push "raw lisp definition not installed?"))

(defun sidekick-finalize-event-user (ctx body state)
  (declare (xargs :stobjs state
                  :mode :logic))
  (b* ((alist (list* (cons :ctx ctx)
                     (cons :body body)
                     (and (acl2::f-boundp-global 'acl2::last-event-data state)
                          (acl2::f-get-global 'acl2::last-event-data state)))))
    (with-sidekick-lock
      (sidekick-eventdata-push alist))
    state))

(defun sidekick-get-all-event-data ()
  (declare (xargs :guard t))
  ;; BOZO completely unsound
  (er hard? 'sidekick-get-all-event-data "raw lisp definition not installed?"))

(defttag :sidekick)
; (depends-on "eventdata-raw.lsp")
(include-raw "eventdata-raw.lsp")

(defattach acl2::finalize-event-user sidekick-finalize-event-user)



(defun eventdata->namex (x)
  (let ((look (assoc 'acl2::namex x)))
    (and look
         (cdr look))))

(defun find-eventdata (name all-event-data)
  (b* (((when (atom all-event-data))
        nil)
       (namex1 (eventdata->namex (car all-event-data)))
       ((when (and namex1
                   (or (eq namex1 name)
                       (and (symbol-listp namex1)
                            (member name namex1)))))
        (car all-event-data)))
    (find-eventdata name (cdr all-event-data))))

(defun eventdata->total-time (x)
  (let ((times (cdr (assoc 'acl2::time x))))
    (if (and (equal (len times) 4)
             (rational-listp times))
        ;; Allegedly the format is: (prove print proof-tree other)
        (+ (first times)
           (second times)
           (third times)
           (fourth times))
      nil)))

(defun chop-to-hundreths (x)
  (declare (xargs :guard (and (rationalp x)
                              (<= 0 x))))
  (let* ((ipart    (truncate x 1))
         (fpart    (- x ipart))
         (100fpart (* fpart 100))
         (chop     (truncate 100fpart 1)))
    (cat (natstr ipart)
         "."
         (if (< chop 10)
             (cat "0" (natstr chop))
           (natstr chop)))))

#||

(chop-to-hundreths
 (eventdata->total-time
  (find-eventdata 'vl::vl-exprlist->finalwidths (sidekick-get-all-event-data))))

||#

;; Good deal.  So, next time:
;;
;;  - figure out how to grab all events from a command block
;;  - simple sum up their total times, etc.
;;  - implement top-level command-block-time command.




