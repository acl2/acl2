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

(in-package "ACL2")
(include-book "top")
(reset-prehistory nil)

(sidekick::stop)
(acl2::tshell-stop)

:q


(setq *print-startup-banner* nil)


;; HORRIBLE HACK -- fix this when Matt adds :initial-command stuff to save-exec.
;; For now just redefine maybe-load-acl2-init because it's easy.
(defun maybe-load-acl2-init ()
  ;; Blah, recreate some output that print-startup-banner suppresses.  I really
  ;; just want to suppress the ugly modification notice.
  #+ccl
  (format t "~&Welcome to ~A ~A!~%"
          (lisp-implementation-type)
          (lisp-implementation-version))
  (format t
          (concatenate 'string
          "~% ~a built ~a.~
    ~% Copyright (C) 2014, Regents of the University of Texas
    ~% ACL2 comes with ABSOLUTELY NO WARRANTY.  This is free software and you~
    ~% are welcome to redistribute it under certain conditions.  For details,~
    ~% see the LICENSE file distributed with ACL2.~%"
          (or *acl2-svn-revision-string* "~a"))
          *copy-of-acl2-version*
          (saved-build-dates :terminal)
          (if (null *acl2-svn-revision-string*)
              ""
            (qfuncall acl2-books-revision)))
  (format t "~%")
  (sidekick::start))

(save-exec "sidekick" nil)


