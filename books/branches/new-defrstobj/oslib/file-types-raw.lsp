; OSLIB -- Operating System Utilities
; Copyright (C) 2013 Centaur Technology
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

(in-package "OSLIB")
(ql:quickload "osicat")

(defun file-kind-fn (path follow-symlinks state)
  (unless (live-state-p state)
    (error "file-kind can only be called on a live state."))
  (mv-let (errmsg result)
    (handler-case
     (multiple-value-bind
         (main-kind broken)
         (osicat::file-kind path :follow-symlinks follow-symlinks)
       (cond ((and follow-symlinks broken)
              (assert (eq main-kind :symbolic-link))
              (mv (msg "Error in file-kind for ~x0: broken symlink." path)
                  nil))
             ((file-kind-p main-kind)
              (mv nil main-kind))
             (t
              (mv (msg "Error in file-kind for ~x0: osicat::file-kind returned ~
                        unexpected value ~s1."
                       path
                       (format nil "~a" main-kind))
                  nil))))
     (error (condition)
            (mv (msg "Error in file-kind: ~s0." (format nil "~a" condition))
                nil)))
    (mv errmsg result state)))

