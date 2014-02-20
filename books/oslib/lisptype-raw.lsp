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

(defun lisp-type-fn (state)

  (unless (live-state-p state)
    (er hard? 'getpid "~s0 can only be called on a live state." 'lisp-type)
    (mv nil state))

  (let ((description (common-lisp::lisp-implementation-type)))
    (cond ((stringp description)
           (mv description state))
          ((not description)
           (mv "" state))
          (t
           (error "common-lisp::lisp-implementation-type did not return a string or nil? ~a"
                  description)))))

(defun lisp-version-fn (state)

  (unless (live-state-p state)
    (er hard? 'getpid "~s0 can only be called on a live state." 'lisp-version)
    (mv nil state))

  (let ((description (common-lisp::lisp-implementation-version)))
    (cond ((stringp description)
           (mv description state))
          ((not description)
           (mv "" state))
          (t
           (error "common-lisp::lisp-implementation-version did not return a string or nil? ~a"
                  description)))))

