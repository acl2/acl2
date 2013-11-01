; Standard IO Library
; read-string.lisp
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

(in-package "ACL2")

(defun read-string-fn (str state)
  (handler-case
   (progn (unless (live-state-p state)
            (error "read-string requires a live state!"))
          (let ((acc nil)
                (*readtable* *acl2-readtable*))
            (with-input-from-string
             (stream str)
             (loop do
                   (let* ((eof-marker (cons nil nil))
                          (elem       (read stream nil eof-marker)))
                     (if (eq elem eof-marker)
                         (loop-finish)
                       (push elem acc)))))
            (setq acc (nreverse acc))
            (let ((msg (bad-lisp-objectp acc)))
              (if msg
                  (mv msg nil state)
                (mv nil acc state)))))
   (error (condition)
          (return-from read-string-fn
                       (mv (format nil "~S" condition) nil state)))
   ;; Really bad-lisp-objectp shouldn't just stack-overflow on #1=(a . #1#).
   ;; Catching it is tricky...
   ;; "Because such a condition is indicative of a limitation of the
   ;;  implementation or of the image rather than an error in a program,
   ;;  objects of type storage-condition are not of type error."
   (storage-condition (condition)
                      (return-from read-string-fn
                                   (mv (format nil "~S" condition) nil state)))))

