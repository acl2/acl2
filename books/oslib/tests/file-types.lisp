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

(in-package "ACL2")
(include-book "../file-types")
(include-book "std/util/defconsts" :dir :system)

(defttag :sys-call)

(defmacro check-file-kind (path expected-type &key follow-symlinks)
  `(make-event
    (b* ((path ',path)
         (expected-type ',expected-type)
         (follow-symlinks ',follow-symlinks)
         ((mv err ans state) (oslib::file-kind path
                                               :follow-symlinks follow-symlinks))
         (- (cw "; path ~s0 -> ~x1~%"
                path
                (list :err err :ans ans :expect expected-type)))
         (okp (if (eq expected-type :error)
                  (and (or err
                           (cw "Oops, expected error but no error."))
                       (or (not ans)
                           (cw "Oops, expected no answer.")))
                (and (or (not err)
                         (cw "Oops, expected no error."))
                     (or (eq ans expected-type)
                         (cw "Oops, wrong type.")))))
         ((when okp)
          (value '(value-triple :success))))
      (er soft 'check-file-kind "Assertion failed"))))

(check-file-kind "/" :directory)
(check-file-kind "file-types.lisp" :regular-file)
(check-file-kind "does-not-exist.txt" nil)

(make-event
 (b* ((- (sys-call "./makelink.sh" nil)))
   (value '(value-triple :makelink))))

(check-file-kind "test-link"
                 :symbolic-link
                 :follow-symlinks nil)

(check-file-kind "test-link"
                 :regular-file
                 :follow-symlinks t)


#+Unix ;; <-- maybe need to tweak this
(progn
  (check-file-kind "/dev/null" :character-device)
  (check-file-kind "/dev/sda1" :block-device))
