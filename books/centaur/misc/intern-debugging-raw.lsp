; Intern Debugging
; Copyright (C) 2010 Centaur Technology
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

#+Clozure
(progn

; Accessors for symbol hash tables.
; Per nfasload.lisp, symbol hash tables are (htvec . (htcount . hlimit))

  (defmacro ccl-htvec (tbl)
    `(the simple-vector (car ,tbl)))

  (defmacro ccl-htcount (tbl)
    `(the fixnum (cadr ,tbl)))

  (defmacro ccl-htlimit (tbl)
    `(the fixnum (cddr ,tbl)))

; Basic way to inspect packages, which we make available to the logic.

  (defun inspect-package (name)
    (let* ((pkg (or (find-package name)
                    (er hard? 'inspect-package "package ~x0 not found." name)))
           (tab (ccl::pkg.itab pkg)))
      (format t "; - Current count: ~:D~%" (ccl-htcount tab))
      (format t "; - Current limit: ~:D~%" (ccl-htlimit tab))
      nil))

  (setq ccl::*warn-if-redefine-kernel* nil)

  (defun intern (str &optional (package *package*))
    ;; (format t "Debugging intern is being called.~%")
    (let* ((pkg (ccl::pkg-arg package))
           (tab (ccl::pkg.itab pkg)))
      (when (and (= (ccl-htcount tab)
                    (the fixnum (1- (ccl-htlimit tab))))
                 ;; Don't bother reporting on very small packages resizing.
                 ;; This helps avoid package-size messages when including
                 ;; books, for instance.
                 (< 10000 (ccl-htcount tab)))
        (let ((name (package-name pkg)))
          (format t "~%; Note: we may be about to resize the ~a package.~%" name)
          (format t "; Before interning ~a:~%" str)
          (inspect-package name)
          (let ((ret (time (ccl::%intern str pkg))))
            (format t "; After interning ~a:~%" str)
            (inspect-package name))
          (format t "~%")
          ret))
      (ccl::%intern str pkg)))

  (defun ccl::%pkg-ref-intern (str ref)
    ;; It seems necessary to also redefine this to get compiled functions with
    ;; interns in them to call our new intern.
    (intern str (or (ccl::package-ref.pkg ref)
                    (ccl::%kernel-restart ccl::$xnopkg (ccl::package-ref.name ref)))))

  (setq ccl::*warn-if-redefine-kernel* t))
