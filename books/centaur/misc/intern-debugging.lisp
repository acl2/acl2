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
(include-book "oslib/lisptype" :dir :system)
(include-book "std/strings/defs-program" :dir :system)

(make-event
 (let ((state
        (b* ((__function__ 'centaur/misc/intern-debugging.lisp)
             ((fun (warn-version version))
              (cw "~|~%WARNING (centaur/misc/intern-debugging): consider ~
                   upgrading CCL.  (Your current version, ~s0, may perform ~
                   badly when interning millions of symbols, which can cause ~
                   problems for VL/ESIM.)~%~%"
                  version))

             ((mv type state) (oslib::lisp-type))
             ((unless (equal type "Clozure Common Lisp"))
              ;; Not using CCL anyway, no need to worry about CCL issues.
              state)

             ((mv version state) (oslib::lisp-version)) ;; E.g., "Version 1.9-r15996  (LinuxX8664)"
             (tokens (str::strtok version '(#\Space)))
             ((unless (and (equal (first tokens) "Version")
                           (stringp (second tokens))))
              (raise "Failed to parse CCL version: Expected 'Version': ~s0" version)
              state)

             (vnums (str::strtok (second tokens) '(#\- #\r))) ;; E.g., ("1.9" "15996")
             ((when (atom vnums))
              (raise "Failed to parse CCL version: Expected something after 'Version': ~s0" version)
              state)

             (release (car vnums))
             (svnrev (and (consp (cdr vnums))
                          (stringp (second vnums))
                          (str::strval (second vnums))))
             ((when svnrev)
              ;; Just base things on the svn revision.
              (if (< svnrev 16019)
                  (warn-version version)
                nil)
              state)

             ;; Perhaps there is no SVN revision?
             (reltokens (str::strtok release '(#\.)))
             ;; E.g., ("1" "9")
             (major (and (stringp (first reltokens))
                         (str::strval (first reltokens))))
             (minor (and (stringp (second reltokens))
                         (str::strval (second reltokens))))
             ((unless (and major minor))
              (raise "Failed to parse CCL release version: ~s0" version)
              state)
             ((when (or (<= 2 major)  ;; 2.0 or later
                        (and (equal major 1) ;; 1.10 or later
                             (<= 10 minor))))
              state))
          (warn-version version)
          state)))
   (value '(value-triple :invisible)))
 :check-expansion t)
