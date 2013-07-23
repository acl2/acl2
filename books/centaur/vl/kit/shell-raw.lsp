; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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

(defun vl::vl-shell-fn (argv state)
  (declare (ignore argv))
  (format t "VL Verilog Toolkit
Copyright (C) 2008-2013 Centaur Technology <http://www.centtech.com>

  This program is free software; you can redistribute it and/or modify it under
  the terms of the GNU General Public License as published by the Free Software
  Foundation; either version 2 of the License, or (at your option) any later
  version.  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
  more details.  You should have received a copy of the GNU General Public
  License along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301,
  USA.

,-------------------------,
|  VL Interactive Shell   |     This is an interactive ACL2 shell with VL pre-
|     (for experts)       |     loaded.  To learn about ACL2 (and hence how to
|                         |     use this shell) see the ACL2 homepage:
|   Type :quit to quit    |      http://www.cs.utexas.edu/users/moore/acl2
`-------------------------'

")

  (f-put-global 'ld-verbose nil state)
  (acl2-default-restart)
  state)


;; Suppress ACL2 greeting stuff (relevant only for "vl shell" command)

(defun acl2-default-restart ()
  (if *acl2-default-restart-complete*
      (return-from acl2-default-restart nil))

  (#+cltl2
   common-lisp-user::acl2-set-character-encoding
   #-cltl2
   user::acl2-set-character-encoding)

  (fix-default-pathname-defaults)

  #+hons (qfuncall acl2h-init)

  (maybe-load-acl2-init)
  (eval `(in-package ,*startup-package-name*))

; The following two lines follow the recommendation in Allegro CL's
; documentation file doc/delivery.htm.

  #+allegro (tpl:setq-default *package* (find-package *startup-package-name*))
  #+allegro (rplacd (assoc 'tpl::*saved-package*
                           tpl:*default-lisp-listener-bindings*)
                    'common-lisp:*package*)
  #+allegro (lp)
  #+lispworks (lp)
  #+ccl (eval '(lp)) ; using eval to avoid compiler warning

  (setq *acl2-default-restart-complete* t)
  nil)



; BOZO horrible stupid gross hack.  Part of this should get integrated into
; ACL2 (the use of -- "$@" instead of $*.)  It'd be nice to have first-class
; support for a different -e in ACL2 as well.

#+Clozure
(defun save-acl2-in-ccl-aux (sysout-name core-name)
  (let* ((ccl-program0
          (or (car ccl::*command-line-argument-list*) ; Gary Byers suggestion
              (error "Unable to determine CCL program pathname!")))
         (ccl-program (qfuncall pathname-os-to-unix
                                ccl-program0
                                (get-os)
                                *the-live-state*))
         (core-name (unix-full-pathname core-name
                                        (pathname-name ccl-program))))
    (when (probe-file sysout-name)

; At one point we supplied :if-exists :overwrite in the first argument to
; with-open-file below.  Robert Krug reported problems with that solution in
; OpenMCL 0.14 (CCL).  A safe solution seems to be simply to delete the file
; before attempting to write to it.

      (delete-file sysout-name))
    (when (probe-file core-name)
      (delete-file core-name))
    (with-open-file ; write to nsaved_acl2
     (str sysout-name :direction :output)
     (write-exec-file str

; Gary Byers has pointed out (Feb. 2009) that:

;    In order for REQUIRE (and many other things) to work, the lisp needs
;    to know where its installation directory (the "ccl" directory) is.
;    (More accurately, the "ccl" logical host has to has its logical-pathname
;    translations set up to refer to that directory:)
;
;    ? (truename "ccl:")
;    #P"/usr/local/src/ccl-dev/"

; So we make an effort to set CCL_DEFAULT_DIRECTORY correctly so that the above
; truename will be correct.

                      ("~a~%"
                       (let ((default-dir
                               (or (ccl::getenv "CCL_DEFAULT_DIRECTORY")
                                   (let ((path (our-truename "ccl:")))
                                     (and path
                                          (qfuncall pathname-os-to-unix
                                                    (namestring path)
                                                    (get-os)
                                                    *the-live-state*))))))
                         (if default-dir
                             (format nil
                                     "export CCL_DEFAULT_DIRECTORY=~s"
                                     default-dir)
                           "")))

; It is probably important to use -e just below instead of :toplevel-function,
; at least for #+hons.  Jared Davis and Sol Swords have told us that it seems
; that with :toplevel-function one gets a new "toplevel" thread at start-up,
; which "plays badly with the thread-local hash tables that make up the hons
; space".

; See the section on "reading characters from files" in file acl2.lisp for an
; explanation of the -K argument below.

                      "~s -I ~s -K ISO-8859-1 -e \"(vl::vl-main ccl::*unprocessed-command-line-arguments*)\" -- \"$@\"~%"
                      ccl-program
                      core-name))
    (chmod-executable sysout-name)
    (ccl::gc)
    (ccl:save-application core-name)))
