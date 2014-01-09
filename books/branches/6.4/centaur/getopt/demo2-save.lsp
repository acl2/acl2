; ACL2 Getopt Library
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


; You can give this script to ACL2 using something like:
;
;  ACL2_CUSTOMIZATION=NONE acl2 < demo2-save.lsp
;
; This should create a demo2 script and Lisp image that:
;
;   - Doesn't print any startup stuff
;   - Doesn't read any customization files
;   - Reads and processes the command-line arguments
;
; E.g.,
;
;     $ ./demo2
;     colorless green ideas sleep furiously
;     $ echo $?
;     0
;
;     $ ./demo2 --help
;     demo2: how to write a command line program in ACL2
;         -h,--help             Print a help message and exit with status 0.
;         -v,--version          Print out a version message and exit with
;                               status 0.
;     $ echo $?
;     0
;
;     $ ./demo2 --version
;     demo2: version 1.234
;     $ echo $?
;     0
;
;     $ ./demo2 --foo
;     Unrecognized option --foo
;     $ echo $?
;     1
;
;     $ ./demo2 --help=17
;     Option --help can't take an argument
;     $ echo $?
;     1

(include-book "demo2")

:q

;; Set up our program to not print a bunch of ACL2 banners.
(setq *print-startup-banner* nil)

;; Set up our program NOT try to read the any customization files.
(defun initial-customization-filename () :none)

(save-exec "demo2" "getopt demo 2 program"

           ;; Inert-args MUST be given, or ACL2 won't put the "--" into the
           ;; startup script, and ARGV won't know which arguments belong to the
           ;; Lisp, and which belong to our program.
           :inert-args ""
           :return-from-lp '(getopt-demo::demo2-main acl2::state))



