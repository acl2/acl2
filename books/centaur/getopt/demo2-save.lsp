; ACL2 Getopt Library
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
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

;; Avoid causing a difference with the expected output.
(setq common-lisp-user::*acl2-exit-lisp-hook* nil)


#+allegro
(defun acl2::exit-lisp (&optional (status '0 status-p))
  (excl:exit status :no-unwind t :quiet t))

(save-exec "demo2" "getopt demo 2 program"

           ;; Inert-args MUST be given, or ACL2 won't put the "--" into the
           ;; startup script, and ARGV won't know which arguments belong to the
           ;; Lisp, and which belong to our program.
           :inert-args ""
           :return-from-lp '(getopt-demo::demo2-main acl2::state))



