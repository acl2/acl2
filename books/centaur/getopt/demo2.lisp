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

(in-package "GETOPT-DEMO")
(include-book "top")
(include-book "oslib/argv" :dir :system)
(set-state-ok t)

(defsection demo2
  :parents (getopt)
  :short "Demonstration of how to use @(see getopt) and @(see argv) to create a
working command-line program from ACL2."

  :long "<p>This is an example of how to write an extremely basic command-line
program in ACL2 that parses some options from the command-line.</p>

<p>Note: our focus in this demo is to show how @(see getopt) and @(see argv)
and @(see save-exec) work together.  Our program takes just a few basic
options.  If you want to see a demo of how to parse fancier command-line
options, see @(see demo) instead.</p>

<p>Depending on its input, our program will print out:</p>

<ul>
<li>A help message (--help or -h)</li>
<li>A version message (--version or -v)</li>
<li>The nonsense sentence @('colorless green ideas sleep furiously').</li>
</ul>

<p>Our top-level program is @(see demo2-main).</p>

<ul>
 <li>It uses @(see argv) to get the command-line options.</li>
 <li>It uses @(see getopt) to parse them into a @(see demo2-opts-p) structure.</li>
 <li>It then prints a message, as described above.</li>
</ul>

<p>To see how to turn @('demo2-main') into an executable, see the file
@('centaur/getopt/demo2-save.lsp').</p>")

(defoptions demo2-opts
  :parents (demo2)
  :tag :demo2

  ((help    "Print a help message and exit with status 0."
            booleanp
            :rule-classes :type-prescription
            :alias #\h)

   (version "Print out a version message and exit with status 0."
            booleanp
            :rule-classes :type-prescription
            :alias #\v)))

(defsection demo2-main
  :parents (demo2)
  :short "Run the demo2 program."

  (defund demo2-main (state)
    (b* (((mv argv state)              (oslib::argv))
         ((mv errmsg opts ?extra-args) (parse-demo2-opts argv))

         ((when errmsg)
          (cw "~@0~%" errmsg)
          (exit 1)
          state)

         ((demo2-opts opts) opts)

         ((when opts.help)
          (b* ((- (cw "demo2: how to write a command line program in ACL2~%"))
               (state (princ$ *demo2-opts-usage* *standard-co* state))
               (- (cw "~%")))
            (exit 0)
            state))

         ((when opts.version)
          (cw "demo2: version 1.234~%")
          (exit 0)
          state))

      (cw "colorless green ideas sleep furiously~%")
      (exit 0)
      state)))

