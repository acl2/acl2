; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "progutils")
(include-book "tools/include-raw" :dir :system)
(include-book "std/util/define" :dir :system)
; (depends-on "shell-raw.lsp")

(defxdoc vl-shell
  :parents (kit)
  :short "An interactive VL command loop.  Allows you to use the VL @(see kit)
as a normal copy of @(see acl2) with VL preloaded."

  :long "<p>The @('vl shell') enters a Lisp read-eval-print loop.  From this
loop you can invoke @(see acl2::lp) to get into an @(see acl2) session where
much of VL is already loaded.  This is an advanced feature that is mainly
intended for developers who are debugging and hacking on VL.</p>

<p>For usage information, you can run @('vl shell --help'), or see @(see
*vl-shell-help*).</p>")

(local (xdoc::set-default-parents vl-shell))

(defval *vl-shell-help*
  :showdef nil
  :showval t
  "
vl shell:  Starts an interactive VL command loop (for experts).

Usage:     vl shell    (there are no options)

VL is built atop the ACL2 theorem prover.  The VL shell gives you access to the
ACL2 command loop, with all of the VL functions already built in.

This is an advanced feature that is mainly intended for developers who are
debugging and hacking on VL.

")

(define vl-shell-entry ((events true-listp) &key (state 'state))
  :short "Implementation-level @('vl shell') command."
  :long "<p>This command is defined in raw Lisp, see @('shell-raw.lsp') for
details.</p>

<p>Its argument is a list of ACL2 events to run before presenting the user with
an interactive shell.</p>"
  :returns state
  :ignore-ok t
  (progn$ (die "Raw lisp definition not installed?")
          state))


(define vl-shell-top ((argv string-listp) &key (state 'state))
  :short "Top-level @('vl shell') command."
  :long "<p>This command just calls @(see vl-shell-entry).  It provides a
single event that saves the user arguments as an ACL2 constant named
@('vl::*vl-shell-argv*').</p>"
  :returns state
  :ignore-ok t
  (vl-shell-entry `((defconst vl::*VL-SHELL-ARGV* ',argv))))

(defttag :vl-shell)
(acl2::include-raw "shell-raw.lsp")

