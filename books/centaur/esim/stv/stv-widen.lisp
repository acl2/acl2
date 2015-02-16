; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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


; stv-widen.lisp -- widening of STV input and output lines
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "std/lists/repeat" :dir :system)
(local (include-book "std/lists/take" :dir :system))

(define stv-widen-lines ((lines true-list-listp)
                         (number-of-phases natp)
                         (warn-non-blank booleanp))
  :returns (widened-lines true-list-listp :hyp :guard)
  :parents (stv-widen)
  :short "Rewrite lines of an STV, repeating the last entry in each line to
extend it to the desired number of phases."

  :long "<p>The @('warn-non-blank') is intended to be set for :output lines
and :internals lines.  When it is set, we cause an error if an attempt is made
to replicate any element other than @('_'), since it doesn't make sense to
replicate simulation variables.</p>"

  (b* (((when (atom lines))
        nil)
       (line1         (car lines))
       (line1-name    (car line1))
       (line1-phases  (cdr line1))
       (- (or (consp line1-phases)
              (er hard? 'stv-widen-lines
                  "No phases were provided for ~x0.~%" line1-name)))
       (line1-nphases (len line1-phases))
       (line1-widened-phases
        (cond ((= line1-nphases number-of-phases)
               line1-phases)
              ((< line1-nphases number-of-phases)
               (b* ((repeat-me (car (last line1-phases))))
                 (or (not warn-non-blank)
                     (eq repeat-me '_)
                     (er hard? 'stv-widen-lines
                         "The line for ~x0 needs to be extended, but it ends ~
                          with ~x1.  We only allow output and internal lines ~
                          to be extended when they end with an underscore."
                         line1-name repeat-me))
                 (append line1-phases
                         (replicate (- number-of-phases line1-nphases) repeat-me))))
              (t
               (prog2$
                (er hard? 'stv-widen-lines
                    "Entry for ~x0 is longer than the max number of phases?" line1-name)
                (take number-of-phases line1-phases))))))
    (cons (cons line1-name line1-widened-phases)
          (stv-widen-lines (cdr lines) number-of-phases warn-non-blank))))

(define stv-widen ((stv stvdata-p))
  :returns (widened-stv stvdata-p :hyp :guard)
  :parents (symbolic-test-vectors)
  :short "Widen the input/output/internals lines so that they all agree on how
many phases there are."

  :long "<p>This is an STV preprocessing step which can be run before or after
@(see stv-expand).  We generally expect that all the lines have been widened
before any compilation is performed.</p>"

  (b* (((stvdata stv) stv)
       (number-of-phases (stv-number-of-phases stv))
       (new-inputs       (stv-widen-lines stv.inputs number-of-phases nil))
       (new-outputs      (stv-widen-lines stv.outputs number-of-phases t))
       (new-internals    (stv-widen-lines stv.internals number-of-phases t))
       (new-overrides    (stv-widen-lines stv.overrides number-of-phases t)))
    (change-stvdata stv
                    :inputs    new-inputs
                    :outputs   new-outputs
                    :internals new-internals
                    :overrides new-overrides)))
