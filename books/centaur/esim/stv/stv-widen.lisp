; ESIM Symbolic Hardware Simulator
; Copyright (C) 2010-2012 Centaur Technology
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


; stv-widen.lisp -- widening of STV input and output lines
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "std/lists/repeat" :dir :system)
(local (include-book "std/lists/take" :dir :system))

(defsection stv-widen-lines
  :parents (stv-widen)
  :short "@(call stv-widen-lines) rewrites lines of an STV, repeating the last
entry in each line until the desired number of phases is reached."

  :long "<p>The @('warn-non-blank') is intended to be set for :output lines
and :internals lines.  When it is set, we cause an error if an attempt is made
to replicate any element other than @('_'), since it doesn't make sense to
replicate simulation variables.</p>"

  (defund stv-widen-lines (lines number-of-phases warn-non-blank)
    (declare (xargs :guard (and (true-list-listp lines)
                                (natp number-of-phases))))
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
                           (repeat repeat-me (- number-of-phases line1-nphases)))))
                (t
                 (prog2$
                  (er hard? 'stv-widen-lines
                      "Entry for ~x0 is longer than the max number of phases?" line1-name)
                  (take number-of-phases line1-phases))))))
      (cons (cons line1-name line1-widened-phases)
            (stv-widen-lines (cdr lines) number-of-phases warn-non-blank))))

  (local (in-theory (enable stv-widen-lines)))

  (defthm true-list-listp-of-stv-widen-lines
    (implies (true-list-listp lines)
             (true-list-listp (stv-widen-lines lines number-of-phases warn-non-blank)))))


(defsection stv-widen
  :parents (symbolic-test-vectors)
  :short "Widen the input/output/internals lines so that they all agree on how
many phases there are."
  :long "<p><b>Signature:</b> @(call stv-widen) returns a new @(see stvdata-p).</p>

<p>This is an STV preprocessing step which can be run before or after @(see
stv-expand).  We generally expect that all the lines have been widened before
any compilation is performed.</p>

<p>Note that we don't widen @(':initial') lines; they have only one value, not
a series of values over time.</p>"

  (defund stv-widen (stv)
    (declare (xargs :guard (stvdata-p stv)))
    (b* (((stvdata stv) stv)
         (number-of-phases  (stv-number-of-phases stv)))
      (change-stvdata stv
                      :inputs    (stv-widen-lines stv.inputs number-of-phases nil)
                      :outputs   (stv-widen-lines stv.outputs number-of-phases t)
                      :internals (stv-widen-lines stv.internals number-of-phases t))))

  (local (in-theory (enable stv-widen)))

  (defthm stvdata-p-of-stv-widen
    (implies (stvdata-p stv)
             (stvdata-p (stv-widen stv)))))

