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


; stv-debug.lisp -- waveform generation for STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-run")
(include-book "stv-sim")
(include-book "centaur/misc/date" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "../esim-vcd")
(local (include-book "centaur/vl/util/arithmetic" :dir :system))


(local (defthm len-of-4v-sexpr-restrict-with-rw-alists
         (equal (len (4v-sexpr-restrict-with-rw-alists x al))
                (len x))))

(local (defthm true-list-listp-4v-sexpr-restrict-with-rw-alists
         (true-list-listp (4v-sexpr-restrict-with-rw-alists x al))))

(local (defthm cons-listp-4v-sexpr-restrict-with-rw-alist
         (vl::cons-listp (4v-sexpr-restrict-with-rw-alist x al))))

(local (defthm cons-list-listp-of-4v-sexpr-restrict-with-rw-alists
         (vl::cons-list-listp (4v-sexpr-restrict-with-rw-alists x al))))



(defttag writes-okp)
(remove-untouchable acl2::writes-okp nil)

(defsection stv-make-snapshots

  (defund stv-combine-into-snapshots (in-alists out-alists int-alists)
    (declare (xargs :guard (and (vl::same-lengthp in-alists out-alists)
                                (vl::same-lengthp in-alists int-alists)
                                (true-list-listp in-alists)
                                (true-list-listp out-alists)
                                (true-list-listp int-alists))))
    (if (atom in-alists)
        nil
      (let ((snapshot1 (append (car in-alists)
                               (car out-alists)
                               (car int-alists))))
        (cons snapshot1 (stv-combine-into-snapshots (cdr in-alists)
                                                    (cdr out-alists)
                                                    (cdr int-alists))))))

  (local (defthm c0
           (implies (and (vl::cons-list-listp in-alists)
                         (vl::cons-list-listp out-alists)
                         (vl::cons-list-listp int-alists))
                    (vl::cons-list-listp
                     (stv-combine-into-snapshots in-alists out-alists int-alists)))
           :hints(("Goal" :in-theory (enable stv-combine-into-snapshots)))))

  (defund stv-make-snapshots (pstv)
    (declare (xargs :guard (processed-stv-p pstv)))
    (b* (((processed-stv pstv) pstv)

         ((compiled-stv cstv) pstv.compiled-stv)
         (nphases (nfix cstv.nphases))
         ((unless (posp nphases))
          (er hard? 'stv-process "STV has no phases?"))

         ((mv ?init-st-general
              in-alists-general
              ?nst-alists-general
              out-alists-general
              int-alists-general)
          (time$ (stv-fully-general-simulation-debug nphases pstv.mod)
                 :msg "; stv debug simulation: ~st sec, ~sa bytes.~%"
                 :mintime 1/2))

         (snapshots
          (with-fast-alist cstv.restrict-alist
            (time$ (stv-combine-into-snapshots
                    (4v-sexpr-restrict-with-rw-alists in-alists-general cstv.restrict-alist)
                    (4v-sexpr-restrict-with-rw-alists out-alists-general cstv.restrict-alist)
                    (4v-sexpr-restrict-with-rw-alists int-alists-general cstv.restrict-alist))
                   :msg "; stv-debug general snapshots: ~st sec, ~sa bytes.~%"
                   :mintime 1/2))))
      snapshots))

  (memoize 'stv-make-snapshots :aokp t)

  (defthm cons-list-listp-of-stv-make-snapshots
    (vl::cons-list-listp (stv-make-snapshots pstv))
    :hints(("Goal" :in-theory (e/d (stv-make-snapshots)
                                   ((force)))))))



(defsection stv-debug
  :parents (symbolic-test-vectors)
  :short "Evaluate a symbolic test vector at particular, concrete inputs, and
generate a waveform."

  :long "<p>This macro is an extended version of @(see stv-run).  In addition
to building an alist of the output simulation variables, it also writes out a
waveform that can be viewed in a VCD viewer.  Note that debugging can be slow,
especially the first time before things are memoized.</p>"

  (defun stv-debug-fn (pstv input-alist filename viewer state)
    "Returns (MV OUT-ALIST STATE)"
    (declare (xargs :guard (processed-stv-p pstv)
                    :stobjs state
                    :mode :program))
    (time$
     (b* (((processed-stv pstv) pstv)
          ((compiled-stv cstv) pstv.compiled-stv)

          (snapshots
           (time$ (stv-make-snapshots pstv)
                  :mintime 1/2
                  :msg "; stv-debug snapshots: ~st sec, ~sa bytes.~%"))

          (in-usersyms
           ;; These should already be a fast alist, but in case the object was
           ;; serialized and reloaded or something, we'll go ahead and try to
           ;; make them fast again.
           (make-fast-alist cstv.in-usersyms))

          (ev-alist
           (time$ (make-fast-alist
                   (stv-simvar-inputs-to-bits input-alist in-usersyms))
                  :mintime 1/2
                  :msg "; stv-debug ev-alist: ~st sec, ~sa bytes.~%"))

          (evaled-out-bits
           (time$ (make-fast-alist
                   (4v-sexpr-eval-alist pstv.relevant-signals ev-alist))
                  :mintime 1/2
                  :msg "; stv-debug evaluating sexprs: ~st sec, ~sa bytes.~%"))

          (evaled-snapshots
           (time$ (4v-sexpr-eval-alists snapshots ev-alist)
                  :mintime 1/2
                  :msg "; stv-debug evaluating snapshots: ~st sec, ~sa bytes.~%"))

          (- (fast-alist-free ev-alist))

          (assembled-outs
           (time$ (stv-assemble-output-alist evaled-out-bits cstv.out-usersyms)
                  :mintime 1/2
                  :msg "; stv-debug assembling outs: ~st sec, ~sa bytes.~%"))

          (- (fast-alist-free evaled-out-bits))

          ;; Actual VCD generation
          ((mv date state) (acl2::date state))
          (dump (vl::vcd-dump-main pstv.mod evaled-snapshots date))

          ((mv & & state) (assign acl2::writes-okp t))
          (state (time$ (vl::with-ps-file filename
                           (vl::vl-ps-update-rchars dump))
                        :mintime 1/2
                        :msg "; vcd-dump file generation: ~st seconds, ~sa bytes.~%"))

          ;; Maybe launch a VCD viewer, but not if we're certifying books
          (certifying-book-p (acl2::f-get-global 'acl2::certify-book-info state))

          ;; BOZO we aren't really escaping filenames right or anything like that
          (- (if (and viewer (not certifying-book-p))
                 (b* ((cmd (str::cat viewer " " filename)))
                   (cw "; vcd-dump launching \"~s0\".~%" cmd)
                   (acl2::tshell-ensure)
                   (acl2::tshell-run-background cmd))
               nil)))

       (mv assembled-outs state))
     :msg "; stv-debug: ~st sec, ~sa bytes.~%"
     :mintime 1))

  (defmacro stv-debug (pstv input-alist
                            &key
                            (filename '"stv.debug")
                            (viewer   '"gtkwave"))
    `(stv-debug-fn ,pstv ,input-alist ,filename ,viewer state)))

