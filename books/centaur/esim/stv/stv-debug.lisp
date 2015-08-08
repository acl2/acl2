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


; stv-debug.lisp -- waveform generation for STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-run")
(include-book "stv-sim")
(include-book "oslib/date" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "../esim-vcd")
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "system/f-put-global" :dir :system))

(local (defthm len-of-4v-sexpr-restrict-with-rw-alists
         (equal (len (4v-sexpr-restrict-with-rw-alists x al))
                (len x))))

(local (defthm true-list-listp-4v-sexpr-restrict-with-rw-alists
         (true-list-listp (4v-sexpr-restrict-with-rw-alists x al))))

(local (defthm cons-listp-4v-sexpr-restrict-with-rw-alist
         (cons-listp (4v-sexpr-restrict-with-rw-alist x al))))

(local (defthm cons-list-listp-of-4v-sexpr-restrict-with-rw-alists
         (cons-list-listp (4v-sexpr-restrict-with-rw-alists x al))))

(local (defthm cons-listp-4v-sexpr-eval-default-alist
         (cons-listp (4v-sexpr-eval-default-alist x al default))
         :hints(("Goal" :in-theory (e/d (4v-sexpr-eval-default-alist)
                                        (4v-sexpr-eval-default-when-4v-sexpr-eval-non-x))))))

(local (defthm cons-list-listp-of-4v-sexpr-eval-default-alists
         (cons-list-listp (4v-sexpr-eval-default-alists x al default))
         :hints(("Goal" :in-theory (e/d (4v-sexpr-eval-default-alists))))))

(local (defthm cons-listp-of-4v-sexpr-eval-alist
         (cons-listp (4v-sexpr-eval-alist x al))))

(local (defthm cons-list-listp-of-4v-sexpr-eval-alists
         (cons-list-listp (4v-sexpr-eval-alists x al))))

(define stv-combine-into-snapshots
  :parents (stv-debug)
  ((in-alists true-list-listp)
   (out-alists true-list-listp)
   (int-alists true-list-listp))
  :guard (and (same-lengthp in-alists out-alists)
              (same-lengthp in-alists int-alists))
  :returns (snapshots cons-list-listp
                      :hyp (and (cons-list-listp in-alists)
                                (cons-list-listp out-alists)
                                (cons-list-listp int-alists)))
  (b* (((when (atom in-alists))
        nil)
       (snapshot1 (append (car in-alists)
                          (car out-alists)
                          (car int-alists))))
    (cons snapshot1 (stv-combine-into-snapshots (cdr in-alists)
                                                (cdr out-alists)
                                                (cdr int-alists)))))

(define stv-make-snapshots
  :parents (stv-debug)
  :short "Prepare an STV for debugging by create \"snapshots\" that are ready
to be evaluated and written to the VCD file."
  ((pstv processed-stv-p)
   (mod))
  :returns (snapshots cons-list-listp)
  :long "<p>This is computationally expensive.  We memoize it so that we only
need to make the snapshots the first time you want to debug an STV.  The same
snapshots can then be reused across as many calls of @(see stv-debug) as you
like.</p>"

  (b* (((processed-stv pstv) pstv)
       ((compiled-stv cstv) pstv.compiled-stv)
       (nphases (nfix cstv.nphases))
       ((unless (posp nphases))
        (raise "STV has no phases?"))

       ((mv ?init-st-general
            in-alists-general
            ?nst-alists-general
            out-alists-general
            int-alists-general)
        (time$ (stv-fully-general-simulation-debug nphases mod cstv.override-bits)
               :msg "; stv debug simulation: ~st sec, ~sa bytes.~%"
               :mintime 1/2)))

    (with-fast-alist cstv.restrict-alist
      (time$ (stv-combine-into-snapshots
              (4v-sexpr-restrict-with-rw-alists in-alists-general cstv.restrict-alist)
              (4v-sexpr-restrict-with-rw-alists out-alists-general cstv.restrict-alist)
              (4v-sexpr-restrict-with-rw-alists int-alists-general cstv.restrict-alist))
             :msg "; stv-debug general snapshots: ~st sec, ~sa bytes.~%"
             :mintime 1/2)))
  ///
  (memoize 'stv-make-snapshots :aokp t))

(defttag writes-okp)
(remove-untouchable acl2::writes-okp nil)

; Added by Matt K., 9/28/2013, to get around ACL2(hp) error such as:
;   Error:  Not owner of hash table #<HASH-TABLE :TEST EQL size 95/135 #x30205C1CDBBD>
; David Rager points out (email, 9/28/2013) that "memoization is known
; not to be thread-safe"; Jared Davis says this too.  (Perhaps this will be
; addressed in the future.)
(local (unmemoize 'mod-state))
(local (unmemoize 'occmap))

(define stv-debug
  :parents (symbolic-test-vectors)
  :short "Evaluate a symbolic test vector at particular, concrete inputs, and
generate a waveform."
  ((pstv processed-stv-p)
   input-alist
   &key
   ((filename stringp) '"stv.debug")
   dontcare-ins
   (default-signal-val ''x)
   ((viewer   (or (stringp viewer) (not viewer))) '"gtkwave")
   (state    'state))
  :guard-debug t
  :returns (mv out-alist state)
  :long "<p>This macro is an extended version of @(see stv-run).  In addition
to building an alist of the output simulation variables, it also writes out a
waveform that can be viewed in a VCD viewer.  Note that debugging can be slow,
especially the first time before things are memoized.</p>"

  (time$
   (b* (((processed-stv pstv) pstv)
        ((compiled-stv cstv) pstv.compiled-stv)

        (mod-function (intern-in-package-of-symbol
                       (str::cat (symbol-name pstv.name) "-MOD")
                       pstv.name))
        ((mv er mod)
         (magic-ev-fncall mod-function
                          nil ;; args
                          state
                          t ;; hard error returns nil?  sure why not
                          t ;; attachments allowed? sure why not
                          ))

        ((when er)
         (mv (raise "Error evaluating ~x0 to look up STV module: ~@1."
                    mod-function (if (eq er 't) "t" er))
             state))
        ((unless (good-esim-modulep mod))
         (mv (raise "Error: ~x0 returned a bad ESIM module: ~@1"
                    mod-function (bad-esim-modulep mod))
             state))

        (snapshots
         (time$ (stv-make-snapshots pstv mod)
                :mintime 1/2
                :msg "; stv-debug snapshots: ~st sec, ~sa bytes.~%"))

        (in-usersyms
         ;; These should already be a fast alist, but in case the object was
         ;; serialized and reloaded or something, we'll go ahead and try to
         ;; make them fast again.
         (make-fast-alist cstv.in-usersyms))

        (ev-alist
         (time$ (append (stv-simvar-inputs-to-bits input-alist in-usersyms)
                        dontcare-ins)
                :mintime 1/2
                :msg "; stv-debug ev-alist: ~st sec, ~sa bytes.~%"))


        ((with-fast ev-alist))

        (evaled-out-bits
         (time$ (make-fast-alist
                 (4v-sexpr-eval-default-alist pstv.relevant-signals ev-alist default-signal-val))
                :mintime 1/2
                :msg "; stv-debug evaluating sexprs: ~st sec, ~sa bytes.~%"))

        (evaled-snapshots
         (time$ (4v-sexpr-eval-default-alists snapshots ev-alist default-signal-val)
                :mintime 1/2
                :msg "; stv-debug evaluating snapshots: ~st sec, ~sa bytes.~%"))

        (assembled-outs
         (time$ (stv-assemble-output-alist evaled-out-bits cstv.out-usersyms)
                :mintime 1/2
                :msg "; stv-debug assembling outs: ~st sec, ~sa bytes.~%"))

        (- (fast-alist-free evaled-out-bits))

        ;; Actual VCD generation
        ((mv date state) (oslib::date))
        (dump (vl2014::vcd-dump-main mod evaled-snapshots date))

        ((mv & & state) (assign acl2::writes-okp t))
        (state (time$ (vl2014::with-ps-file filename
                                        (vl2014::vl-ps-update-rchars dump))
                      :mintime 1/2
                      :msg "; vcd-dump file generation: ~st seconds, ~sa bytes.~%"))

        ;; Maybe launch a VCD viewer, but not if we're certifying books
        (certifying-book-p
         (and (acl2::boundp-global 'acl2::certify-book-info state)
              (acl2::f-get-global 'acl2::certify-book-info state)))

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
