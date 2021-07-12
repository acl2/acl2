; AIGNET - And-Inverter Graph Networks
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")

(include-book "aiger")
(include-book "centaur/misc/tshell" :dir :system)
(include-book "std/strings/defs" :dir :system) ; previously came in via tshell
(local (include-book "std/strings/decimal" :dir :system))
(defttag aignet-abc)

(defxdoc aignet-abc-interface
  :parents (aignet)
  :short "Using the open-source synthesis and equivalence/model-checking tool ABC with aignet")

(local (in-theory (disable w)))

(define read-ctrex-skip-regs ((regs natp)
                              (channel symbolp)
                              state)
  :guard (open-input-channel-p channel :byte state)
  :returns (mv err new-state)
  (if (zp regs)
      (mv nil state)
    (b* (((mv byte state) (read-byte$ channel state))
         ((when (not byte))
          (mv "Premature EOF in counterexample file while skipping regs"
              state)))
      (read-ctrex-skip-regs (1- regs) channel state)))
  ///
  (std::defret read-ctrex-skip-regs-frame-preserves-open-input-channel-p1
    (implies (and (symbolp channel)
                  (open-input-channel-p1 channel :byte state)
                  (state-p1 state))
             (and (open-input-channel-p1 channel :byte new-state)
                  (state-p1 new-state))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(define read-ctrex-into-frames-frame ((framenum natp)
                                      (innum natp)
                                      frames
                                      (channel symbolp)
                                      state)
  :guard (and (open-input-channel-p channel :byte state)
              (< framenum (frames-nrows frames))
              (<= innum (frames-ncols frames)))
  :measure (nfix (- (frames-ncols frames) (nfix innum)))
  :returns (mv err new-frames new-state)
  (B* (((when (mbe :logic (zp (- (frames-ncols frames) (nfix innum)))
                   :exec (eql (frames-ncols frames) innum)))
        (mv nil frames state))
       ((mv byte state) (read-byte$ channel state))
       ((mv err val)
        (cond ((eq byte nil)
                 (mv "Premature EOF while reading input values"
                     nil))
                ((eql (char-code #\0) byte) (mv nil 0))
                ((eql (char-code #\1) byte) (mv nil 1))
                (t (mv (msg "Nonsense byte read: ~x0~%" (code-char byte))
                       nil))))
       ((when err) (mv err frames state))
       (frames (frames-set2 framenum innum val frames)))
    (read-ctrex-into-frames-frame framenum (1+ (lnfix innum)) frames channel state))
  ///
  (std::defret nrows-of-read-ctrex-into-frames-frame
    (<= (len (stobjs::2darr->rows frames)) (len (stobjs::2darr->rows new-frames)))
    :rule-classes :linear)

  (std::defret nrows-of-read-ctrex-into-frames-frame-strong
    (implies (< (nfix framenum) (len (stobjs::2darr->rows frames)))
             (equal (len (stobjs::2darr->rows new-frames))
                    (len (stobjs::2darr->rows frames)))))

  (std::defret ncols-of-read-ctrex-into-frames-frame
    (equal (stobjs::2darr->ncols new-frames)
           (stobjs::2darr->ncols frames)))

  (std::defret read-ctrex-into-frames-frame-preserves-open-input-channel-p1
    (implies (and (symbolp channel)
                  (open-input-channel-p1 channel :byte state)
                  (state-p1 state))
             (and (open-input-channel-p1 channel :byte new-state)
                  (state-p1 new-state))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(define read-ctrex-into-frames-frames ((framenum natp)
                           frames
                           (channel symbolp)
                           state)
  :guard (and (open-input-channel-p channel :byte state)
              (<= framenum (frames-nrows frames)))
  :measure (nfix (- (frames-nrows frames) (nfix framenum)))
  :returns (mv err new-frames new-state)
  (b* (((when (mbe :logic (zp (- (frames-nrows frames) (nfix framenum)))
                   :exec (eql (frames-nrows frames) framenum)))
        (mv nil frames state))
       ((mv err frames state) (read-ctrex-into-frames-frame
                              framenum 0 frames channel state))
       ((when err) (mv err frames state)))
    (read-ctrex-into-frames-frames (1+ (lnfix framenum)) frames channel state))
  ///

  (std::defret nrows-of-read-ctrex-into-frames-frames
    (equal (len (stobjs::2darr->rows new-frames))
           (len (stobjs::2darr->rows frames))))

  (std::defret ncols-of-read-ctrex-into-frames-frames
    (equal (stobjs::2darr->ncols new-frames)
           (stobjs::2darr->ncols frames)))

  (std::defret read-ctrex-into-frames-frames-preserves-open-input-channel-p1
    (implies (and (symbolp channel)
                  (open-input-channel-p1 channel :byte state)
                  (state-p1 state))
             (and (open-input-channel-p1 channel :byte new-state)
                  (state-p1 new-state))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))




(define read-ctrex-into-frames ((fname stringp)
                                (num-regs natp)
                                frames
                                state)
  :returns (mv err new-frames new-state)
  (b* ((fname (mbe :logic (str::str-fix fname) :exec fname))
       ((mv channel state) (open-input-channel fname :byte state))
       ((unless channel)
        (mv "Aignet-run-abc: Failed to read the counterexample file." frames state))
       ((mv err state) (read-ctrex-skip-regs num-regs channel state))
       ((when err)
        (b* ((state (close-input-channel channel state)))
          (mv (msg "Aignet-run-abc: error while skipping initial registers in counterexample: ~@0" err)
              frames state)))
       ((mv err frames state)
        (read-ctrex-into-frames-frames 0 frames channel state))
       (state (close-input-channel channel state)))
    (mv (and err
             (msg "Aignet-run-abc: error reading counterexample: ~@0" err))
        frames state))
  ///
  (std::defret nrows-of-read-ctrex-into-frames
    (equal (len (stobjs::2darr->rows new-frames))
           (len (stobjs::2darr->rows frames))))

  (std::defret ncols-of-read-ctrex-into-frames
    (equal (stobjs::2darr->ncols new-frames)
           (stobjs::2darr->ncols frames)))

  (std::defret read-ctrex-into-frames-preserves-state-p1
    (implies (state-p1 state)
             (state-p1 new-state)))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(local (include-book "std/lists/nthcdr" :dir :system))


(define find-non-space ((str stringp)
                        (pos natp)
                        (len (equal len (length str))))
  :guard (<= pos len)
  :measure (nfix (- (length str) (nfix pos)))
  :returns (nonspace-pos (or (natp nonspace-pos)
                             (equal nonspace-pos nil))
                         :rule-classes :type-prescription)
  (b* ((len (mbe :logic (length str) :exec len))
       (pos (lnfix pos))
       ((when (mbe :logic (zp (- len (nfix pos)))
                   :exec (eql len pos)))
        nil)
       ((unless (eql (char str pos) #\Space))
        pos))
    (find-non-space str (1+ pos) len))
  ///
  (std::defret find-non-space-less-than-length
    (implies nonspace-pos
             (< nonspace-pos (length str)))
    :rule-classes :linear))




;; takes:
;; str -- the string to read from
;; pos -- the position to start at
;; prompts -- the text to search for previous to each number
(define read-ctrex-entries ((str stringp "line from the output")
                            (pos natp "position in the line")
                            (prompts string-listp "prompts to look for in order")
                            (strlen (equal strlen (length str))))
  :guard (<= pos strlen)
  :measure (len prompts)
  :hints(("Goal" :in-theory (enable len)))
  :prepwork ((local (defthm listpos-plus-pos-nthcdr
                      (implies (and (acl2::sublistp x (nthcdr pos y))
                                    (natp pos)
                                    (< pos (len y)))
                               (<= (+ pos (len x) (acl2::listpos x (nthcdr pos y)))
                                   (len y)))
                      :hints (("goal" :use ((:instance ACL2::LISTPOS-UPPER-BOUND-STRONG-2
                                             (y (nthcdr pos y))))
                               :in-theory (disable ACL2::LISTPOS-UPPER-BOUND-STRONG-2)
                               :do-not-induct t))
                      :rule-classes :linear))
             (local (in-theory (e/d ()
                                    (acl2::sublistp-when-prefixp
                                     acl2::consp-of-nthcdr
                                     acl2::nthcdr-when-zp
                                     nthcdr nth len
                                     acl2::sublistp-when-prefixp
                                     acl2::len-when-prefixp
                                     ACL2::NFIX-WHEN-NOT-NATP)))))
  :returns (mv ok
               (entries nat-listp
                        :hints(("Goal" :in-theory (e/d (nat-listp)
                                                       ((:d read-ctrex-entries)))
                                :induct (read-ctrex-entries str pos prompts strlen)
                                :expand ((read-ctrex-entries str pos prompts strlen))))))
  (if (atom prompts)
      (mv t nil)
    (b* ((str (mbe :logic (str::str-fix str) :exec str))
         (prompt (mbe :logic (str::str-fix (car prompts)) :exec (car prompts)))
         (prompt-length (length prompt))
         (strlen (mbe :logic (length str) :exec strlen))
         (pos (lnfix pos))
         ((unless (mbt (<= pos strlen)))
          (mv nil nil))
         (loc (str::strpos-fast prompt str pos prompt-length strlen))
         ((unless loc)
          (mv nil nil))
         (numloc (find-non-space str (+ loc prompt-length) strlen))
         ((unless numloc)
          (mv nil nil))
         ((mv num numend)
          (str::parse-nat-from-string str 0 0 numloc strlen))
         ((when (= numloc numend))
          (mv nil nil))
         ((mv ok rest)
          (read-ctrex-entries str numend (cdr prompts) strlen))
         ((unless ok)
          (mv nil nil)))
      (mv t (cons num rest))))
  ///
  (std::defret len-of-read-ctrex-entries
    (implies ok
             (equal (len entries) (len prompts)))
    :hints(("Goal" :in-theory (e/d (len)
                                   ((:d read-ctrex-entries)))
            :induct (read-ctrex-entries str pos prompts strlen)
            :expand ((read-ctrex-entries str pos prompts strlen))))))





(define find-ctrex-line ((strings string-listp))
  :prepwork ((local (in-theory (disable ACL2::PREFIXP-OF-CONS-LEFT))))
  :returns (mv (type ":comb, :seq, or error message")
               (nums nat-listp
                     "list of numbers read from the line: for :comb, just number
                      of PIs; for :seq, number of PIs, number of regs, PO number
                      that was contradicted, frame number on which the counterexample
                      occurred, and total number of bits."))
  (b* (((when (atom strings)) (mv nil nil))
       (str (car strings))
       (pos (str::strpos "CEX:" str))
       ((unless pos)
        (find-ctrex-line (cdr strings)))
       (seq-prompts '("Po = "
                      "Frame = "
                      "FF = "
                      "PI = "
                      "Bit = "))
       ((mv ok nums) (read-ctrex-entries str pos seq-prompts (length str)))
       ((when ok) (mv :seq nums))
       (comb-prompts '("Po = " "PI = "))
       ((mv ok nums) (read-ctrex-entries str pos comb-prompts (length str)))
       ((unless ok)
        (mv (msg "Bad counterexample line: ~s0" str) nil)))
    (mv :comb nums))
  ///
  (std::defret len-of-find-ctrex-line
    (equal (len nums)
           (case type
             (:comb 2)
             (:seq 5)
             (otherwise 0)))))

(define find-status-line ((strings string-listp))
  :returns (status symbolp ":refuted, :proved, :failed, or nil")
  :prepwork ((local (in-theory (e/d (list-equiv)
                                    (ACL2::PREFIXP-OF-CONS-LEFT)))))
  :guard-debug t
  (b* (((when (atom strings)) nil)
       (str (car strings))
       ((when (not (str::strprefixp "Status = " str)))
        (find-status-line (cdr strings)))
       (lst (coerce str 'list))
       (past-status (nthcdr (length "Status = ") lst))
       (negative (eql (car past-status) #\-))
       (past-status (if negative (Cdr past-status) past-status))
       (status-code
        (* (if negative -1 1)
           (str::dec-digit-chars-value
            (str::take-leading-dec-digit-chars past-status))))
       (status (case status-code
                 (0 :refuted)
                 (1 :proved)
                 (otherwise :failed))))
    status))

(define abc-output-status-and-trace ((output-lines string-listp)
                                     (ctrex-filename acl2::maybe-stringp)
                                     force-status
                                     (num-ins natp)
                                     frames
                                     state)
  :returns (mv status/err new-frames new-state)
  :guard-hints (("goal" :do-not-induct t))

  :prepwork ((local (defthm natp-nth-of-nat-listp
                      (implies (and (nat-listp x)
                                    (< (nfix n) (len x)))
                               (and (natp (nth n x))
                                    (acl2-numberp (nth n x))))))
             (local (defthm natp-+-1
                      (implies (natp x) (natp (+ 1 x)))))
             (local (defthm true-listp-when-string-listp
                      (implies (string-listp x)
                               (true-listp x))
                      :rule-classes :forward-chaining))
             (local (defthm string-listp-of-rev
                      (implies (string-listp x)
                               (string-listp (acl2::rev x)))
                      :hints(("Goal" :in-theory (enable acl2::rev))))))
  (b* ((revlines (reverse (mbe :logic (acl2::list-fix output-lines) :exec output-lines)))
       (status (find-status-line revlines))
       ((unless status)
        (mv (if force-status
                "Aignet-run-abc: No proof status was found in the output."
              nil)
            frames state))
       ((unless (and (eq status :refuted) ctrex-filename))
        (mv status frames state))
       ((mv ctrex-type ctrex-stats) (find-ctrex-line revlines))
       ((unless (or (eq ctrex-type :comb)
                    (eq ctrex-type :seq)))
        ;; error
        (mv (msg "Aignet-run-abc: Error parsing counterexample status line: ~@0" ctrex-type)
            frames state))
       (ctrex-num-ins (if (eq ctrex-type :comb)
                          (nth 1 ctrex-stats)
                        (nth 3 ctrex-stats)))
       ((unless (eql (lnfix num-ins) ctrex-num-ins))
        (mv (msg "Aignet-run-abc: Error -- counterexample claims there are ~x0 inputs but we have ~x1."
                 ctrex-num-ins (lnfix num-ins))
            frames state))
       ((mv regs nframes)
        (if (eq ctrex-type :comb)
            (mv 0 0)
          (mv (nth 2 ctrex-stats) (nth 1 ctrex-stats))))

       (frames (frames-resize-rows 0 frames))
       (frames (frames-resize-cols num-ins frames))
       (frames (frames-resize-rows (+ 1 nframes) frames))
       ((mv err frames state)
        (read-ctrex-into-frames ctrex-filename regs frames state))
       ((when err)
        (mv (msg "Aignet-run-abc: Error reading counterexample file: ~@0" err)
            frames state)))
    (mv status frames state))
  ///
  (std::defret frames-ncols-of-abc-output-status-and-trace-when-refuted
    (implies (and (equal status/err :refuted)
                  ctrex-filename)
             (equal (stobjs::2darr->ncols new-frames) (nfix num-ins))))

  (std::defret abc-output-status-and-trace-preserves-state-p1
    (implies (state-p1 state)
             (state-p1 new-state)))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(acl2::defstobj-clone input-aignet aignet :prefix "INPUT-")
(acl2::defstobj-clone output-aignet aignet :prefix "OUTPUT-")

(defthm w-state-of-princ$
  (equal (w (princ$ obj channel state))
         (w state))
  :hints(("Goal" :in-theory (enable w princ$ get-global))))

(define aignet-run-abc-core-st ((input-aignet "input AIG")
                                (output-aignet "output AIG")
                                (frames "output ctrex")
                                (script stringp "Commands for ABC to run, including reading
                                         the input aiger file and writing the output,
                                         if desired.")
                                &key
                                (script-filename stringp)
                                (input-filename stringp)
                                (output-filename
                                 acl2::maybe-stringp
                                 "If set, implies that the script writes a new aignet to this file")
                                (ctrex-filename
                                 acl2::maybe-stringp
                                 "If set, implies that the script may dump a counterexample in this file.")
                                ((force-status
                                  "If set to true, causes an error if no proof status line
                           is present in the output.")  'nil)
                                ((quiet "Don't print the output from ABC") 'nil)
                                (state 'state))
  :returns (mv (status "Either :refuted, :proved, :failed, NIL, or an error message. NIL implies
                        that there was no error detected but also no proof status
                        line, implying that maybe no proof was attempted.")
               new-output-aignet
               new-frames
               new-state)
  :parents (aignet-abc-interface)
  :short "Run abc on an aignet; takes and returns state."
  :long "<p>See @(see aignet-run-abc-core), which is identical except that it
hides the usage of state.</p>"
  (b* ((output-aignet (aignet-clear output-aignet))
       (input-filename (mbe :logic (acl2::str-fix input-filename) :exec input-filename))
       (script-filename (mbe :logic (acl2::str-fix script-filename) :exec script-filename))
       (state (aignet-write-aiger input-filename input-aignet state))
       ((mv channel state) (open-output-channel! script-filename :character state))
       ((unless channel)
        (mv "Aignet-run-abc: Failed to write the ABC script." output-aignet frames state))
       (state (princ$ script channel state))
       (state (close-output-channel channel state))
       ((mv exit-status lines) (acl2::tshell-call
                                (str::cat (if quiet "abc -f " "abc -F ") script-filename)
                                :print (not quiet) :save t))
       ((unless (equal exit-status 0))
        (mv (msg "Aignet-run-abc: abc failed with exit status ~x0" exit-status)
            output-aignet frames state))
       ((mv read-err output-aignet state)
        (if output-filename
            (aignet-read-aiger
             (mbe :logic (acl2::str-fix output-filename) :exec output-filename)
             output-aignet state)
          (mv nil output-aignet state)))
       ((when read-err)
        (mv (msg "Aignet-run-abc: failed to read result AIG: ~s0" read-err)
            output-aignet frames state))
       ((mv status frames state)
        (abc-output-status-and-trace lines ctrex-filename force-status
                                     (num-ins input-aignet) frames state)))
    (mv status output-aignet frames state))
  ///
  (std::defret frames-ncols-of-aignet-run-abc-core-st-when-refuted
    (implies (and (equal status :refuted)
                  ctrex-filename)
             (equal (stobjs::2darr->ncols new-frames) (num-ins input-aignet))))

  (std::defret aignet-run-abc-core-st-preserves-state-p1
    (implies (state-p1 state)
             (state-p1 new-state)))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(remove-untouchable acl2::create-state t)

(define aignet-run-abc-core ((input-aignet "input AIG")
                             (output-aignet "output AIG")
                             (frames "output ctrex")
                             (script stringp "Commands for ABC to run, including reading
                                         the input aiger file and writing the output,
                                         if desired.")
                             &key
                             (script-filename stringp)
                             (input-filename stringp)
                             (output-filename
                              acl2::maybe-stringp
                              "If set, implies that the script writes a new aignet to this file")
                             (ctrex-filename
                              acl2::maybe-stringp
                              "If set, implies that the script may dump a counterexample in this file.")
                             ((force-status
                               "If set to true, causes an error if no proof status
                                line is present in the output.")  'nil)
                             ((quiet "Don't print the output from ABC") 'nil))
  :returns (mv (status "Either :refuted, :proved, :failed, NIL, or an error message. NIL implies
                        that there was no error detected but also no proof status
                        line, implying that maybe no proof was attempted.")
               new-output-aignet
               new-frames)
  :parents (aignet-abc-interface)
  :short "Run abc on an aignet, without using state"
  :long "<p>This function dumps the input aignet into a specified aiger file
given as @(':input-filename'), writes the given script into
@('script-filename'), then runs abc with that script. If the
@('output-filename') option is given, then when abc finishes it attempts to
read a new aignet from that file, which overwrites @('output-aignet').  If the
@('ctrex-filename') option is given and ABC outputs a status line indicating
that it has a counterexample, then this function reads the counterexample from
that file, which overwrites @('frames').</p>

<p>This function does not make any modifications to the given ABC script and
does not attempt to ensure that it makes sense.  For example, if
@('ctrex-filename') is given, then the script should likely contain:</p>
@({
  print_status
  write_ctrex ctrex-filename
})
<p>If @('output-filename') is given, then the script should contain a command
that writes out the final network to that file, such as:</p>
@({
  &w output-filename
})

<p>This function is not axiomatized in any way, because it could be used for at
least four different applications, which would make sense to axiomatize
differently:</p>

<ul>
<li>combinational simplification</li>
<li>combinational (equivalence, satisfiability) checking</li>
<li>sequential simplification</li>
<li>sequential (equivalence, model) checking.</li>
</ul>

<p>See @(see abc-example-scripts) for some scripts that do these things.</p>"
  (with-local-state
    (mv-let (status output-aignet frames state)
      (aignet-run-abc-core-st input-aignet output-aignet frames script
                              :script-filename script-filename
                              :input-filename input-filename
                              :output-filename output-filename
                              :ctrex-filename ctrex-filename
                              :force-status force-status
                              :quiet quiet)
      (mv status output-aignet frames)))
  ///
  (std::defret frames-ncols-of-aignet-run-abc-core-logic-when-refuted
    (implies (and (equal status :refuted)
                  ctrex-filename)
             (equal (stobjs::2darr->ncols new-frames) (num-ins input-aignet)))))

(push-untouchable acl2::create-state t)


(defun aignet-abc-useless-clauseproc (clause)
  (list clause))

(defmacro aignet-abc (input-aignet
                      output-aignet
                      frames
                      script
                      &key
                      script-filename
                      input-filename
                      output-filename
                      ctrex-filename
                      force-status
                      quiet
                      axiom)
  `(aignet-abc-fn ,input-aignet
                  ,output-aignet
                  ,frames
                  ,script
                  ,script-filename
                  ,input-filename
                  ,output-filename
                  ,ctrex-filename
                  ,force-status
                  ,quiet
                  ,axiom))

(define-trusted-clause-processor
  aignet-abc-useless-clauseproc
  (aignet-abc-fn)
  :partial-theory
  (encapsulate
    (((aignet-abc-fn input-aignet output-aignet frames * * * * * * * *)
      => (mv * output-aignet frames)
      :formals (input-aignet
                output-aignet
                frames
                script
                script-filename
                input-filename
                output-filename
                ctrex-filename
                force-status
                quiet
                axiom)
      :guard (and (stringp script)
                  (stringp script-filename)
                  (stringp input-filename)
                  (acl2::maybe-stringp output-filename)
                  (acl2::maybe-stringp ctrex-filename))))

    (local (defun aignet-abc-fn (input-aignet
                                 output-aignet
                                 frames
                                 script
                                 script-filename
                                 input-filename
                                 output-filename
                                 ctrex-filename
                                 force-status
                                 quiet
                                 axiom)
             (declare (xargs :stobjs (input-aignet output-aignet frames)
                             :guard (and (stringp script)
                                         (stringp script-filename)
                                         (stringp input-filename)
                                         (acl2::maybe-stringp output-filename)
                                         (acl2::maybe-stringp ctrex-filename)))

                      (ignore input-aignet
                              script
                              script-filename
                              input-filename
                              output-filename
                              ctrex-filename
                              force-status
                              quiet
                              axiom))
             (b* ((output-aignet (aignet-clear output-aignet)))
               (mv "error" output-aignet frames))))

    (local (in-theory '((equal) (member-equal) aignet-abc-fn)))

    (defthm output-aignet-irrelevevant-of-aignet-abc
      (implies (syntaxp (not (equal output-aignet ''nil)))
               (equal (aignet-abc input-aignet
                                  output-aignet
                                  frames
                                  script
                                  :script-filename script-filename
                                  :input-filename input-filename
                                  :output-filename output-filename
                                  :ctrex-filename ctrex-filename
                                  :force-status force-status
                                  :quiet quiet
                                  :axiom axiom)
                      (aignet-abc input-aignet
                                  nil
                                  frames
                                  script
                                  :script-filename script-filename
                                  :input-filename input-filename
                                  :output-filename output-filename
                                  :ctrex-filename ctrex-filename
                                  :force-status force-status
                                  :quiet quiet
                                  :axiom axiom))))

    (defthm aignet-abc-comb-prove-correct
      (b* (((mv status ?output-aignet ?frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom :comb-prove)))
        (implies (equal status :proved)
                 (and (implies (< (nfix n) (num-outs input-aignet))
                               (equal (lit-eval (fanin 0 (lookup-stype n (po-stype) input-aignet))
                                               invals regvals input-aignet)
                                      0))
                      (implies (< (nfix n) (num-regs input-aignet))
                               (equal (lit-eval (lookup-reg->nxst n input-aignet)
                                                invals regvals input-aignet)
                                      0))))))

    (defthm aignet-abc-comb-simp-correct
      (b* (((mv status output-aignet ?frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom :comb-simp)))
        (implies (and (not (stringp status)) ;; not error msg
                      output-filename)
                 (and (comb-equiv output-aignet input-aignet)
                      (equal (stype-count :reg output-aignet)
                             (stype-count :reg input-aignet))
                      (equal (stype-count :pi output-aignet)
                             (stype-count :pi input-aignet))
                      (equal (stype-count :po output-aignet)
                             (stype-count :po input-aignet))
                      (equal (stype-count :nxst output-aignet)
                             (stype-count :reg input-aignet))))))

    (defthm aignet-abc-comb-prove-simp-correct
      (b* (((mv status output-aignet ?frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom :comb-prove-simp)))
        (and (implies (equal status :proved)
                      (and (implies (< (nfix n) (num-outs input-aignet))
                                    (equal (lit-eval (fanin 0 (lookup-stype n (po-stype) input-aignet))
                                                    invals regvals input-aignet)
                                           0))
                           (implies (< (nfix n) (num-regs input-aignet))
                                    (equal (lit-eval (lookup-reg->nxst n input-aignet)
                                                    invals regvals input-aignet)
                                           0))))
             (implies (and (not (stringp status)) ;; not error msg
                           output-filename)
                      (and (comb-equiv output-aignet input-aignet)
                           (equal (stype-count :reg output-aignet)
                                  (stype-count :reg input-aignet))
                           (equal (stype-count :pi output-aignet)
                                  (stype-count :pi input-aignet))
                           (equal (stype-count :po output-aignet)
                                  (stype-count :po input-aignet))
                           (equal (stype-count :nxst output-aignet)
                                  (stype-count :reg input-aignet)))))))

    (defthm aignet-abc-seq-prove-correct
      (b* (((mv status ?output-aignet ?frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom :seq-prove)))
        (implies (and (equal status :proved)
                      (< (nfix n) (num-outs input-aignet)))
                 (equal (lit-eval-seq k (fanin 0 (lookup-stype n (po-stype) input-aignet))
                                     inframes nil input-aignet)
                        0))))

    (defthm aignet-abc-seq-simp-correct
      (b* (((mv status output-aignet ?frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom :seq-simp)))
        (implies (and (not (stringp status)) ;; not error msg
                      output-filename)
                 (and (seq-equiv output-aignet input-aignet)
                      (equal (stype-count :pi output-aignet)
                             (stype-count :pi input-aignet))
                      (equal (stype-count :po output-aignet)
                             (stype-count :po input-aignet))))))


    (defthm aignet-abc-seq-prove-simp-correct
      (b* (((mv status output-aignet ?frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom :seq-prove-simp)))
        (and (implies (and (equal status :proved)
                           (< (nfix n) (num-outs input-aignet)))
                      (equal (lit-eval-seq k (fanin 0 (lookup-stype n (po-stype) input-aignet))
                                          inframes nil input-aignet)
                             0))
             (implies (and (not (stringp status)) ;; not error msg
                           output-filename)
                      (and (seq-equiv output-aignet input-aignet)
                           (equal (stype-count :pi output-aignet)
                                  (stype-count :pi input-aignet))
                           (equal (stype-count :po output-aignet)
                                  (stype-count :po input-aignet)))))))

    (defthm aignet-abc-frames-ncols-correct
      (b* (((mv status ?output-aignet frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom axiom)))
        (implies (and (equal status :refuted)
                      ctrex-filename)
                 (equal (stobjs::2darr->ncols frames) (num-ins input-aignet)))))

    (defthm aignet-abc-status
      (b* (((mv status ?output-aignet ?frames)
            (aignet-abc input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet
                        :axiom axiom)))
        (or (equal status :proved)
            (equal status :refuted)
            (equal status :failed)
            (equal status nil)
            (stringp status)))
      :rule-classes ((:forward-chaining
                      :trigger-terms ((mv-nth 0 (aignet-abc input-aignet
                                                            output-aignet
                                                            frames
                                                            script
                                                            :script-filename script-filename
                                                            :input-filename input-filename
                                                            :output-filename output-filename
                                                            :ctrex-filename ctrex-filename
                                                            :force-status force-status
                                                            :quiet quiet
                                                            :axiom axiom))))))))

(progn!
 (set-raw-mode t)
 (defun aignet-abc-fn (input-aignet
                       output-aignet
                       frames
                       script
                       script-filename
                       input-filename
                       output-filename
                       ctrex-filename
                       force-status
                       quiet
                       axiom)
   (declare (ignore axiom))
   (aignet-run-abc-core input-aignet
                        output-aignet
                        frames
                        script
                        :script-filename script-filename
                        :input-filename input-filename
                        :output-filename output-filename
                        :ctrex-filename ctrex-filename
                        :force-status force-status
                        :quiet quiet)))




(defxdoc aignet-abc
  :parents (aignet-abc-interface)
  :short "Run abc on an aignet, with a few different possible axioms about what comes out."
  :long "<p>This function is identical to @(see aignet-run-abc-core), but takes
one additional keyword argument, @('axiom').  This argument specifies what can
be assumed about the results.  The soundness of this assumption is highly
questionable and dependent on the soundness of ABC and the appropriateness of
the script it is run with.  The axiom may be any of the following; if it is
anything else or is not specified, then nothing particular is assumed.</p>

<ul>

<li>@(':comb-prove'): Asserts that if we produce @(':proved') as the status, it
implies that all outputs and register nextstates of the input AIG are
combinationally constant-true; that is, for any setting of the inputs and
register states.</li>

<li>@(':comb-simp') Asserts that if we produce a non-error status (one of
@(':proved'), @(':refuted'), @(':failed'), or @('nil')), and the output
filename was given, that the output aignet is combinationally equivalent to the
input aignet (see @(see comb-equiv)).</li>

<li>@(':comb-prove-simp') combines the assertions of @(':comb-prove') and
@(':comb-simp').</li>

<li>@(':seq-prove'): Asserts that if we produce @(':proved') as the status, it
implies that all outputs of the input AIG are sequentially constant-true
starting from the all-0 initial state.</li>

<li>@(':seq-simp') Asserts that if we produce a non-error status (one of
@(':proved'), @(':refuted'), @(':failed'), or @('nil')), and the output
filename was given, that the output aignet is sequentially equivalent to the
input aignet (see @(see seq-equiv)).</li>

<li>@(':seq-prove-simp') combines the assertions of @(':seq-prove') and
@(':seq-simp').</li>

</ul>

<p>See @(see abc-example-scripts) for example scripts that may be appropriate
for these various assumptions, modulo the correctness of ABC.</p>")


(defxdoc abc-example-scripts
  :parents (aignet-abc-interface)
  :short "Example scripts to use with @(see aignet-abc)."
  :long "
<ul>
<li>Combinational equivalence checking:
@({
  &r input-filename
  &put
  dcec
  print_status
  write_cex ctrex-filename
})
</li>

<li>Combinational simplification:
@({
  &r input-filename
  &put
  dc2
  dfraig
  &get
  &w output-filename
})
</li>

<li>Combinational simplification followed by equivalence checking:
@({
  &r input-filename
  &put
  dc2
  dfraig
  dcec
  print_status
  write_cex ctrex-filename
  &get
  &w output-filename
})
</li>

<li>Sequential model/equivalence checking:
@({
  &r input-filename
  &put
  dprove
  print_status
  write_cex ctrex-filename
 })
</li>

<li>Sequential simplification:
@({
  &r input-filename
  &put
  scleanup
  scorr
  dretime
  &get
  &w output-filename
 })
</li>

<li>Sequential simplification and proof:
@({
 &r input-filename
 &put
 dprove -u
 print_status
 write_cex ctrex-filename
 &get
 &w output-filename
 })
</li>
</ul>")
