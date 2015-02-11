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


; stv-compile.lisp -- compile a symbolic test vector into a compiled-stv that
; explains how to run an ESIM module over time
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "../esim-cut")
(include-book "../esim-sexpr-support")
;; (include-book "../follow-backwards")
(include-book "centaur/misc/vecs-ints" :dir :system)
(include-book "centaur/misc/tuplep" :dir :system)
(include-book "std/util/defmvtypes" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/lists/final-cdr" :dir :system)
(include-book "centaur/vl2014/util/defs" :dir :system)
(local (include-book "../esim-sexpr-support-thms"))
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))

(local (defthm atom-listp-of-pat-flatten1
         (atom-listp (pat-flatten1 x))
         :hints(("Goal" :in-theory (e/d (pat-flatten1)
                                        ((force)))))))

(local (in-theory (enable consp-when-member-equal-of-atom-listp)))


; NOTE: throughout this code we assume the STV has already been preprocessed!
;
;  - Each input/output name is a list of E bits (lsb order).  Any Verilog names
;    have already been expanded away into such lists, e.g., by stv-expand.
;
;  - Each internal/initial name is a list of E paths (lsb order).  Verilog names
;    have been expanded away.  The paths are not necessarily canonical.
;
;  - The input/output/internal lines have been widened (e.g., by stv-widen),
;    and all share some length.

(define stv-gensyms-aux ((prefix stringp)
                         (n      natp)
                         acc)
  :returns (syms symbol-listp :hyp (symbol-listp acc))
  :parents (stv-gensyms)
  (b* (((when (zp n))
        acc)
       (n     (- n 1))
       (sym1  (intern$ (str::cat prefix "[" (str::natstr n) "]") "ACL2")))
    (stv-gensyms-aux prefix n (cons sym1 acc)))
  ///
  (defthm len-of-stv-gensyms-aux
    (equal (len (stv-gensyms-aux prefix n acc))
           (+ (len acc) (nfix n)))))


(define stv-gensyms ((prefix stringp)
                     (n      natp))
  :returns (syms symbol-listp)
  :parents (stv-compile)
  :short "Generate a list of symbols, @('(foo[0] ... foo[n-1])')."
  ;; I originally used VL's emodwire stuff for this, but it's nice to eliminate
  ;; that dependency and just generate our own symbols.
  (stv-gensyms-aux prefix n nil)
  ///
  (defthm len-of-stv-gensyms
    (equal (len (stv-gensyms prefix n))
           (nfix n))))



; -----------------------------------------------------------------------------
;
;                COMPILING :INPUT LINE VALUES INTO 4V-SEXPRS
;
; -----------------------------------------------------------------------------

(define stv-expand-input-entry
  :parents (stv-compile)
  :short "Convert a single user-level input value (e.g., 17, X, abus, etc) into
a list of @(see 4v-sexprs)."

  :long "<p>This function basically defines what each value in an :input line
means.  We transform each such value into a list of @(see 4v-sexprs).  These
are the sexprs that will be given to this input during this phase.  At a high
level, our expansion strategy is:</p>

<ul>

<li><b>NAT</b>.  Expands to a list of @('*4vt-sexpr*') and @('*4vf-sexpr*')'s,
in LSB order, of the appropriate width.</li>

<li><b>X</b>.  Expands to a list of @('*4vx-sexpr*') of the appropriate
width.</li>

<li><b>:ONES</b>.  Expands to a list of @('*4vt-sexpr*') of the appropriate
width.</li>

<li><b>~</b>.  Expands to a singleton list whose one entry is either
@('*4vf-sexpr*') or @('*4vt-sexpr*'), based on the previous value for this
signal.</li>

<li><b>_</b>.  Expands to a list of variables, whose names are derived from the
names of input bits for this line.  Basically, @('|foo[0]|') gets turned into
@('|foo[0].P4|') in the 4th phase, etc.</li>

<li><b>Simulation variables</b>.  A simulation variable like @('opcode') is
turned into a list like @('(|opcode[0]| ... |opcode[n]|)').</li>

</ul>"

  ((name (and (atom-listp name)
              (consp name))
         "The name of this input, and should be a list of E input bits in
          lsb-first order.  (That is, Verilog-style names should have already
          been expanded away using @(see stv-expand).)")

   (width (equal width (len name))
          "Just the pre-computed width of this input.")

   (pnum natp
         "The current phase number (and starts at 0).  We use this to know what
          suffix to put onto the generated variable names for @('_') values,
          e.g., @('|foo[0].P4|').")

   (entry "The actual entry we are trying to expand.  For instance, it might be
           @('5'), @(':ones'), @('_'), or whatever else the user wrote down for
           this input at this phase number.")

   (gensyms "A flat list of all the names we have generated so far for @('_')
             entries, which we may extend.  This allows us to check for name
             collisions later on.")

   (usersyms "A fast alist that binds the names of simulation variables like
              @('opcode') to lists of bits that we generate for these symbols,
              i.e., @('(opcode[0] ... opcode[n])').  This allows us to check
              for name collisions with generated symbols and width mismatches.
              That is, we will allow the same variable to be given to multiple
              inputs at multiple phases, but for that to be sensible these
              inputs had better have the same width.")

   (prev-val "The sexpr list that this signal expanded to in the previous
              phase, or NIL if this is the first phase of the simulation.  We
              use this to figure out the new value of a @('~') entry."))

  :returns (mv new-val gensyms usersyms)

  (b* (((when (natp entry))
        (or (< entry (ash 1 width))
            (raise "Phase ~x0 for ~x1: value ~x2 is too wide to fit in ~x3 ~
                    bits!" pnum name entry width))
        (mv (bool-to-4v-sexpr-lst (int-to-v entry width)) gensyms usersyms))

       ((when (eq entry 'x))
        (mv (replicate width *4vx-sexpr*) gensyms usersyms))

       ((when (eq entry :ones))
        (mv (replicate width *4vt-sexpr*) gensyms usersyms))

       ((when (eq entry '~))
        (or (= width 1)
            (raise "Phase ~x0 for ~x1: value ~~ is not legal here.  It can ~
                    only be used in one-bit inputs, but this input is ~x2 ~
                    bits wide." pnum name width))
        (or prev-val
            (raise "Phase ~x0 for ~x1: value ~~ is not legal here.  It must ~
                    be preceeded by a constant true or false, so it cannot be ~
                    used at the start of a line." pnum name))
        (or (equal prev-val (list *4vt-sexpr*))
            (equal prev-val (list *4vf-sexpr*))
            (raise "Phase ~x0 for ~x1: value ~~ is not legal here.  It must ~
                    be preceeded by a constant true or false, but the ~
                    previous value was ~x2." pnum name prev-val))
        (mv (if (equal prev-val (list *4vt-sexpr*))
                (list *4vf-sexpr*)
              (list *4vt-sexpr*))
            gensyms usersyms))

       ((when (eq entry '_))
        (let ((my-syms (stv-suffix-signals name (str::cat ".P" (str::natstr pnum)))))
          (mv my-syms
              (append my-syms gensyms)
              usersyms)))

       ((unless (and (symbolp entry)
                     (not (keywordp entry))))
        (raise "Phase ~x0 for ~x1: value ~x2 is not legal for input lines of ~
                symbolic test vectors.  See :xdoc symbolic-test-vector-format ~
                for help." pnum name entry)
        (mv (replicate width *4vx-sexpr*) gensyms usersyms))

       (my-syms (stv-gensyms (symbol-name entry) width))
       (look    (hons-get entry usersyms)))

    (or (not look)
        (equal (cdr look) my-syms)
        (raise "Phase ~x0 for ~x1: variable ~x2 cannnot be used here.  This ~
                input is ~x3 bits wide, but ~x2 was previously used for a ~
                ~x4-bit input." pnum name entry width (len (cdr look))))
    (mv my-syms gensyms (if look
                            usersyms
                          (hons-acons entry my-syms usersyms))))
  ///
  (defthm true-listp-of-stv-expand-input-entry-gensyms
    (implies (true-listp gensyms)
             (b* (((mv ?new-val gensyms ?usersyms)
                   (stv-expand-input-entry name width pnum entry
                                           gensyms usersyms prev-val)))
               (true-listp gensyms)))))


(define stv-expand-input-entries
  :parents (stv-compile)
  :short "Extend @(see stv-expand-input-entry) across a line."
  ((name (and (atom-listp name)
              (consp name)))
   (width (equal width (len name)))
   (pnum natp)
   (entries true-listp)
   gensyms
   usersyms
   prev-val)
  :returns (mv new-entries gensyms usersyms)

  (b* (((when (atom entries))
        (mv nil gensyms usersyms))
       ((mv new-car gensyms usersyms)
        (stv-expand-input-entry name width pnum (car entries)
                                gensyms usersyms prev-val))
       ((mv new-cdr gensyms usersyms)
        (stv-expand-input-entries name width (+ 1 pnum) (cdr entries)
                                  gensyms usersyms new-car)))
    (mv (cons new-car new-cdr) gensyms usersyms))
  ///
  (defmvtypes stv-expand-input-entries (true-listp nil nil))

  (defthm true-listp-of-stv-expand-input-entries-gensyms
    (implies (true-listp gensyms)
             (b* (((mv ?new-entries gensyms ?usersyms)
                   (stv-expand-input-entries name width pnum entries
                                             gensyms usersyms prev-val)))
               (true-listp gensyms)))))


(define stv-expand-input-lines
  :parents (stv-compile)
  :short "Extend @(see stv-expand-input-entry) across a list of lines."
  ((lines true-list-listp)
   gensyms
   usersyms)
  :returns (mv (new-lines true-list-listp)
               gensyms
               usersyms)
  (b* (((when (atom lines))
        (mv nil gensyms usersyms))
       (line1 (car lines))
       ((cons name1 entries1) line1)

       ((unless (and (consp name1)
                     (atom-listp name1)))
        (raise "Expected all input line names to be already expanded to ~
                non-empty lists of E bits, but found ~x0." name1)
        (mv nil gensyms usersyms))

       ((mv new-entries1 gensyms usersyms)
        (stv-expand-input-entries name1 (len name1) 0 entries1 gensyms usersyms nil))
       (new-car (cons name1 new-entries1))
       ((mv new-cdr gensyms usersyms)
        (stv-expand-input-lines (cdr lines) gensyms usersyms)))
    (mv (cons new-car new-cdr) gensyms usersyms))
  ///
  (defmvtypes stv-expand-input-lines (true-listp nil nil))

  (defthm true-listp-of-stv-expand-input-lines-gensyms
    (let ((ret (stv-expand-input-lines lines gensyms usersyms)))
      (implies (true-listp gensyms)
               (true-listp (mv-nth 1 ret))))))



; -----------------------------------------------------------------------------
;
;                     CREATING THE SPECIALIZING ALIST
;
; -----------------------------------------------------------------------------

(define stv-restrict-alist-aux ((name atom-listp)
                                (phase natp)
                                entries
                                acc)
  :returns (acc alistp :hyp (alistp acc))
  :parents (stv-restrict-alist)
  (b* (((when (atom entries))
        acc)
       (name-at-phase (stv-suffix-signals name (str::cat ".P" (str::natstr phase))))
       (val-at-phase  (car entries))
       (acc           (safe-pairlis-onto-acc name-at-phase val-at-phase acc)))
    (stv-restrict-alist-aux name (+ 1 phase) (cdr entries) acc)))

(define stv-restrict-alist
  :parents (stv-compile)
  :short "Construct an alist binding fully-general input names (for all phases)
to @(see 4v-sexprs) derived from the symbolic test vector."

  ((lines true-list-listp
          "The output from @(see stv-expand-input-lines).  That is, these
           should STV input lines that have already been widened, had their
           names resolved into E bits, and had their entries turned into
           4v-sexpr lists.")
   (acc "An alist that we extend.  Typically it is the alist that has the
         @(':initial') bindings."))

  :returns (restrict-alist alistp :hyp (alistp acc))

  :long "<p>We construct an ordinary (slow) alist that binds the input names we
are going to use in our fully-general @(see esim) simulation to their bindings
according to the symbolic test vector.  This is a single alist that includes
the bindings for the variables at all phases, plus (presumably, via acc) any
initial bindings for state bits.</p>

<p>The sexprs in this alist will often be constants (e.g., when natural
numbers, @(':ones'), @('x'), or @('~') values are used), but they can also have
free variables from @('_') symbols and also simulation variable bits.</p>

<p>The general intent is to make the resulting alist fast, and use it along
with @(see 4v-sexpr-restrict) to specialize the fully general simulation,
effectively \"assuming\" the STV.</p>"

    (b* (((when (atom lines))
          acc)
         (line1 (car lines))
         ((cons name entries) line1)
         ((unless (atom-listp name))
          (raise "Name should be a list of E bits, but is ~x0." name))
         (acc (stv-restrict-alist-aux name 0 entries acc)))
      (stv-restrict-alist (cdr lines) acc)))



; -----------------------------------------------------------------------------
;
;               COMPILING :OUTPUT LINE VALUES INTO 4V-SEXPRS
;
; -----------------------------------------------------------------------------

(define stv-expand-output-entry
  :parents (stv-compile)
  :short "Convert a single user-level output/internal value (e.g., _, result)
into a list of @(see 4v-sexprs)."

  :long "<p>The only valid entries for output lines are @('_') (for signals we
don't care about) and simulation variables.  Here, we just leave any @('_')
values alone, but we replace simulation variables with lists of new variables
that we generate from their names.  That is, a simulation variable like
@('result') will be converted into a list of bits like @('(result[0]
... result[4])').</p>"

  ((name (and (true-listp name)
              (consp name))
         "The name of this output.  It should be a list of E input bits in
          lsb-first order.  That is, Verilog-style names should have already
          been expanded away using @(see stv-expand).")

   (width (equal width (len name))
          "Just the pre-computed width of this output.  It must be exactly
           equal to @('(len name)').  This lets us know how many variables to
           generate when we hit a simulation variable.")

   (pnum natp
         "The current phase number (and starts at 0).  This is semantically
          irrelevant; we use it only to generate better error messages.")

   (entry "The actual entry we are trying to expand, i.e., it's what the user
           wrote down for this output at this phase.  To be well-formed, the
           entry needs to be @('_') or a simulation variable, but the user can
           write down anything so we have to check that it is valid.")

   (usersyms "A fast alist binding simulation variables to the lists of bits
              that we've generated to represent them.  We assume this only
              contains the output simulation variables.  This lets us make sure
              that output variables aren't being reused."))

  :returns (mv new-val usersyms)

  (b* (((when (or (natp entry)
                  (eq entry 'x)
                  (eq entry '~)
                  (keywordp entry)
                  (not (symbolp entry))))
        (raise "Phase ~x0 for ~x1: value ~x2 is not legal for :output lines."
               pnum name entry)
        (mv nil usersyms))

       ((when (eq entry '_))
        ;; That's fine, just leave it alone.
        (mv entry usersyms))

       ;; Else, a simulation variable.  It had better not be used yet.
       (look (hons-get entry usersyms))
       ((when look)
        (raise "Phase ~x0 for ~x1: variable ~x2 is already in use, so it ~
                cannot be used again." pnum name entry)
        (mv nil usersyms))

       ;; Okay it wasn't used.  Make its symbols and such.
       (my-syms  (stv-gensyms (symbol-name entry) width))
       (usersyms (hons-acons entry my-syms usersyms)))
    (mv my-syms usersyms)))

(define stv-expand-output-entries
  :parents (stv-compile)
  :short "Extend @(see stv-expand-output-entry) across a line."
  ((name    (and (true-listp name) (consp name)))
   (width   (equal width (len name)))
   (pnum    natp)
   (entries true-listp)
   usersyms)
  :returns (mv (new-entries true-listp :rule-classes :type-prescription)
               usersyms)
  (b* (((when (atom entries))
        (mv nil usersyms))
       ((mv new-car usersyms)
        (stv-expand-output-entry name width pnum (car entries) usersyms))
       ((mv new-cdr usersyms)
        (stv-expand-output-entries name width (+ 1 pnum) (cdr entries) usersyms)))
    (mv (cons new-car new-cdr) usersyms)))

(define stv-expand-output-lines
  :parents (stv-compile)
  :short "Extend @(see stv-expand-output-entry) across a list of lines."

  ((lines true-list-listp) usersyms)
  :returns (mv (new-lines true-list-listp)
               usersyms)
  (b* (((when (atom lines))
        (mv nil usersyms))
       (line1 (car lines))
       ((cons name1 entries1) line1)

       ((unless (and (consp name1)
                     (atom-listp name1)))
        (raise "Expected :output line names to be already expanded to ~
                non-empty lists of E bits, but found ~x0." name1)
        (mv nil usersyms))

       ((mv new-entries1 usersyms)
        (stv-expand-output-entries name1 (len name1) 0 entries1 usersyms))

       (new-car (cons name1 new-entries1))
       ((mv new-cdr usersyms)
        (stv-expand-output-lines (cdr lines) usersyms)))
    (mv (cons new-car new-cdr) usersyms)))



; -----------------------------------------------------------------------------
;
;               COMPILING :INTERNAL LINE VALUES INTO 4V-SEXPRS
;
; -----------------------------------------------------------------------------

; These are almost the same as output lines.  The only difference is that we
; need to canonicalize their paths.

(define stv-expand-internal-line
  :parents (stv-compile)
  ((line true-listp)
   usersyms
   (mod good-esim-modulep))
  :returns (mv (new-line true-listp :rule-classes :type-prescription)
               usersyms)
  (b* (((cons name entries) line)
       ((unless (and (consp name)
                     (true-listp name)))
        (raise "Expected :internal line names to be already expanded to ~
                non-empty lists of E paths, but found ~x0." name)
        (mv nil usersyms))

       ;; The ESIM simulation only involves canonical paths, so to be able to
       ;; extract the right paths we need to canonicalize these paths.
       ((mv okp new-name) (fast-canonicalize-paths name mod))
       ((unless okp)
        (raise "Failed to canonicalize all the paths for ~x0." name)
        (mv nil usersyms))
       ((mv new-entries usersyms)
        (stv-expand-output-entries new-name (len new-name) 0 entries usersyms))
       (new-line (cons new-name new-entries)))
    (mv new-line usersyms))
  :prepwork
  ((local (defthm fast-canonicalize-paths-1-under-iff
            (iff (mv-nth 1 (fast-canonicalize-paths paths mod))
                 (consp paths))
            :hints(("Goal" :in-theory (enable fast-canonicalize-paths)))))))

(define stv-expand-internal-lines
  :parents (stv-compile)
  :short "Extend @(see stv-expand-internal-line) across a list of lines."
  ((lines true-list-listp)
   (usersyms)
   (mod good-esim-modulep))
  :returns (mv (new-lines true-list-listp)
               usersyms)
  (b* (((when (atom lines))
        (mv nil usersyms))
       ((mv line1 usersyms) (stv-expand-internal-line (car lines) usersyms mod))
       ((mv lines2 usersyms) (stv-expand-internal-lines (cdr lines) usersyms mod)))
    (mv (cons line1 lines2) usersyms)))



; -----------------------------------------------------------------------------
;
;                     CREATING THE EXTRACTION ALISTS
;
; -----------------------------------------------------------------------------

(define stv-nth-extraction-alist
  :parents (stv-extraction-alists)
  :short "Add the bindings for name to entryN to the NTH-ALIST-ACC"
  ((n             natp)
   (lines         true-list-listp   "A list of (name entry1 ... entryK)")
   (nth-alist-acc alistp))
   (b* (((when (atom lines))
         nth-alist-acc)
        (line1 (car lines))
        ((cons name entries) line1)
        (entry (nth n entries))
        ((when (eq entry '_))
         ;; Don't care about this output at this time.  Keep going.
         (stv-nth-extraction-alist n (cdr lines) nth-alist-acc))
        (nth-alist-acc (safe-pairlis-onto-acc name entry nth-alist-acc)))
     (stv-nth-extraction-alist n (cdr lines) nth-alist-acc)))

(define stv-extraction-alists
  :parents (stv-compile)
  :short "Alists explaining what signals we want to extract from the simulation
after each phase."
  ((n          natp            "Initially this is the total number of phases.
                                It will counts down from the max phase to 0.")

   (lines      true-list-listp "Constant.  Expanded output or internals lines.")

   (alists-acc "Accumulator, initially nil."))

  :returns (alists-acc "A list of alists that say, after each step, which
                        output bits we want to collect, and how to name them."
                       true-listp :hyp (true-listp alists-acc))

  :long "<p>The basic idea is that if we have a list of outputs lines like:</p>

@({
   (foo  _ _ a _)
   (bar  _ b _ c)
   (baz  _ _ d _)
})

<p>Then we will want to create four alists, one for each phase.  The P0 alist
is empty.  The P1 alist binds something like</p>

@({
   ((bar[0] . b[0])
    (bar[1] . b[1])
    ...
    (bar[n] . b[n]))
})

<p>The P2 alist binds something like:</p>

@({
 ((foo[0] . a[0])
   ...
  (foo[n] . a[n])
  (baz[0] . d[0])
   ...
  (baz[0] . d[k]))
})

<p>And so on.  That is, each of these extraction alists says, for a particular
phase, the names of the output signals we want to extract from the simulation,
and which bit of which simulation variable the name corresponds to.</p>"

  (let* ((nth-alist  (stv-nth-extraction-alist n lines nil))
         (alists-acc (cons nth-alist alists-acc)))
    (if (zp n)
        alists-acc
      (stv-extraction-alists (- n 1) lines alists-acc))))



; -----------------------------------------------------------------------------
;
;                         COMPILING :OVERRIDE LINES
;
; -----------------------------------------------------------------------------

(define stv-append-alist-keys ((lines))
  :returns (name-bits "Flat list of paths from the car of each line."
                      true-listp :rule-classes :type-prescription)
  (if (atom lines)
      nil
    (append-without-guard (and (consp (car lines)) (caar lines))
                          (stv-append-alist-keys (cdr lines)))))

(define stv-cut-module
  ((override-paths "Already expanded path to every signal we want to override.
                    These are paths to real wire in the module, e.g., foo
                    instead of foo<override_value> or similar."
                   true-listp)
   (mod            good-esim-modulep))
  :returns (new-mod good-esim-modulep "The cut module." :hyp :guard)
  (b* ((new-mod (ecut-module override-paths mod))
       ((unless (good-esim-modulep new-mod))
        (raise "Ecut failed to produce a good esim module: ~@0"
               (bad-esim-modulep new-mod))
        mod))
    new-mod))

(define stv-expand-override-entry
  ((name "The name of this override line.  This will be a list of E paths."
         (and (consp name)
              (true-listp name)))
   (width "Pre-computed width of the name."
          (equal (len name) width))
   (pnum  "Current phase number (may not be necessary for anything, but lets
           us generate better error messages.)"
          natp)
   (entry "The actual entry we're trying to expand.")
   (in-usersyms
    "Fast alist binding simulation variables to lists of bits that we've
     generated to represent them.  We assume this contains only the input
     variables.")
   (out-usersyms
    "Same, but for outputs."))
  :returns
  (mv (in-value-sexprs)
      (in-decision-sexprs)
      (out-value-vars   "either a list of variables or a _")
      (new-in-usersyms)
      (new-out-usersyms))
  (b* (((when (natp entry))
        (or (< entry (ash 1 width))
            (raise "Phase ~x0 for ~x1: value ~x2 is too wide to fit in ~x3 ~
                    bits!" pnum name entry width))
        (mv (bool-to-4v-sexpr-lst (int-to-v entry width))
            (replicate width *4vt-sexpr*)
            '_
            in-usersyms
            out-usersyms))

       ((when (eq entry 'x))
        (mv (replicate width *4vx-sexpr*)
            (replicate width *4vt-sexpr*)
            '_
            in-usersyms
            out-usersyms))

       ((when (eq entry :ones))
        (mv (replicate width *4vt-sexpr*)
            (replicate width *4vt-sexpr*)
            '_
            in-usersyms
            out-usersyms))

       ((when (eq entry '~))
        (raise "Phase ~x0 for ~x1: value ~~ is not legal on overrides." pnum name)
        (mv (replicate width *4vx-sexpr*)
            (replicate width *4vt-sexpr*)
            '_
            in-usersyms
            out-usersyms))

       ((when (eq entry '_))
        (mv (replicate width *4vx-sexpr*)
            (replicate width *4vf-sexpr*)
            '_
            in-usersyms
            out-usersyms))

       ((unless (and (symbolp entry)
                     (not (keywordp entry))))
        (raise "Phase ~x0 for ~x1: value ~x2 is not legal for override lines of ~
                symbolic test vectors.  See :xdoc symbolic-test-vector-format ~
                for help." pnum name entry)
        (mv (replicate width *4vx-sexpr*)
            (replicate width *4vt-sexpr*)
            '_
            in-usersyms
            out-usersyms))

       (my-syms (stv-gensyms (symbol-name entry) width))
       (out-look    (hons-get entry out-usersyms))
       (in-look    (hons-get entry in-usersyms)))

    (and out-look
         (raise "Phase ~x0 for ~x1: variable ~x2 is already in use, so it ~
                 cannot be used again."
          pnum name entry))

    (or (not in-look)
        (equal (cdr in-look) my-syms)
        (raise "Phase ~x0 for ~x1: variable ~x2 cannnot be used here.  This ~
                override is ~x3 bits wide, but ~x2 was previously used for a ~
                ~x4-bit wire." pnum name entry width (len (cdr in-look))))

    (mv my-syms
        (replicate width *4vt-sexpr*)
        my-syms
        (if in-look in-usersyms (hons-acons entry my-syms in-usersyms))
        (hons-acons entry my-syms out-usersyms))))


(define stv-expand-override-entries
  ((name "The name of this override line.  This will be a list of E paths."
         (and (consp name)
              (true-listp name)))
   (width "Pre-computed width of the name."
          (equal (len name) width))
   (pnum  "Current phase number (may not be necessary for anything, but lets
           us generate better error messages.)"
          natp)
   (entries "The rest of the entries")
   (in-usersyms
    "Fast alist binding simulation variables to lists of bits that we've
     generated to represent them.  We assume this contains only the input
     variables.")
   (out-usersyms
    "Same, but for outputs."))
  :returns
  (mv (in-value-entries    true-listp)
      (in-decision-entries true-listp)
      (out-value-entries   true-listp)
      (new-in-usersyms)
      (new-out-usersyms))
  (b* (((when (atom entries))
        (mv nil nil nil in-usersyms out-usersyms))
       ((mv first-values first-decisions first-outs in-usersyms out-usersyms)
        (stv-expand-override-entry
         name width pnum (car entries) in-usersyms out-usersyms))
       ((mv rest-values rest-decisions rest-outs in-usersyms out-usersyms)
        (stv-expand-override-entries
         name width (+ 1 pnum) (cdr entries) in-usersyms out-usersyms)))
    (mv (cons first-values rest-values)
        (cons first-decisions rest-decisions)
        (cons first-outs rest-outs)
        in-usersyms out-usersyms)))

(define stv-forge-state-bit ((instnames "List of instance names")
                             (st-name atom))
  :returns (full-name atom :hyp :guard)
  :parents (stv-compile)
  :short "Generate the name for a state bit, like @('foo!bar!baz!inst!S'),
given a list of instance names and the name of the state bit."
  ;; BOZO have to keep this in sync with mod-state/occ-state
  (if (atom instnames)
      st-name
    (acl2::prefix-atom (acl2::stringify (car instnames))
                       "!"
                       (stv-forge-state-bit (cdr instnames) st-name))))

(std::defprojection stv-forge-state-bits (instnames x)
  (stv-forge-state-bit instnames x)
  :guard (atom-listp x)
  :result-type atom-listp)


(define stv-path-to-override-value-instnames (path)
  :returns (st-path)
  (if (atom path)
      (if (symbolp path)
          (list (ecutnames->value-reg (ecut-wire-names path)))
        (raise "end of path isn't a symbol"))
    (cons (car path) (stv-path-to-override-value-instnames (cdr path)))))

(define stv-path-to-override-value-stbit (path)
  :returns (st)
  (stv-forge-state-bit (stv-path-to-override-value-instnames path)
                       "S"))

(define stv-path-to-override-decision-instnames (path)
  :returns (st-path)
  (if (atom path)
      (if (symbolp path)
          (list (ecutnames->decision-reg (ecut-wire-names path)))
        (raise "end of path isn't a symbol"))
    (cons (car path) (stv-path-to-override-decision-instnames (cdr path)))))

(define stv-path-to-override-decision-stbit (path)
  :returns (st)
  (stv-forge-state-bit (stv-path-to-override-decision-instnames path)
                       "S"))

(std::defprojection stv-paths-to-override-value-stbits (x)
  (stv-path-to-override-value-stbit x)
  :guard t
  :parents nil)

(std::defprojection stv-paths-to-override-decision-stbits (x)
  (stv-path-to-override-decision-stbit x)
  :guard t
  :parents nil)





(define stv-expand-override-lines
  ((lines "all the override lines, names already expanded into paths"
          true-list-listp)
   in-usersyms out-usersyms)
  :returns (mv (in-table true-list-listp)
               (out-table true-list-listp)
               new-in-usersyms new-out-usersyms)
  (b* (((when (atom lines))
        (mv nil nil in-usersyms out-usersyms))
       ((cons name entries) (car lines))
       ((unless (and (consp name) (true-listp name)))
        (raise "Programming error: malformed name ~x0" name)
        (mv nil nil in-usersyms out-usersyms))
       ((mv val-entries decision-entries out-entries in-usersyms out-usersyms)
        (stv-expand-override-entries
         name (len name) 0 entries in-usersyms out-usersyms))

       (val-stbits (stv-paths-to-override-value-stbits name))
       (dec-stbits (stv-paths-to-override-decision-stbits name))

       (in-val-line (cons val-stbits val-entries))
       (in-dec-line (cons dec-stbits decision-entries))

       (out-line (cons val-stbits out-entries))

       ((mv in-table out-table in-usersyms out-usersyms)
        (stv-expand-override-lines (cdr lines) in-usersyms out-usersyms)))
    (mv (cons in-val-line (cons in-dec-line in-table))
        (cons out-line out-table)
        in-usersyms out-usersyms)))


#||
(stv-expand-override-lines
 '((;; name
    ((a b . c[0])
     (a b . c[1]))
    ;; entries
    0
    X
    :ones
    a
    b
    2
    _))
 nil
 nil)
||#


















#||

(include-book
 "stv-expand")

(defconst *s0*
  (make-stvdata :inputs nil
                :outputs nil
                :internals nil
                :initial '(("mmxcntl.rsMmxSrc3_I" src3i)
                             ("mmxcntl.rsMmxSrc2_I[4:2]" _)
                             ("mmxcntl.rsMmxSrc2_I[0]" 1)
                             ("mmxcntl.rsFeuBIBus_I[16:0]" bibus))))

(defconst *s1*
  (stv-expand *s0* |*mmx*|))

(b* (((mv alist ?usersyms)
      (stv-initial-lines-to-alist (stvdata->initial *s1*) nil |*mmx*|)))
  (stv-add-suffixes-to-initial-alist alist))


||#



; -----------------------------------------------------------------------------
;
;                         TOP-LEVEL STV COMPILATION
;
; -----------------------------------------------------------------------------

(define stv-compile
  :parents (symbolic-test-vectors)
  :short "Syntactically transform a symbolic test vector, readying it for
evaluation, debugging, etc."

  ((stv stvdata-p
        "An @(see stvdata-p) that has already had its lines widened and any
         Verilog-style names expanded; see @(see stv-widen) and @(see
         stv-expand).")

   (mod good-esim-modulep
        "The @(see esim) module this STV is about."))

  :returns (cstv (equal (compiled-stv-p cstv)
                        (if cstv t nil)))

  :long "<p>Compiling an STV involves doing lots of error checking to ensure
the STV is syntactically well-formed, only refers to legitimate inputs and
outputs, and so forth.  After sanity checking, our basic goal is to compile the
STV into a form that functions like @(see stv-run) and @(see stv-debug) can
efficiently process.</p>

<p>In particular, after (successfully) compiling an STV we obtain a @(see
compiled-stv-p) structure that says says how many steps we need to run for,
explains the mappings from user-level simulation variables to their internal
bit-encodings, and and has pre-computed alists for restricting the a @(see
esim) run and extracting the results.</p>

<p>Compilation is a syntactic process that is relatively cheap.  We @(see
memoize) it mainly in the hopes of keeping the various alists we create the
same across multiple evaluations of an STV.</p>

<p>Note that to reuse the same @(see esim) simulations across related STVs, our
basic approach in @(see stv-run) is to do a fully general simulation of the
module for N cycles.  In this general simulation, we set @('|foo[0]|') to
@('|foo[0].P3|') during phase 3, and so forth.  The idea is that instead of
re-running @(see esim) for each STV, we will just specialize this alist by
using @(see 4v-sexpr-restrict) to replace @('|foo[0].P3|') with whatever value
we want for @('|foo[0]|') at phase 3.</p>

<p>The function @(see stv-restrict-alist) pre-computes these bindings.
Essentially it just needs to build a big alist that binds the suffixed input
names to the sexprs that we generated in @(see stv-expand-input-lines),
above.</p>

<p>The outputs are somewhat similar.  The function @(see stv-extraction-alists)
builds a list of alists that say, for each step, which output bits we want to
collect and how we want to name them.</p>"

  (b* (((stvdata stv) stv)
       (nphases (stv-number-of-phases stv))
       ((unless (posp nphases))
        (raise "Trying to compile an STV without any phases?"))

       (override-paths (stv-append-alist-keys stv.overrides))
       (mod (stv-cut-module override-paths mod))

       ;; Inputs...
       (in-usersyms nil)
       ((mv inputs gensyms in-usersyms)
        (stv-expand-input-lines stv.inputs nil in-usersyms))

       (restrict-alist nil)
       (restrict-alist (stv-restrict-alist inputs restrict-alist))

       ;; Outputs and internals...
       (out-usersyms nil)
       ((mv outputs out-usersyms)
        (stv-expand-output-lines stv.outputs out-usersyms))
       ((mv internals out-usersyms)
        (stv-expand-internal-lines stv.internals out-usersyms mod))
       (out-extract-alists (stv-extraction-alists (- nphases 1) outputs nil))
       (int-extract-alists (stv-extraction-alists (- nphases 1) internals nil))

       ((mv override-ins override-outs in-usersyms out-usersyms)
        (stv-expand-override-lines stv.overrides in-usersyms out-usersyms))
       (restrict-alist (stv-restrict-alist override-ins restrict-alist))
       (nst-extract-alists (stv-extraction-alists (- nphases 1) override-outs nil))

       (all-in-bits (alist-keys restrict-alist))
       ((unless (uniquep all-in-bits))
        ;; This could be really bad because you'd be shadowing one value with
        ;; another, and it could easily happen to you if you gave two
        ;; different paths on :initial things that turned out to refer to the
        ;; same state bit.
        (raise "Name clash.  Multiple input/initial bindings were generated ~
                for ~x0." (duplicated-members all-in-bits)))

       (in-simvars  (alist-keys in-usersyms))
       (out-simvars (alist-keys out-usersyms))
       ((unless (and (uniquep in-simvars)
                     (uniquep out-simvars)
                     (symbol-listp in-simvars)
                     (symbol-listp out-simvars)))
        (raise "Programming error.  in-simvars or out-simvars aren't unique ~
                symbols.  This shouldn't be possible."))

       ;; (illegally-reused-simvars
       ;;  (duplicated-members (append in-simvars out-simvars)))
       ;; ((when illegally-reused-simvars)
       ;;  ;; This is something the user could try to do.  It wouldn't *really*
       ;;  ;; be a problem, but certainly seems to indicate confusion on their
       ;;  ;; part.
       ;;  (raise "Error: It is illegal to reuse the input simulation variables ~
       ;;          (from :input and :initial lines) as output simulation ~
       ;;          variables (from :output and :internal lines).  Illegally ~
       ;;          reused variables: ~x0" illegally-reused-simvars))

       (all-in-bits (vl2014::append-alist-vals-exec in-usersyms gensyms))
       ((unless (uniquep all-in-bits))
        ;; It's hard to imagine this happening, but if somehow the user gave an
        ;; input simulation variable name that clashed with a gensym, it'd be
        ;; bad.
        (raise "Name clash for ~x0." (duplicated-members all-in-bits)))

       (override-bits
        (stv-append-alist-keys override-ins))
       ((unless (symbol-listp override-bits))
        (raise "Programming error -- override-bits should be a symbol-list: ~x0"
               override-bits))

       (ret (make-compiled-stv
             :nphases        nphases
             :restrict-alist restrict-alist

             ;; These have to stay separate because we have to use them to
             ;; extract from different esim outputs
             :out-extract-alists out-extract-alists
             :int-extract-alists int-extract-alists
             :nst-extract-alists nst-extract-alists

             :override-bits override-bits

             ;; I reverse these here so that they are "in the right order"
             ;; per the lines of the STV.  This isn't anything that is
             ;; semantically important, but it makes things like
             ;; stv-autohyps, stv-autoins, stv->ins, etc. nicer to look at
             ;; because you see the stuff in the same order as you put it in.
             :in-usersyms  (make-fast-alist (rev in-usersyms))
             :out-usersyms (make-fast-alist (rev out-usersyms))

             ;; These have some various uses in documentation and also in
             ;; stv-process, but probably we should work to get rid of these.
             :expanded-ins  inputs

             :override-paths override-paths
             )))

    (fast-alist-free in-usersyms)
    (fast-alist-free out-usersyms)
    ret)

  ///

  ;; Compilation isn't necessarily slow, but memoizing it seems like a good
  ;; idea to make sure that all of the alists stay the same.
  (memoize 'stv-compile))


