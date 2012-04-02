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


; stv-compile.lisp -- frontend for sanity checking and compiling symbolic test
; vectors into the alists that explain how to manipulate a fully general ESIM
; run.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-expand")
(include-book "esim-sexpr-support")
(include-book "esim-vl")
(include-book "centaur/misc/vecs-ints" :dir :system)
(local (include-book "esim-sexpr-support-thms"))
(local (include-book "centaur/vl/util/arithmetic" :dir :system))


(defxdoc stv-compile
  :parents (symbolic-test-vectors)
  :short "Syntactically transform a symbolic test vector, readying it for
evaluation, debugging, etc."

  :long "<p><b>Signature:</b> @(call stv-compile) returns a @(see
compiled-stv-p).</p>

<p>Here, <tt>mod</tt> should be a valid @(see esim) module, and <tt>stv</tt>
should be a valid, user-level symbolic-test-vector for this module.  In
particular, see @(see symbolic-test-vector-format) to understand how the
<tt>stv</tt> should look.</p>

<p>Compiling an STV involves doing lots of error checking to ensure the STV is
syntactically well-formed, only refers to legitimate inputs and outputs, and so
forth.  After sanity checking, our basic goal is to compile the STV into a form
that functions like @(see stv-run) and @(see stv-debug) can efficiently
process.</p>

<p>In particular, after compiling an STV we obtain an @(see compiled-stv-p)
structure that says says how many steps we need to run for, explains the
mappings from user-level simulation variables to their internal bit-encodings,
and and has pre-computed alists for restricting the a @(see esim) run and
extracting the results.</p>

<p>Compilation is a syntactic process that is relatively cheap.  We memoize it
mainly in the hopes that it will keep the various alists the same across
multiple evaluations of an STV.</p>


<h3>The Compilation Process</h3>

<p>We begin by syntactically simplifying the STV.</p>

<ol>

<li>We use @(see stv-widen) to repeat the last entry of each line until all the
input, output, and internal lines are the same length.</li>

<li>We then use @(see stv-expand-names) to expand away any strings used as
input/output names, by looking them up in the module and converting them into
lists of E bits.  Any names that were already made up of E bits are also
checked against the module's inputs/outputs to make sure they exist, and we
make sure no input bits are duplicated.</li>

<li>We finally use @(see stv-expand-hids) to expand away any internal signal
names into lists of canonical E Paths; see @(see mod-internal-paths).</li>

</ol>

<p>We then comprehend the entries in the STV lines.</p>

<ol>

<li>In @(see stv-expand-input-lines), we replace each entry in every input line
with a list of @(see 4v-sexprs) that should be used at that phase.  For
instance, numbers gets turned into a list of <tt>(T)</tt> and <tt>(F)</tt>
expressions, underscores get turned into generated symbols names, and input
simulation variables get turned into lists of variables representing their
bits.</li>

<li>In @(see stv-expand-output-lines), we similarly replace the entries in each
output and internal line.  Underscores get replaced with NIL, and output
simulation variables get replaced with lists of variables representing their
bits.</li>

</ol>

<p>Some sanity checking is needed to ensure there are no name clashes between
generated names and simulation-variable bit names.  We also do some checking to
make sure that every use of an input simulation variable has the same width,
that there is no confusion between input/output simulation variables, etc.</p>

<p>Finally, we prepare to simulate the STV by pre-computing certain alists that
will be useful in functions like @(see stv-run) and @(see stv-debug).</p>

<p>Note that to reuse the same @(see esim) simulations across related STVs, our
basic approach in @(see stv-run) is to do a fully general simulation of the
module for N cycles.  In this general simulation, we set <tt>|foo[0]|</tt> to
<tt>|foo[0].P3|</tt> during phase 3, and so forth.  The idea is that instead of
re-running @(see esim) for each STV, we will just specialize this alist by
using @(see 4v-sexpr-restrict) to replace <tt>|foo[0].P3|</tt> with whatever value
we want for <tt>|foo[0]|</tt> at phase 3.</p>

<p>The function @(see stv-restrict-alist) pre-computes these bindings.
Essentially it just needs to build a big alist that binds the suffixed input
names to the sexprs that we generated in @(see stv-expand-input-lines),
above.</p>

<p>The outputs are somewhat similar.  The function @(see stv-extraction-alists)
builds a list of alists that say, for each step, which output bits we want to
collect and how we want to name them.</p>


<h3>Definition</h3>

@(def stv-compile)")

(defund basic-stv-p (stv)
  (declare (xargs :guard t))
  (and (true-list-listp (cdr (hons-assoc-equal :inputs stv)))
       (true-list-listp (cdr (hons-assoc-equal :outputs stv)))
       (true-list-listp (cdr (hons-assoc-equal :internals stv)))
       ))

(local (in-theory (enable basic-stv-p)))


(defsection stv-suffix-symbols
  :parents (stv-compile)
  :short "@(call stv-suffix-symbols) adds <tt>suffix</tt> to the name of every
symbol in the list <tt>x</tt>."

  (defund stv-suffix-symbols (x suffix)
    (declare (xargs :guard (and (symbol-listp x)
                                (stringp suffix))))
    (if (atom x)
        nil
      (cons (intern-in-package-of-symbol (str::cat (symbol-name (car x)) suffix)
                                         (car x))
            (stv-suffix-symbols (cdr x) suffix))))

  (local (in-theory (enable stv-suffix-symbols)))

  (defthm symbol-listp-of-stv-suffix-symbols
    (symbol-listp (stv-suffix-symbols x suffix))))


(defun safe-pairlis-onto-acc (x y acc)
  ;; Just pairs up X and Y and accumulates them onto acc, but causes an error
  ;; if X and Y aren't the same length.
  (declare (xargs :guard t))
  (mbe :logic
       (revappend (pairlis$ x y) acc)
       :exec
       (cond ((atom x)
              (if (atom y)
                  acc
                (prog2$ (er hard? 'safe-pairlis-onto-acc "Too many values!")
                        acc)))
             ((atom y)
              (prog2$ (er hard? 'safe-pairlis-onto-acc "Not enough values!")
                      (safe-pairlis-onto-acc (cdr x) nil
                                             (cons (cons (car x) nil)
                                                   acc))))
             (t
              (safe-pairlis-onto-acc (cdr x) (cdr y)
                                     (cons (cons (car x) (car y))
                                           acc))))))




; -----------------------------------------------------------------------------
;
;                       WIDENING STV PHASE LISTS
;
; -----------------------------------------------------------------------------

; As described above, we want to repeat the final value in the phase lists all
; the way to the end of the simulation.
;
; We now introduce a transform which explicitly repeats the final values of the
; phase lists and makes all of the phase lists have the same length.

(defsection stv-number-of-phases
  :parents (stv-widen)
  :short "@(call stv-number-of-phases) determines the maximum number of phases
that are used in any line of a symbolic test vector."

  (defund stv-max-phases-in-lines (lines)
    (declare (xargs :guard (true-list-listp lines)))
    (if (atom lines)
        0
      (max (length (cdr (car lines)))
           (stv-max-phases-in-lines (cdr lines)))))

  (defund stv-number-of-phases (stv)
    (declare (xargs :guard (basic-stv-p stv)))
    (max (stv-max-phases-in-lines (cdr (hons-assoc-equal :inputs stv)))
         (max (stv-max-phases-in-lines (cdr (hons-assoc-equal :outputs stv)))
              (stv-max-phases-in-lines (cdr (hons-assoc-equal :internals stv)))))))


(defsection stv-widen-lines
  :parents (stv-widen)
  :short "@(call stv-widen-lines) rewrites the lines of an STV by repeating
the last entry in each line until there are the desired number of phases."

  :long "<p>The <tt>warn-non-blank</tt> flag is set for output lines.  When it
is set, we cause an error if an attempt is made to replicate any element other
than <tt>_</tt>, since it doesn't make sense to replicate simulation
variables.</p>"

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
  :parents (stv-compile)
  :short "@(call stv-widen) rewrites a symbolic test vector by repeating the
last element of each line as necessary so that all lines become the same
length."

  (defund stv-widen (stv)
    (declare (xargs :guard (basic-stv-p stv)))
    (b* ((number-of-phases  (stv-number-of-phases stv))
         (inputs            (cdr (hons-assoc-equal :inputs stv)))
         (outputs           (cdr (hons-assoc-equal :outputs stv)))
         (internals         (cdr (hons-assoc-equal :internals stv)))
         (widened-inputs    (stv-widen-lines inputs number-of-phases nil))
         (widened-outputs   (stv-widen-lines outputs number-of-phases t))
         (widened-internals (stv-widen-lines internals number-of-phases t)))
      (list (cons :inputs    widened-inputs)
            (cons :outputs   widened-outputs)
            (cons :internals widened-internals))))

  (local (in-theory (enable stv-widen)))

  (defthm basic-stv-p-of-stv-widen
    (implies (basic-stv-p stv)
             (basic-stv-p (stv-widen stv)))))




; -----------------------------------------------------------------------------
;
;                   EXPANDING STV SIGNAL NAMES INTO BITS
;
; -----------------------------------------------------------------------------

(defsection stv-expand-names-in-lines
  :parents (stv-expand-names)
  :short "@(call stv-expand-names-in-lines) expands all of the names in a list
of STV input or output lines, using @(see vl::stv-expand-name)."

  (defund stv-expand-names-in-lines (lines type mod)
    (declare (xargs :guard (and (or (eq type :i)
                                    (eq type :o))
                                (true-list-listp lines))))
    (b* (((when (atom lines))
          nil)
         (line1              (car lines))
         ((cons name phases) line1)
         (new-name           (vl::stv-expand-name name type mod)))
      (cons (cons new-name phases)
            (stv-expand-names-in-lines (cdr lines) type mod))))

  (local (in-theory (enable stv-expand-names-in-lines)))

  (defthm alistp-of-stv-expand-names-in-lines
    (alistp (stv-expand-names-in-lines lines type mod)))

  (defthm true-list-listp-of-stv-expand-names-in-lines
    (implies (true-list-listp lines)
             (true-list-listp (stv-expand-names-in-lines lines type mod)))))


(defsection stv-expand-hids-in-lines
  :parents (stv-expand-names)
  :short "@(call stv-expand-hids-in-lines) expands all of the HIDs in a list of
STV internals lines."

  (defund stv-expand-hids-in-lines (lines mod)
    (declare (xargs :guard (and (true-list-listp lines)
                                (good-esim-modulep mod))))
    (b* (((when (atom lines))
          nil)
         (line1              (car lines))
         ((cons name phases) line1)
         ((unless (stringp name))
          (er hard? 'stv-expand-hids-in-lines
              "Internals line name is not a string: ~x0" name))
         (lsb-paths          (vl::stv-hid-to-paths name mod)))
      (cons (cons lsb-paths phases)
            (stv-expand-hids-in-lines (cdr lines) mod))))

  (local (in-theory (enable stv-expand-hids-in-lines)))

  (defthm alistp-of-stv-expand-hids-in-lines
    (alistp (stv-expand-hids-in-lines lines mod)))

  (defthm true-list-listp-of-stv-expand-hids-in-lines
    (implies (true-list-listp lines)
             (true-list-listp (stv-expand-hids-in-lines lines mod)))))


(defsection stv-expand-names
  :parents (stv-compile)
  :short "@(call stv-expand-names) simplifies a symbolic test vector by
expanding all of the names in its lines into explicit lists of bits."

  :long "<p>We do this as the second step in compiling an STV.  We could do
this before widening the phases, but widening first gives us potentially better
error messages.</p>"

  (defund stv-expand-names (stv mod)
    (declare (xargs :guard (and (basic-stv-p stv)
                                (good-esim-modulep mod))))
    (b* ((inputs           (cdr (hons-assoc-equal :inputs stv)))
         (outputs          (cdr (hons-assoc-equal :outputs stv)))
         (internals        (cdr (hons-assoc-equal :internals stv)))
         (expanded-inputs  (stv-expand-names-in-lines inputs :i mod))
         (expanded-outputs (stv-expand-names-in-lines outputs :o mod))
         (expanded-interns (stv-expand-hids-in-lines internals mod))
         (flat-in-bits     (flatten (strip-cars expanded-inputs)))
         (flat-out-bits    (flatten (strip-cars expanded-outputs)))
         ;; It's explicitly okay to have the same output bits repeated, because
         ;; you might want to for instance have one simulation variable that
         ;; refers to foo[127:0] and another variable for foo[63:0], etc.
         (dupes            (duplicated-members
                            (append flat-in-bits (sets::mergesort flat-out-bits))))
         ;; BOZO we could perhaps do more error checking on internals stuff
         (- (or (not dupes)
                (er hard? 'stv-expand-names
                    "After expanding wire names,there are multiple bindings ~
                     for some wires! ~x0."  dupes))))
      (list (cons :inputs    expanded-inputs)
            (cons :outputs   expanded-outputs)
            (cons :internals expanded-interns))))

  (local (in-theory (enable stv-expand-names)))

  (defthm basic-stv-p-of-stv-expand-names
    (implies (basic-stv-p stv)
             (basic-stv-p (stv-expand-names stv mod)))))






; -----------------------------------------------------------------------------
;
;                     EXPANDING INPUT PHASE ENTRIES
;
; -----------------------------------------------------------------------------

(defsection stv-expand-input-entry
  :parents (stv-expand-input-lines)
  :short "Convert an entry for a single input, at a single phase, into a list
of @(see 4v-sexprs)."

  :long "<p><b>Signature:</b> @(call stv-expand-input-entry) returns <tt>(mv
new-val gensyms usersyms)</tt>.</p>

<p>This function basically defines what each entry in the phase list means, by
transforming it into a list of @(see 4v-sexprs) that will be bound to the input
during this phase.  At a high level, our expansion strategy is as follows:</p>

<ul>

<li><b>NAT</b>.  Expands to a list of <tt>*4vt-sexpr*</tt> and
<tt>*4vf-sexpr*</tt>'s, in LSB order, of the appropriate width.</li>

<li><b>X</b>.  Expands to a list of <tt>*4vx-sexpr*</tt> of the appropriate
width.</li>

<li><b>:ONES</b>.  Expands to a list of <tt>*4vt-sexpr*</tt> of the appropriate
width.</li>

<li><b>~</b>.  Expands to a singleton list whose one entry is either
<tt>*4vf-sexpr*</tt> or <tt>*4vt-sexpr*</tt>, based on the previous value for
this signal.</li>

<li><b>_</b>.  Expands to a list of variables, whose names are derived from the
names of input bits for this line.  Basically, <tt>|foo[0]|</tt> gets turned
into <tt>|foo[0].P4|</tt> in the 4th phase, etc.  We collect these symbol names
so we can make sure there are no name collisions.</li>

<li><b>Simulation variables</b>.  A simulation variable like <tt>opcode</tt> is
turned into a list like <tt>(|opcode[0]| ... |opcode[n]|)</tt>.  We collect
these up to make sure they don't collide with generated variables for
<tt>_</tt>'s.</li>

</ul>

<p>To support this strategy, this function takes a number of inputs.</p>

<ul>

<li><tt>name</tt> is the name of this input.  We assume that the names have
already been expanded with @(see stv-expand-names), so <tt>name</tt> will be
a list of ESIM bits in LSB-first order.</li>

<li><tt>width</tt> is the pre-computed width of this input, i.e., it should
always be <tt>(len name)</tt>.</li>

<li><tt>pnum</tt> is the current phase number (starts at 0), so that we know
what suffix to put onto the variable names in the case of <tt>_</tt>
entries.</li>

<li><tt>entry</tt> is the actual entry we are trying to expand.  For instance,
it might be <tt>5</tt>, <tt>:ones</tt>, <tt>_</tt>, or whatever else the user
wrote for this input at this phase number.</li>

<li><tt>gensyms</tt> is a flat list of all the names we have generated so far
for <tt>_</tt> entries, which we may extend.  (This allows us to check for name
collisions later on).</li>

<li><tt>usersyms</tt> is a fast alist that binds the names of simulation
variables like <tt>opcode</tt> to lists of bits that we generate for these
symbols, i.e., <tt>(opcode[0] ... opcode[n])</tt>.  This allows us to check for
name collisions with generated symbols, and for width mismatches (i.e., all
uses of <tt>opcode</tt> had better go to inputs of the same width.</li>

<li><tt>prev-val</tt> is the sexpr list that this signal expanded to in the
previous phase, or NIL if this is the first phase of the simulation.  We use
this to figure out the new value of a <tt>~</tt> entry.</li>

</ul>"

  (defund stv-expand-input-entry (name width pnum entry gensyms usersyms prev-val)
    (declare (xargs :guard (and (symbol-listp name)
                                (consp name)
                                (natp pnum)
                                (equal width (len name)))))
    (b* (((when (natp entry))
          (or (< entry (ash 1 width))
              (er hard? 'stv-expand-input-entry
                  "Value ~x0 is too wide to fit in ~x1 bits (phase ~x2 for ~
                   input ~x3)."
                  entry width pnum name
                  (fast-alist-free usersyms)))
          (mv (bool-to-4v-sexpr-lst (int-to-v entry width)) gensyms usersyms))

         ((when (eq entry 'x))
          (mv (repeat *4vx-sexpr* width) gensyms usersyms))

         ((when (eq entry :ones))
          (mv (repeat *4vt-sexpr* width) gensyms usersyms))

         ((when (eq entry '~))
          (or (and (= width 1)
                   (or (equal prev-val (list *4vt-sexpr*))
                       (equal prev-val (list *4vf-sexpr*))))
              (er hard? 'stv-expand-input-entry
                  "Value ~~ is not legal in phase ~x0 for input ~x1; it can ~
                   only be used to invert one-bit wires whose previous value ~
                   expanded to a constant 1 or 0."
                  pnum name
                  (fast-alist-free usersyms)))
          (mv (if (equal prev-val (list *4vt-sexpr*))
                  (list *4vf-sexpr*)
                (list *4vt-sexpr*))
              gensyms usersyms))

         ((when (eq entry '_))
          (let ((my-syms (stv-suffix-symbols name (str::cat ".P" (str::natstr pnum)))))
            (mv my-syms
                (append my-syms gensyms)
                usersyms)))

         ((when (and (symbolp entry)
                     (not (keywordp entry))))
          (b* ((my-syms (vl::vl-emodwires-from-msb-to-lsb (symbol-name entry) 0 (- width 1)))
               (look    (hons-get entry usersyms)))
            (or (not look)
                (equal (cdr look) my-syms)
                (er hard? 'stv-expand-input-entry
                    "Variable ~x0 is ~x1 bits wide in phase ~x2 for input ~
                     ~x3, but it was ~x4 bits wide earlier."
                    entry width pnum name (len (cdr look))
                    (fast-alist-free usersyms)))
            (mv my-syms gensyms (if look
                                    usersyms
                                  (hons-acons entry my-syms usersyms))))))

      (er hard? 'stv-expand-input-entry
          "The value ~x0 is not a supported value for symbolic test vectors; ~
           it occurs in phase ~x1 for input ~x2."
          entry pnum name
          (fast-alist-free usersyms))
      (mv (repeat *4vx-sexpr* width) gensyms usersyms)))

  (local (in-theory (enable stv-expand-input-entry)))

  (defthm true-listp-of-stv-expand-input-entry-gensyms
    (implies (true-listp gensyms)
             (true-listp
              (mv-nth 1 (stv-expand-input-entry name width pnum entry gensyms
                                                usersyms prev-val))))))




(defsection stv-expand-input-entries
  :parents (stv-expand-input-lines)
  :short "Convert all of the entries in a single input lines into lists of
@(see 4v-sexprs) of the appropriate width."

  :long "<p>See @(see stv-expand-input-entry).  This just calls it only each
entry in a line, while appropriately updating the phase number, previous value,
and accumulators.</p>"

  (defund stv-expand-input-entries (name width pnum entries gensyms usersyms prev-val)
    "Returns (MV NEW-ENTRIES GENSYMS USERSYMS)"
    (declare (xargs :guard (and (symbol-listp name)
                                (consp name)
                                (natp pnum)
                                (equal width (len name))
                                (true-listp entries))))
    (b* (((when (atom entries))
          (mv nil gensyms usersyms))
         ((mv new-car gensyms usersyms)
          (stv-expand-input-entry name width pnum (car entries)
                                  gensyms usersyms prev-val))
         ((mv new-cdr gensyms usersyms)
          (stv-expand-input-entries name width (+ 1 pnum) (cdr entries)
                                    gensyms usersyms new-car)))
      (mv (cons new-car new-cdr) gensyms usersyms)))

  (local (in-theory (enable stv-expand-input-entries)))

  (defthm true-listp-of-stv-expand-input-entries-gensyms
    (implies (true-listp gensyms)
             (true-listp
              (mv-nth 1 (stv-expand-input-entries name width pnum entries gensyms
                                                  usersyms prev-val))))))


(defsection stv-expand-input-lines
  :parents (stv-compile)
  :short "Converts all the phase entries in the input lines into lists of @(see
4v-sexprs) of the appropriate widths."

  :long "<p>See @(see stv-expand-input-entry).  This just calls it on all of
the entries in all of the input lines.</p>"

  (defund stv-expand-input-lines (lines gensyms usersyms)
    "Returns (MV NEW-LINES GENSYMS USERSYMS)"
    (declare (xargs :guard (true-list-listp lines)
                    :guard-debug t))
    (b* (((when (atom lines))
          (mv nil gensyms usersyms))
         (line1 (car lines))
         ((cons name1 entries1) line1)

         ((unless (and (consp name1)
                       (symbol-listp name1)))
          (fast-alist-free usersyms)
          (er hard? 'stv-expand-input-lines
              "Expected all input line names to be already expanded to ~
             non-empty symbol lists, but found ~x0." name1)
          (mv nil gensyms usersyms))

         ((mv new-entries1 gensyms usersyms)
          (stv-expand-input-entries name1 (len name1) 0 entries1 gensyms usersyms nil))
         (new-car (cons name1 new-entries1))
         ((mv new-cdr gensyms usersyms)
          (stv-expand-input-lines (cdr lines) gensyms usersyms)))
      (mv (cons new-car new-cdr) gensyms usersyms)))

  (local (in-theory (enable stv-expand-input-lines)))

  (defmvtypes stv-expand-input-lines (true-listp nil nil))

  (defthm true-listp-of-stv-expand-input-lines-gensyms
    (implies (true-listp gensyms)
             (true-listp (mv-nth 1 (stv-expand-input-lines lines gensyms usersyms))))))





; -----------------------------------------------------------------------------
;
;                     EXPANDING OUTPUT PHASE ENTRIES
;
; -----------------------------------------------------------------------------

(defsection stv-expand-output-entry
  :parents (stv-expand-output-lines)
  :short "Convert an entry for a single output, at a single phase, into a list
of @(see 4v-sexprs) or NIL."

  :long "<p><b>Signature:</b> @(call stv-expand-output-entry) returns <tt>(mv
new-val usersyms)</tt>.</p>

<p>Output lines are much simpler than input lines, in that the only valid
entries are <tt>_</tt> and unique simulation variables.</p>

<p>An entry of <tt>_</tt> means the user doesn't care about the output at this
phase and doesn't want to extract its value.  In this function, we just leave
these alone.</p>

<p>But if a simulation variable is provided, it means we want to extract the
output's value during this phase and give it a name.  We treat this situation
similarly to that of simulation variables in input lines, by expanding the
variable into an explicit list of bits that we generate for the simulation
variable.</p>

<p>As inputs, we are given:</p>

<ul>

<li><tt>name</tt>, the name of this output; we assume that @(see
stv-expand-names) has already been applied so that the name is a list of ESIM
bits in LSB-first order.</li>

<li><tt>width</tt>, the pre-computed width of this input, i.e., this should
always just be <tt>(len name)</tt>.</li>

<li><tt>pnum</tt>, the current phase number (starts at 0); this is only used
in error reporting.</li>

<li><tt>entry</tt>, the actual entry we are trying to expand.  It should
be either <tt>_</tt> or a simulation variable, but we need to check that it is
one of these since it's provided by the user.</li>

<li><tt>usersyms</tt>, a fast alist binding simulation variables to the
lists of bits that we've generated to represent them.  We assume this only
contains the output simulation variables.</li>

</ul>"

  (defund stv-expand-output-entry (name width pnum entry usersyms)
    "Returns (MV NEW-VAL USERSYMS)"
    (declare (xargs :guard (and (true-listp name)
                                (consp name)
                                (natp pnum)
                                (equal width (len name)))))
    (b* (((when (or (natp entry)
                    (eq entry 'x)
                    (eq entry '~)
                    (keywordp entry)
                    (not (symbolp entry))))
          (fast-alist-free usersyms)
          (er hard? 'stv-expand-output-entry
              "Value ~x0 is not allowed in output lines of symbolic test ~
               vectors, but occurs at phase ~x1 for output ~x2."
              entry pnum name)
          (mv nil usersyms))

       ((when (eq entry '_))
        ;; That's fine, just leave it alone.
        (mv entry usersyms))

       ;; Else, a simulation variable.  It had better not be used yet.
       (look (hons-get entry usersyms))
       ((when look)
        (fast-alist-free usersyms)
        (er hard? 'stv-expand-output-entry
            "Variables used in output symbols must be unique, but ~x0 was ~
             already used before we got to phase ~x1 for output ~x2."
            entry pnum name)
        (mv nil usersyms))

       ;; Okay it wasn't used.  Make its symbols and such.
       (my-syms  (vl::vl-emodwires-from-msb-to-lsb (symbol-name entry) 0 (- width 1)))
       (usersyms (hons-acons entry my-syms usersyms)))
    (mv my-syms usersyms))))

(defsection stv-expand-output-lines
  :parents (stv-compile)
  :short "Converts all the simulation variables in the output lines into lists
of user-variable bits of the appropriate widths."

  :long "<p>See @(see stv-expand-output-entry).  This just calls it on all of
the entries in all of the output lines.</p>"

  (defund stv-expand-output-entries (name width pnum entries usersyms)
    "Returns (MV NEW-ENTRIES USERSYMS)"
    (declare (xargs :guard (and (true-listp name)
                                (consp name)
                                (natp pnum)
                                (equal width (len name))
                                (true-listp entries))))
    (b* (((when (atom entries))
          (mv nil usersyms))
         ((mv new-car usersyms)
          (stv-expand-output-entry name width pnum (car entries) usersyms))
         ((mv new-cdr usersyms)
          (stv-expand-output-entries name width (+ 1 pnum) (cdr entries) usersyms)))
      (mv (cons new-car new-cdr) usersyms)))

  (defund stv-expand-output-lines (lines usersyms)
    "Returns (MV NEW-LINES USERSYMS)"
    (declare (xargs :guard (true-list-listp lines)
                    :guard-debug t))
    (b* (((when (atom lines))
          (mv nil usersyms))
         (line1 (car lines))
         ((cons name1 entries1) line1)

         ((unless (and (consp name1)
                       (true-listp name1)))
          (fast-alist-free usersyms)
          (er hard? 'stv-expand-output-lines
              "Expected all output line names to be already expanded to ~
               non-empty lists, but found ~x0." name1)
          (mv nil usersyms))

         ((mv new-entries1 usersyms)
          (stv-expand-output-entries name1 (len name1) 0 entries1 usersyms))

         (new-car (cons name1 new-entries1))
         ((mv new-cdr usersyms)
          (stv-expand-output-lines (cdr lines) usersyms)))
      (mv (cons new-car new-cdr) usersyms))))




; -----------------------------------------------------------------------------
;
;                       CREATING THE SPECIALIZING ALIST
;
; -----------------------------------------------------------------------------

(defsection stv-restrict-alist
  :parents (stv-compile)
  :short "Construct an alist binding fully-general input names (for all phases)
to @(see 4v-sexprs) derived from the symbolic test vector."

  :long "<p>@(call stv-restrict-alist) is given <tt>lines</tt>, the input lines
from a symbolic test vector that have:</p>

<ul>
 <li>Already been widened with @(see stv-widen),</li>
 <li>Already had their names expanded with @(see stv-expand-names), and</li>
 <li>Already had their entries expanded with @(see stv-expand-input-lines).</li>
</ul>

<p>and it is also given <tt>acc</tt>, an alist to extend.</p>

<p>It constructs an ordinary (slow) alist that binds the input names we are
going to use in our fully-general simulation to their bindings according to the
symbolic test vector.  This is a single alist that includes the bindings for
the variables at all phases.</p>

<p>The sexprs in this alist will often be constants (e.g., when natural
numbers, <tt>:ones</tt>, <tt>x</tt>, or <tt>~</tt> values are used), but they
can also have free variables from <tt>_</tt> symbols and also simulation
variable bits.</p>

<p>The general intent is to make the resulting alist fast, and use it along
with @(see 4v-sexpr-restrict) to specialize the fully general simulation,
effectively \"assuming\" the STV.</p>"

  (defund stv-restrict-alist-aux (name phase entries acc)
    (declare (xargs :guard (and (symbol-listp name)
                                (natp phase))))
    (b* (((when (atom entries))
          acc)
         (name-at-phase (stv-suffix-symbols name (str::cat ".P" (str::natstr phase))))
         (val-at-phase  (car entries))
         (acc           (safe-pairlis-onto-acc name-at-phase val-at-phase acc)))
      (stv-restrict-alist-aux name (+ 1 phase) (cdr entries) acc)))

  (defund stv-restrict-alist (lines acc)
    (declare (xargs :guard (true-list-listp lines)))
    (b* (((when (atom lines))
          acc)
         (line1 (car lines))
         ((cons name entries) line1)
         ((unless (symbol-listp name))
          (er hard? 'stv-restrict-alist "name should be a symbol list, but is ~x0." name))
         (acc (stv-restrict-alist-aux name 0 entries acc)))
      (stv-restrict-alist (cdr lines) acc))))



; -----------------------------------------------------------------------------
;
;                     CREATING THE EXTRACTION ALISTS
;
; -----------------------------------------------------------------------------

(defsection stv-extraction-alists
  :parents (stv-compile)
  :short "Alists explaining what signals we want to extract from the simulation
after each phase."

  :long "<p>@(call stv-extraction-alists) takes the total number of phases, the
output lines (which we assume have already been expanded with @(see
stv-expand-output-lines), and an accumulator which should initially be
<tt>nil</tt>.</p>

<p>It returns a list of alists that say, after each step, which output bits we
want to collect, and how we want to name them.  The basic idea is that if we have
a list of outputs like this:</p>

<code>
   (foo  _ _ a _)
   (bar  _ b _ c)
   (baz  _ _ d _)
</code>

<p>Then we will want to create four alists, one for each phase.  The P0 alist
is empty.  The P1 alist binds something like</p>

<code>
   ((bar[0] . b[0])
    (bar[1] . b[1])
    ...
    (bar[n] . b[n]))
</code>

<p>The P2 alist binds something like:</p>

<code>
 ((foo[0] . a[0])
   ...
  (foo[n] . a[n])
  (baz[0] . d[0])
   ...
  (baz[0] . d[k]))
</code>

<p>And so on.  That is, each of these extraction alists says, for a particular
phase, the names of the output signals we want to extract from the simulation,
and which bit of which simulation variable the name corresponds to.</p>"

  (defund stv-nth-extraction-alist (n lines nth-alist-acc)
    "Lines are (name entry1 ... entryK)
     Add the bindings for name to entryN to the NTH-ALIST-ACC"
    (declare (xargs :guard (and (natp n)
                                (true-list-listp lines))))
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

  (defund stv-extraction-alists (n lines alists-acc)
    "N counts down from the max phase to zero.  Lines are constant.
     We return the list of binding alists, in the proper phase order."
    (declare (xargs :guard (and (natp n)
                                (true-list-listp lines))))
    (let* ((nth-alist  (stv-nth-extraction-alist n lines nil))
           (alists-acc (cons nth-alist alists-acc)))
      (if (zp n)
          alists-acc
        (stv-extraction-alists (- n 1) lines alists-acc)))))



; -----------------------------------------------------------------------------
;
;                         TOP-LEVEL STV COMPILATION
;
; -----------------------------------------------------------------------------

(cutil::defaggregate compiled-stv
  (nphases            ;; number of phases for this simulation
   expanded-ins       ;; fully expanded stv lines
   expanded-outs      ;; fully expanded stv lines
   expanded-ints      ;; fully expanded stv lines
   out-extract-alists ;; what to extract at times 0...N from outputs
   int-extract-alists ;; what to extract at times 0...N from internals
   restrict-alist     ;; (input-bit@phase -> sexpr) alist
   in-usersyms        ;; (simulation var -> bit list) alist
   out-usersyms       ;; (simulation var -> bit list) alist for OUTS+INTS
   )
  :tag :compiled-stv
  :parents (stv-compile)
  :short "Compiled form of @(see symbolic-test-vectors).")

(defund stv-compile (stv mod)
  (declare (xargs :guard t
                  :guard-debug t))

  (b* (((unless (basic-stv-p stv))
        (er hard? 'stv-compile
            "Alleged symbolic test vector ~x0 does not even satisfy basic-stv-p."
            stv))
       ((unless (good-esim-modulep mod))
        (er hard? 'stv-compile "The module is not a good-esim-modulep"))

       ;; Syntactic transforms, turn names into E bits, widen all phases entry
       ;; lists to the same length.
       (stv (stv-widen stv))
       (stv (stv-expand-names stv mod))
       (nphases (stv-number-of-phases stv))

       (inputs    (cdr (hons-assoc-equal :inputs stv)))
       (outputs   (cdr (hons-assoc-equal :outputs stv)))
       (internals (cdr (hons-assoc-equal :internals stv)))

       ;; Convert the input phase entries into sexpr lists and make the binding
       ;; alist to use to specialize the fully general simulation.
       ((mv inputs gensyms in-usersyms)
        (ec-call (stv-expand-input-lines inputs nil nil)))
       (restrict-alist
        (make-fast-alist (ec-call (stv-restrict-alist inputs nil))))

       ;; Convert the output entries into variable bit lists, put together the
       ;; extraction alists.
       ((mv outputs out-usersyms)
        (ec-call (stv-expand-output-lines outputs nil)))
       (out-extract-alists
        (ec-call (stv-extraction-alists (- nphases 1) outputs nil)))

       ;; Internal lines are basically the same as outputs as far as extraction
       ;; goes.  We build a unified usersyms alist, which forbids name clashes
       ;; between their bits.
       ((mv internals out-usersyms)
        (ec-call (stv-expand-output-lines internals out-usersyms)))
       (int-extract-alists
        (ec-call (stv-extraction-alists (- nphases 1) internals nil)))

       ;; Sanity checks for name collisions.
       (in-names  (alist-keys in-usersyms))
       (out-names (alist-keys out-usersyms))
       ((unless (uniquep (append in-names out-names)))
        (er hard? 'stv-compile
            "Names of inputs, outputs, and internal simulation variables must be ~
             distinct.  Illegally reused names: ~x0"
            (duplicated-members (append in-names out-names))))

       (all-bits    (vl::append-domains-exec in-usersyms gensyms))
       (all-bits    (vl::append-domains-exec out-usersyms all-bits))
       ((unless (uniquep all-bits))
        (er hard? 'stv-compile
            "Name clash for ~x0." (duplicated-members all-bits))))

    (make-compiled-stv :nphases        nphases
                       :expanded-ins   inputs
                       :expanded-outs  outputs
                       :expanded-ints  internals
                       ;; These have to stay separate because we have to use them
                       ;; to extract from different esim outputs
                       :out-extract-alists out-extract-alists
                       :int-extract-alists int-extract-alists
                       :restrict-alist restrict-alist
                       :in-usersyms    in-usersyms
                       :out-usersyms   out-usersyms)))

;; Compilation isn't necessarily slow, but memoizing it seems like a good
;; idea to make sure that all of the alists stay the same.
(memoize 'stv-compile)

(defthm compiled-stv-p-of-stv-compile
  (equal (compiled-stv-p (stv-compile stv mod))
         (if (stv-compile stv mod)
             t
           nil))
  :hints(("Goal" :in-theory (enable stv-compile))))