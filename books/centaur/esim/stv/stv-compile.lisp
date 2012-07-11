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


; stv-compile.lisp -- compile a symbolic test vector into a compiled-stv that
; explains how to run an ESIM module over time
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "../esim-sexpr-support")
(include-book "../follow-backwards")
(include-book "centaur/misc/vecs-ints" :dir :system)
(include-book "centaur/misc/tuplep" :dir :system)
(include-book "cutil/defmvtypes" :dir :system)
(include-book "cutil/defprojection" :dir :system)
(include-book "str/natstr" :dir :system)
(include-book "unicode/final-cdr" :dir :system)
(include-book "centaur/vl/util/defs" :dir :system)
(local (include-book "../esim-sexpr-support-thms"))
(local (include-book "centaur/vl/util/arithmetic" :dir :system))


(local (defthm atom-listp-of-append
         (implies (and (atom-listp x)
                       (atom-listp y))
                  (atom-listp (append x y)))
         :hints(("Goal" :in-theory (disable (force))))))

(local (defthm atom-listp-of-pat-flatten1
         (atom-listp (pat-flatten1 x))
         :hints(("Goal" :in-theory (e/d (pat-flatten1)
                                        ((force)))))))

(local (defthm alist-keys-of-pairlis$
         (equal (alist-keys (pairlis$ x y))
                (list-fix x))
         :hints(("Goal" :in-theory (enable pairlis$)))))

(local (defthm consp-when-member-of-atom-listp
         (implies (and (atom-listp x)
                       (member-equal a x))
                  (equal (consp a)
                         nil))))

(local (defthm atom-listp-when-subsetp
         (implies (and (subsetp x y)
                       (atom-listp y))
                  (equal (atom-listp x)
                         (true-listp x)))
         :hints(("Goal" :induct (len x)))))


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


(defsection stv-gensyms
  :parents (stv-compile)
  :short "@(call stv-gensyms) produces the list of symbols <tt>(prefix[0]
  ... prefix[n-1])</tt>."

  ;; I originally used VL's emodwire stuff for this, but it's nice to eliminate
  ;; that dependency and just generate our own symbols.

  (defund stv-gensyms-aux (prefix n acc)
    (declare (xargs :guard (and (stringp prefix)
                                (natp n))))
    (b* (((when (zp n))
          acc)
         (n     (- n 1))
         (sym1  (intern$ (str::cat prefix "[" (str::natstr n) "]") "ACL2")))
      (stv-gensyms-aux prefix n (cons sym1 acc))))

  (defun stv-gensyms (prefix n)
    "Enumerate (prefix[0] ... prefix[n-1])"
    (declare (xargs :guard (and (stringp prefix)
                                (natp n))))
    (stv-gensyms-aux prefix n nil)))





; -----------------------------------------------------------------------------
;
;              COMPILING :INITIAL LINES INTO A 4V-SEXPR-ALIST
;
; -----------------------------------------------------------------------------

; The basic goal here *sounds* really easy: I want to let the user write down
; names of Verilog regs, e.g., "foo.bar.baz.myreg[2:0]", and then somehow
; figure out what E state bits correspond to this register.
;
; I've wrestled with this before, e.g., for "design registers."  But really I'd
; like to get away from design registers.  They are sort of always getting
; broken (when we change around how flop/latch inference stuff works), and
; that's really irritating.  And EMAPs are really big/slow/awful when we get to
; large modules.
;
; Can't we just use something like the ordinary path stuff (from stv-expand)?
; After all, this path stuff is great: it keeps everything strictly at the
; Verilog level and uses only the information that's already embedded in the
; module to resolve the paths.
;
; Well, there are a couple of things that make this hard.
;
; A minor problem is that latches just have one E bit, but flops need two state
; bits.  This means there isn't a nice, direct correspondence between a Verilog
; "reg" bit and an E state bit.  But let's not worry about this yet.
;
; A harder problem is that, at least with the current flop inference stuff, the
; E state bits aren't really "directly connected" to wire that arises from the
; Verilog reg.  That is, if a Verilog module has a flop like:
;
;     always @(posedge clk) q <= d;
;
; Then the transformed module will have something like:
;
;     wire [n-1:0] q_temp_rhs = d;
;     wire [n-1:0] q_temp_lhs;
;     VL_N_BIT_LATCH guts (q_temp_lhs, q_temp_rhs, clk);
;     wire [n-1:0] q = q_temp_lhs;
;
; Notice here that the VL_N_BIT_LATCH, where the E state bits live, isn't
; driving Q; it's driving this other temporary wire instead.  There are good
; reasons for it to work this way (e.g., it lets us handle delays and
; truncations).  But if we want to let users write things like
; "foo.bar.baz.myreg.q", then we'll have to deal with this.
;
; I have come up with, I think, a very nice solution to this whole mess.  This
; solution "automatically" deals with things like the q = q_temp_lhs stuff,
; without any special knowledge of how latch/flop inference works.  This should
; be very helpful when we want to change and extend our support for always
; blocks.  An even nicer, extremely neat thing is that the solution also lets
; you refer to state bits in an even *less* direct way.
;
; To explain what I mean and why it is so good, consider a high-level module
; that contains a module instance such as:
;
;     // stage A signals to B...
;     myreg #(10) stageSignalsB (.q({ foo_B[5:0], bar_B, baz_B[2:0] }),
;                                .d({ foo_A[5:0], bar_A, baz_A[2:0] }),
;                                .clk(clk), .en1(en1), .en2(en2), ...);
;
; If I just gave you a way to refer to actual Verilog regs, it'd still be a
; pain in the ass to initialize these state bits.  Suppose you wanted to
; initialize bar_B to some particular value.  The actual "reg" for bar_B is
; somewhere inside of myreg, so you'd have to write something like:
;
;     top.sub1.sub2.stageSignalsB.q[3], or
;     top.sub1.sub2.stageSignalsB.guts.q[3], or similar.
;
; This is awful: you'll have to update the index every time a logic designer
; adds something to the register or moves these wires around.  The basic point
; is: it'd be really nice to be able to refer to this state bit using the name
; top.sub1.sub2.bar_B, instead of the name of some Verilog reg, and my solution
; lets us do this!
;
; The solution is simple once we have a tool that lets us linearly follow a
; path backwards through an E module to its "real" driver.  This is pretty
; tricky, but the tool has other uses as well.  See follow-backwards.lisp for
; the details.
;
; With this code in place, we can do something pretty elegant: Given a path
; that the user says refers to a state bit, first follow it back to where it
; originates.  If it's a flop or a latch, we win: we have figured out what
; state bit they're talking about, and we even know whether we should invert
; it.  Otherwise, we'll just cause an error because the user is trying to
; initialize things that aren't very simply connected up to state bits, and
; that's either crazy or just beyond the scope of what I want to think about
; supporting.

(defsection stv-forge-state-bit
  :parents (stv-compile)
  :short "Generate the name for a state bit, like <tt>foo!bar!baz!inst!S</tt>,
given a list of instance names and the name of the state bit."

  ;; BOZO have to keep this in sync with mod-state/occ-state

  (defund stv-forge-state-bit (instnames st-name)
    (declare (xargs :guard (atom st-name)))
    (if (atom instnames)
        st-name
      (acl2::prefix-atom (acl2::stringify (car instnames))
                         "!"
                         (stv-forge-state-bit (cdr instnames) st-name))))

  (local (in-theory (enable stv-forge-state-bit)))

  (defthm atom-of-stv-forge-state-bit
    (implies (atom st-name)
             (atom (stv-forge-state-bit instnames st-name)))))


(cutil::defprojection stv-forge-state-bits (instnames x)
  (stv-forge-state-bit instnames x)
  :guard (atom-listp x)
  :result-type atom-listp)





(defsection stv-initial-line-binding
  :parents (stv-compile)
  :short "Find the state bit(s) associated with some path and bind them to
their initial values."

  :long "<p><b>Signature:</b> @(call stv-initial-line-binding) returns a sexpr
alist.</p>

<p>The <tt>path</tt> is any path into <tt>mod</tt>.  It need not be canonical.
We will follow the path with @(see follow-path-backwards), and we expect that
new path we arrive at will be either an @(see *esim-flop*) or to an @(see
*esim-latch*).  If not, we cause a run-time error.</p>

<p>The <tt>sexpr</tt> is a sexpr that we want to use as the initial value for
<tt>path</tt>.  The basic idea is to bind <tt>sexpr</tt> to the state bits we
have found.  A slight twist is that, if walking from <tt>path</tt> to the state
bits took us through an inversion, then we will bind the state bits to <tt>(not
sexpr)</tt> instead.  This should ensure that our initial bindings to state
bits do indeed initialize <tt>path</tt> to the desired value.</p>

<p>If the path leads to a latch then there is just one state bit, and our alist
will contain only a single entry.</p>

<p>If the path leads to a flop, then there are two state bits!  <b>BOZO</b> for
now, we initialize <b>BOTH</b> state bits together.  This shouldn't cause any
problems until we want to compose together different STV runs.  To support
composition, we'll probably want an extended syntax that lets you specify
whether the master or slave bit gets initialized.</p>"

  (defund stv-initial-line-binding (path sexpr mod)
    (declare (xargs :guard (good-esim-modulep mod)))
    (b* (((mv new-path invp) (follow-path-backwards path mod))
         (instnames          (list-fix new-path))
         (wirename           (final-cdr new-path))
         (submod             (follow-esim-path instnames mod))
         ((unless submod)
          (er hard? 'stv-initial-line-binding
              "Error creating :initial binding for ~x0.  We followed the path ~
               backward to ~x1, but this path doesn't seem valid?" path new-path))

         ;; Basic sanity check to make sure that the path leads to a flop/latch.
         (name (gpl :n submod))
         ((unless (or (eq name 'acl2::*esim-latch*)
                      (eq name 'acl2::*esim-flop*)))
          ;; BOZO I'm just using a name-based check to see if we're at a flop
          ;; or a latch.  Is this okay?  Should we do something deeper?
          (er hard? 'stv-initial-line-binding
              "Error creating :initial binding for ~x0.  We followed the path ~
               backward to ~x1.  We expected this to be a latch or flop, but ~
               instead it is a ~x2 module." path new-path name))

         ((unless (eq wirename 'acl2::|q|))
          ;; Probably silly sanity check.  This may be of no use.  If it ever
          ;; fails, it might indicate that our flop/latch format has changed.
          (er hard? 'stv-initial-line-binding
              "Error creating :initial binding for ~x0.  We followed the path ~
               backward to ~x1, and found a flop/latch whose output isn't ~
               even named acl2::|q|: ~x2?" path new-path wirename))

         (ebits
          ;; Gross way to come up with the actual state bits we want.  Note
          ;; that the PAT-FLATTEN1 here is quite cheap: the submod is a latch
          ;; or a flop, so its mod-state is just one or two bits.
          (stv-forge-state-bits instnames (pat-flatten1 (mod-state submod))))
         (nbits (length ebits))

         ((unless (or (and (eq name 'acl2::*esim-latch*) (= nbits 1))
                      (and (eq name 'acl2::*esim-flop*) (= nbits 2))))
          ;; Cheap, very trivial sanity check.  This could save us if we do
          ;; something to the representation of latches/flops.
          (er hard? 'stv-initial-line-binding
              "Error creating :initial binding for ~x0.  Wrong number of bits ~
               for flop/latch?  The new-path is ~x1 and alleged ebits are ~x2."
              path new-path ebits))

         ((unless (subsetp-of-pat-flatten ebits (mod-state mod)))
          ;; Cheap, good sanity check to make sure that we've actually
          ;; identified state bits.  Note that EBITS is only going to be one or
          ;; two bits, so even though this is O(n^2), N is very small.  This
          ;; should save us from disaster if our naming conventions change.
          (er hard? 'stv-path-to-statepath
              "Error creating :initial binding for ~x0.  Something has gone ~
               horribly wrong. The new-path, ~x1, seems to point to a valid ~
               flop/latch.  But the bits we generated, ~x2, aren't in the ~
               mod-state for the module?" path new-path ebits))

         ;; Everything looks good, we got the right number of state bits,
         ;; checked that they exist, etc.  Make the bindings.  We invert the
         ;; sexpr if the path is inverting, so that the value on PATH will be
         ;; what the user asked for.
         (sexpr (if invp
                    (hons-list 'acl2::not sexpr)
                  sexpr))
         (vals  (repeat sexpr nbits)))
      (pairlis$ ebits vals)))

  (local (in-theory (enable stv-initial-line-binding)))

  (defthm alistp-of-stv-initial-line-binding
    (alistp (stv-initial-line-binding path sexpr mod)))

  (defthm keys-of-stv-initial-line-binding-are-states
    (subsetp-equal (alist-keys (stv-initial-line-binding path sexpr mod))
                   (pat-flatten1 (mod-state mod)))))


(defsection stv-initial-line-bindings-aux
  :parents (stv-compile)
  :short "Extends @(see stv-initial-line-binding) to path/sexpr lists."

  (defund stv-initial-line-bindings-aux (paths sexprs mod)
    (declare (xargs :guard (and (equal (len paths) (len sexprs))
                                (good-esim-modulep mod))))
    (if (atom paths)
        nil
      (append (stv-initial-line-binding (car paths) (car sexprs) mod)
              (stv-initial-line-bindings-aux (cdr paths) (cdr sexprs) mod))))

  (local (in-theory (enable stv-initial-line-bindings-aux)))
  (local (in-theory (disable (force))))

  (defthm alistp-of-stv-initial-line-bindings-aux
    (alistp (stv-initial-line-bindings-aux path sexpr mod)))

  (defthm keys-of-stv-initial-line-bindings-aux-are-states
    (subsetp-equal (alist-keys (stv-initial-line-bindings-aux path sexpr mod))
                   (pat-flatten1 (mod-state mod)))))


(defsection stv-initial-line-bindings
  :parents (stv-compile)
  :short "Convert an :initial line into an alist binding state bits to sexprs."

  :long "<p><b>Signature:</b> @(call stv-initial-line-bindings) returns <tt>(mv
bindings usersyms)</tt>.</p>

<p>The <tt>line</tt> is an :initial line from the STV.  Note that its name
should be a list of E paths in lsb-first order.  That is, Verilog-style names
shoudl have already been expanded away using @(see stv-expand-names) or
similar.  These paths don't need to be canonical, and they don't need to refer
to state bits.  We'll walk back from them to find the associated latch/flop
that drives them.</p>

<p><tt>usersyms</tt> is a fast alist that binds the names of simulation
variables like <tt>opcode</tt> to lists of bits that we generate for these
symbols, i.e., <tt>(opcode[0] ... opcode[n])</tt>.  This allows us to check for
name collisions with generated symbols and width mismatches.  That is, we will
allow the same variable to be given to multiple inputs at multiple phases, but
for that to be sensible these inputs had better have the same width.</p>

<p>The <tt>mod</tt> is needed to do various path lookups.</p>"

  (local (defthm len-of-bool-to-4v-sexpr-lst
           (equal (len (bool-to-4v-sexpr-lst x))
                  (len x))))

  (local (defthm len-of-stv-gensyms-aux
           (equal (len (stv-gensyms-aux prefix n acc))
                  (+ (len acc) (nfix n)))
           :hints(("Goal" :in-theory (enable stv-gensyms-aux)))))

  (defund stv-initial-line-bindings (line usersyms mod)
    "Returns (MV BINDINGS USERSYMS)"
    (declare (xargs :guard (good-esim-modulep mod)))
    (b* (((unless (tuplep 2 line))
          (er hard? 'stv-initial-line-bindings
              "An :initial line must have the form (name value), so this line ~
               is not valid: ~x0." line)
          (mv nil usersyms))

         ((list paths entry) line)

         ((unless (and (consp paths)
                       (true-listp paths)))
          (er hard? 'stv-initial-line-bindings
              "Expected all :initial line names to be already expanded to ~
               non-empty path lists, but found ~x0." paths)
          (mv nil usersyms))

         (width (length paths))

         ((when (eq entry '_))
          ;; Special case: we'll allow blanks, but generate no bindings for them.
          (mv nil usersyms))

         ((mv sexprs usersyms)
          (b* (((when (natp entry))
                (or (< entry (ash 1 width))
                    (er hard? 'stv-initial-line-bindings
                        "At :initial line for ~x0: value ~x1 is too wide to ~
                         fit into ~x2 bits!" paths entry width))
                (mv (bool-to-4v-sexpr-lst (int-to-v entry width)) usersyms))

               ((when (eq entry 'x))
                (mv (repeat *4vx-sexpr* width) usersyms))

               ((when (eq entry :ones))
                (mv (repeat *4vt-sexpr* width) usersyms))

               ((when (or (eq entry '~)
                          (keywordp entry)
                          (not (symbolp entry))))
                (er hard? 'stv-initial-line-bindings
                    "At :initial line for ~x0: value ~x1 is not allowed in ~
                     :initial lines." paths entry)
                (mv (repeat *4vx-sexpr* width) usersyms))

               (my-syms (stv-gensyms (symbol-name entry) width))
               (look    (hons-get entry usersyms)))

            (or (not look)
                (equal (cdr look) my-syms)
                (er hard? 'stv-expand-input-entry
                    "At :initial line for ~x0: variable ~x1 cannot be used ~
                     here.  This input is ~x2 bits wide, but ~x1 was ~
                     previously used for a ~x3-bit input."
                    paths entry width (len (cdr look))))

            (mv my-syms (if look
                            usersyms
                          (hons-acons entry my-syms usersyms)))))

         (bindings (stv-initial-line-bindings-aux paths sexprs mod)))
      (mv bindings usersyms)))

  (local (in-theory (enable stv-initial-line-bindings)))

  (defmvtypes stv-initial-line-bindings (true-listp nil))

  (defthm alistp-of-stv-initial-line-bindings
    (b* ((ret (stv-initial-line-bindings line usersyms mod)))
      (alistp (mv-nth 0 ret))))

  (defthm keys-of-stv-initial-line-bindings-are-states
    (let ((ret (stv-initial-line-bindings line usersyms mod)))
      (subsetp-equal (alist-keys (mv-nth 0 ret))
                     (pat-flatten1 (mod-state mod))))))


(defsection stv-initial-lines-to-alist
  :parents (stv-compile)
  :short "Extend @(see stv-initial-line-bindings) across all the :initial lines."

  (defund stv-initial-lines-to-alist (lines usersyms mod)
    "Returns (MV BINDINGS USERSYMS)"
    (declare (xargs :guard (good-esim-modulep mod)))
    (b* (((when (atom lines))
          (mv nil usersyms))
         ((mv bindings1 usersyms) (stv-initial-line-bindings (car lines) usersyms mod))
         ((mv bindings2 usersyms) (stv-initial-lines-to-alist (cdr lines) usersyms mod)))
      (mv (append bindings1 bindings2) usersyms)))

  (local (in-theory (disable (force))))
  (local (in-theory (enable stv-initial-lines-to-alist)))

  (defmvtypes stv-initial-lines-to-alist (true-listp nil))

  (defthm alistp-of-stv-initial-lines-to-alist
    (b* ((ret (stv-initial-lines-to-alist lines usersyms mod)))
      (alistp (mv-nth 0 ret))))

  (defthm keys-of-stv-initial-lines-to-alist-are-states
    (let ((ret (stv-initial-lines-to-alist lines usersyms mod)))
      (subsetp-equal (alist-keys (mv-nth 0 ret))
                     (pat-flatten1 (mod-state mod)))))

  (defthm atom-listp-of-alist-keys-of-stv-initial-lines-to-alist
    (let ((ret (stv-initial-lines-to-alist lines usersyms mod)))
      (atom-listp (alist-keys (mv-nth 0 ret))))
    :hints(("Goal"
            :in-theory (disable stv-initial-lines-to-alist
                                keys-of-stv-initial-lines-to-alist-are-states)
            :use ((:instance keys-of-stv-initial-lines-to-alist-are-states))))))



(defsection stv-add-suffixes-to-initial-alist
  :parents (stv-compile)
  :short "Add .INIT suffixes to the state bits so that they can't clash with
input signal names."

  (defund stv-add-suffixes-to-initial-alist (x)
    (declare (xargs :guard (atom-listp (alist-keys x))))
    (b* ((keys (alist-keys x))
         (vals (alist-vals x))
         (keys.INIT (stv-suffix-signals keys ".INIT")))
      (pairlis$ keys.INIT vals))))

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
;                COMPILING :INPUT LINE VALUES INTO 4V-SEXPRS
;
; -----------------------------------------------------------------------------

(defsection stv-expand-input-entry
  :parents (stv-compile)
  :short "Convert a single user-level input value (e.g., 17, X, abus, etc) into
a list of @(see 4v-sexprs)."

  :long "<p><b>Signature:</b> @(call stv-expand-input-entry) returns <tt>(mv
new-val gensyms usersyms)</tt>.</p>

<p>This function basically defines what each value in an :input line means.  We
transform each such value into a list of @(see 4v-sexprs).  These are the
sexprs that will be given to this input during this phase.  At a high level,
our expansion strategy is:</p>

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
into <tt>|foo[0].P4|</tt> in the 4th phase, etc.</li>

<li><b>Simulation variables</b>.  A simulation variable like <tt>opcode</tt> is
turned into a list like <tt>(|opcode[0]| ... |opcode[n]|)</tt>.</li>

</ul>

<p>To support this strategy, this function takes a number of inputs.</p>

<ul>

<li><tt>name</tt> is the name of this input, and should be a list of E input
bits in lsb-first order.  (That is, Verilog-style names should have already
been expanded away using @(see stv-expand-names) or similar.)</li>

<li><tt>width</tt> is the pre-computed width of this input, i.e., it must be
exactly equal to <tt>(len name)</tt>.</li>

<li><tt>pnum</tt> is the current phase number (and starts at 0).  We use this
to know what suffix to put onto the generated variable names for <tt>_</tt>
values, e.g.,  <tt>|foo[0].P4|</tt></li>

<li><tt>entry</tt> is the actual entry we are trying to expand.  For instance,
it might be <tt>5</tt>, <tt>:ones</tt>, <tt>_</tt>, or whatever else the user
wrote down for this input at this phase number.</li>

<li><tt>gensyms</tt> is a flat list of all the names we have generated so far
for <tt>_</tt> entries, which we may extend.  This allows us to check for name
collisions later on.</li>

<li><tt>usersyms</tt> is a fast alist that binds the names of simulation
variables like <tt>opcode</tt> to lists of bits that we generate for these
symbols, i.e., <tt>(opcode[0] ... opcode[n])</tt>.  This allows us to check for
name collisions with generated symbols and width mismatches.  That is, we will
allow the same variable to be given to multiple inputs at multiple phases, but
for that to be sensible these inputs had better have the same width.</li>

<li><tt>prev-val</tt> is the sexpr list that this signal expanded to in the
previous phase, or NIL if this is the first phase of the simulation.  We use
this to figure out the new value of a <tt>~</tt> entry.</li>

</ul>"

  (defund stv-expand-input-entry (name width pnum entry gensyms usersyms prev-val)
    (declare (xargs :guard (and (atom-listp name)
                                (consp name)
                                (natp pnum)
                                (equal width (len name)))))
    (b* (((when (natp entry))
          (or (< entry (ash 1 width))
              (er hard? 'stv-expand-input-entry
                  "Phase ~x0 for ~x1: value ~x2 is too wide to fit in ~x3 ~
                   bits!" pnum name entry width))
          (mv (bool-to-4v-sexpr-lst (int-to-v entry width)) gensyms usersyms))

         ((when (eq entry 'x))
          (mv (repeat *4vx-sexpr* width) gensyms usersyms))

         ((when (eq entry :ones))
          (mv (repeat *4vt-sexpr* width) gensyms usersyms))

         ((when (eq entry '~))
          (or (= width 1)
              (er hard? 'stv-expand-input-entry
                  "Phase ~x0 for ~x1: value ~~ is not legal here.  It can ~
                   only be used in one-bit inputs, but this input is ~x2 bits ~
                   wide." pnum name width))
          (or prev-val
              (er hard? 'stv-expand-input-entry
                  "Phase ~x0 for ~x1: value ~~ is not legal here.  It must be ~
                   preceeded by a constant true or false, so it cannot be ~
                   used at the start of a line." pnum name))
          (or (equal prev-val (list *4vt-sexpr*))
              (equal prev-val (list *4vf-sexpr*))
              (er hard? 'stv-expand-input-entry
                  "Phase ~x0 for ~x1: value ~~ is not legal here.  It must be ~
                   preceeded by a constant true or false, but the previous ~
                   value was ~x2." pnum name prev-val))
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
          (er hard? 'stv-expand-input-entry
              "Phase ~x0 for ~x1: value ~x2 is not legal for input lines of ~
               symbolic test vectors.  See :xdoc symbolic-test-vector-format ~
               for help." pnum name entry)
          (mv (repeat *4vx-sexpr* width) gensyms usersyms))

         (my-syms (stv-gensyms (symbol-name entry) width))
         (look    (hons-get entry usersyms)))

      (or (not look)
          (equal (cdr look) my-syms)
          (er hard? 'stv-expand-input-entry
              "Phase ~x0 for ~x1: variable ~x2 cannnot be used here.  This ~
               input is ~x3 bits wide, but ~x2 was previously used for a ~
               ~x4-bit input." pnum name entry width (len (cdr look))))
      (mv my-syms gensyms (if look
                              usersyms
                            (hons-acons entry my-syms usersyms)))))

  (local (in-theory (enable stv-expand-input-entry)))

  (defthm true-listp-of-stv-expand-input-entry-gensyms
    (let ((ret (stv-expand-input-entry name width pnum entry gensyms usersyms prev-val)))
      (implies (true-listp gensyms)
               (true-listp (mv-nth 1 ret))))))


(defsection stv-expand-input-entries
  :parents (stv-compile)
  :short "Extend @(see stv-expand-input-entry) across a line."

  (defund stv-expand-input-entries (name width pnum entries gensyms usersyms prev-val)
    "Returns (MV NEW-ENTRIES GENSYMS USERSYMS)"
    (declare (xargs :guard (and (atom-listp name)
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

  (defmvtypes stv-expand-input-entries (true-listp nil nil))

  (defthm true-listp-of-stv-expand-input-entries-gensyms
    (let ((ret (stv-expand-input-entries name width pnum entries gensyms usersyms prev-val)))
      (implies (true-listp gensyms)
               (true-listp (mv-nth 1 ret))))))


(defsection stv-expand-input-lines
  :parents (stv-compile)
  :short "Extend @(see stv-expand-input-entry) across a list of lines."

  (defund stv-expand-input-lines (lines gensyms usersyms)
    "Returns (MV NEW-LINES GENSYMS USERSYMS)"
    (declare (xargs :guard (true-list-listp lines)))
    (b* (((when (atom lines))
          (mv nil gensyms usersyms))
         (line1 (car lines))
         ((cons name1 entries1) line1)

         ((unless (and (consp name1)
                       (atom-listp name1)))
          (er hard? 'stv-expand-input-lines
              "Expected all input line names to be already expanded to ~
               non-empty lists of E bits, but found ~x0." name1)
          (mv nil gensyms usersyms))

         ((mv new-entries1 gensyms usersyms)
          (stv-expand-input-entries name1 (len name1) 0 entries1 gensyms usersyms nil))
         (new-car (cons name1 new-entries1))
         ((mv new-cdr gensyms usersyms)
          (stv-expand-input-lines (cdr lines) gensyms usersyms)))
      (mv (cons new-car new-cdr) gensyms usersyms)))

  (local (in-theory (enable stv-expand-input-lines)))

  (defmvtypes stv-expand-input-lines (true-listp nil nil))

  (defthm true-list-listp-of-stv-expand-input-lines
    (let ((ret (stv-expand-input-lines lines gensyms usersyms)))
      (true-list-listp (mv-nth 0 ret))))

  (defthm true-listp-of-stv-expand-input-lines-gensyms
    (let ((ret (stv-expand-input-lines lines gensyms usersyms)))
      (implies (true-listp gensyms)
               (true-listp (mv-nth 1 ret))))))



; -----------------------------------------------------------------------------
;
;                     CREATING THE SPECIALIZING ALIST
;
; -----------------------------------------------------------------------------

(defsection stv-restrict-alist
  :parents (stv-compile)
  :short "Construct an alist binding fully-general input names (for all phases)
to @(see 4v-sexprs) derived from the symbolic test vector."

  :long "<p>@(call stv-restrict-alist) produces an alist.</p>

<p><tt>lines</tt> are the output from @(see stv-expand-input-lines).  We expect
that the lines have been widened, had their names resolved into E bits, and had
their entries turned into 4v-sexpr lists.</p>

<p><tt>acc</tt> is an alist that we extend.  Typically it is the alist that has
the <tt>:initial</tt> bindings.</p>

<p>We construct an ordinary (slow) alist that binds the input names we are
going to use in our fully-general simulation to their bindings according to the
symbolic test vector.  This is a single alist that includes the bindings for
the variables at all phases, plus (presumably, via acc) any initial bindings
for state bits.</p>

<p>The sexprs in this alist will often be constants (e.g., when natural
numbers, <tt>:ones</tt>, <tt>x</tt>, or <tt>~</tt> values are used), but they
can also have free variables from <tt>_</tt> symbols and also simulation
variable bits.</p>

<p>The general intent is to make the resulting alist fast, and use it along
with @(see 4v-sexpr-restrict) to specialize the fully general simulation,
effectively \"assuming\" the STV.</p>"

  (defund stv-restrict-alist-aux (name phase entries acc)
    (declare (xargs :guard (and (atom-listp name)
                                (natp phase))))
    (b* (((when (atom entries))
          acc)
         (name-at-phase (stv-suffix-signals name (str::cat ".P" (str::natstr phase))))
         (val-at-phase  (car entries))
         (acc           (safe-pairlis-onto-acc name-at-phase val-at-phase acc)))
      (stv-restrict-alist-aux name (+ 1 phase) (cdr entries) acc)))

  (defund stv-restrict-alist (lines acc)
    (declare (xargs :guard (true-list-listp lines)))
    (b* (((when (atom lines))
          acc)
         (line1 (car lines))
         ((cons name entries) line1)
         ((unless (atom-listp name))
          (er hard? 'stv-restrict-alist
              "Name should be a list of E bits, but is ~x0." name))
         (acc (stv-restrict-alist-aux name 0 entries acc)))
      (stv-restrict-alist (cdr lines) acc))))



; -----------------------------------------------------------------------------
;
;               COMPILING :OUTPUT LINE VALUES INTO 4V-SEXPRS
;
; -----------------------------------------------------------------------------

(defsection stv-expand-output-entry
  :parents (stv-compile)
  :short "Convert a single user-level output/internal value (e.g., _, result)
into a list of @(see 4v-sexprs)."

  :long "<p><b>Signature:</b> @(call stv-expand-output-entry) returns <tt>(mv
new-val usersyms)</tt>.</p>

<p>The only valid entries for output lines are <tt>_</tt> (for signals we don't
care about) and simulation variables.  Here, we just leave any <tt>_</tt>
values alone, but we replace simulation variables with lists of new variables
that we generate from their names.  That is, a simulation variable like
<tt>result</tt> will be converted into a list of bits like <tt>(result[0]
... result[4])</tt>.</p>

<p>We are given:</p>

<ul>

<li><tt>name</tt> is the name of this output.  It should be a list of E input
bits in lsb-first order.  That is, Verilog-style names should have already
been expanded away using @(see stv-expand-names) or similar.</li>

<li><tt>width</tt> is the pre-computed width of this output.  It must be
exactly equal to <tt>(len name)</tt>.  This lets us know how many variables to
generate when we hit a simulation variable.</li>

<li><tt>pnum</tt> is the current phase number (and starts at 0).  This is
semantically irrelevant; we use it only to generate better error messages.</li>

<li><tt>entry</tt> is the actual entry we are trying to expand, i.e., it's what
the user wrote down for this output at this phase.  To be well-formed, the
entry needs to be <tt>_</tt> or a simulation variable, but the user can write
down anything so we have to check that it is valid.</li>

<li><tt>usersyms</tt> is a fast alist binding simulation variables to the lists
of bits that we've generated to represent them.  We assume this only contains
the output simulation variables.  This lets us make sure that output variables
aren't being reused.</li>

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
          (er hard? 'stv-expand-output-entry
              "Phase ~x0 for ~x1: value ~x2 is not legal for :output lines."
              pnum name entry)
          (mv nil usersyms))

         ((when (eq entry '_))
          ;; That's fine, just leave it alone.
          (mv entry usersyms))

         ;; Else, a simulation variable.  It had better not be used yet.
         (look (hons-get entry usersyms))
         ((when look)
          (er hard? 'stv-expand-output-entry
              "Phase ~x0 for ~x1: variable ~x2 is already in use, so it ~
               cannot be used again." pnum name entry)
          (mv nil usersyms))

         ;; Okay it wasn't used.  Make its symbols and such.
         (my-syms  (stv-gensyms (symbol-name entry) width))
         (usersyms (hons-acons entry my-syms usersyms)))
      (mv my-syms usersyms))))


(defsection stv-expand-output-entries
  :parents (stv-compile)
  :short "Extend @(see stv-expand-output-entry) across a line."

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

  (defmvtypes stv-expand-output-entries (true-listp nil)))


(defsection stv-expand-output-lines
  :parents (stv-compile)
  :short "Extend @(see stv-expand-output-entry) across a list of lines."

  (defund stv-expand-output-lines (lines usersyms)
    "Returns (MV NEW-LINES USERSYMS)"
    (declare (xargs :guard (true-list-listp lines)))
    (b* (((when (atom lines))
          (mv nil usersyms))
         (line1 (car lines))
         ((cons name1 entries1) line1)

         ((unless (and (consp name1)
                       (atom-listp name1)))
          (er hard? 'stv-expand-output-lines
              "Expected :output line names to be already expanded to non-empty ~
               lists of E bits, but found ~x0." name1)
          (mv nil usersyms))

         ((mv new-entries1 usersyms)
          (stv-expand-output-entries name1 (len name1) 0 entries1 usersyms))

         (new-car (cons name1 new-entries1))
         ((mv new-cdr usersyms)
          (stv-expand-output-lines (cdr lines) usersyms)))
      (mv (cons new-car new-cdr) usersyms)))

  (local (in-theory (enable stv-expand-output-lines)))

  (defthm true-list-listp-of-stv-expand-output-lines
    (let ((ret (stv-expand-output-lines lines usersyms)))
      (true-list-listp (mv-nth 0 ret)))))



; -----------------------------------------------------------------------------
;
;               COMPILING :INTERNAL LINE VALUES INTO 4V-SEXPRS
;
; -----------------------------------------------------------------------------

; These are almost the same as output lines.  The only difference is that we
; need to canonicalize their paths.

(defsection stv-expand-internal-line
  :parents (stv-compile)

  (local (defthm fast-canonicalize-paths-1-under-iff
           (iff (mv-nth 1 (fast-canonicalize-paths paths mod))
                (consp paths))
           :hints(("Goal" :in-theory (enable fast-canonicalize-paths)))))

  (defund stv-expand-internal-line (line usersyms mod)
    "Returns (MV NEW-LINE USERSYMS)"
    (declare (xargs :guard (and (true-listp line)
                                (good-esim-modulep mod))))
    (b* (((cons name entries) line)

         ((unless (and (consp name)
                       (true-listp name)))
          (er hard? 'stv-expand-internal-lines
              "Expected :internal line names to be already expanded to non-empty ~
               lists of E paths, but found ~x0." name)
          (mv nil usersyms))

         ;; The ESIM simulation only involves canonical paths, so to be able to
         ;; extract the right paths we need to canonicalize these paths.
         ((mv okp new-name) (fast-canonicalize-paths name mod))
         ((unless okp)
          (er hard? 'stv-expand-internal-lines
              "Failed to canonicalize all the paths for ~x0." name)
          (mv nil usersyms))

         ((mv new-entries usersyms)
          (stv-expand-output-entries new-name (len new-name) 0 entries usersyms))

         (new-line (cons new-name new-entries)))
      (mv new-line usersyms)))

  (defmvtypes stv-expand-internal-line (true-listp nil)))


(defsection stv-expand-internal-lines
  :parents (stv-compile)
  :short "Extend @(see stv-expand-internal-line) across a list of lines."

  (defund stv-expand-internal-lines (lines usersyms mod)
    "Returns (MV NEW-LINES USERSYMS)"
    (declare (xargs :guard (and (true-list-listp lines)
                                (good-esim-modulep mod))))
    (b* (((when (atom lines))
          (mv nil usersyms))
         ((mv line1 usersyms) (stv-expand-internal-line (car lines) usersyms mod))
         ((mv lines2 usersyms) (stv-expand-internal-lines (cdr lines) usersyms mod)))
      (mv (cons line1 lines2) usersyms)))

  (defmvtypes stv-expand-internal-lines (true-list-listp nil)))


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
output or internal lines (which we assume have already been expanded), and an
accumulator which should initially be <tt>nil</tt>.</p>

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

(defsection stv-compile
  :parents (symbolic-test-vectors)
  :short "Syntactically transform a symbolic test vector, readying it for
evaluation, debugging, etc."

  :long "<p><b>Signature:</b> @(call stv-compile) returns a @(see
compiled-stv-p).</p>

<p>Here, <tt>mod</tt> should be a valid @(see esim) module, and <tt>stv</tt>
should be an @(see stvdata-p) that has already had its lines widened and any
Verilog-style names expanded; see for instance @(see stv-widen) and @(see
stv-expand-names).</p>

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
collect and how we want to name them.</p>"

  (defund stv-compile (stv mod)
    (declare (xargs :guard (and (stvdata-p stv)
                                (good-esim-modulep mod))))
    (b* (((stvdata stv) stv)
         (nphases (stv-number-of-phases stv))
         ((unless (posp nphases))
          (er hard? 'stv-compile "Trying to compile an STV without any phases?"))

         ;; Initials and inputs...
         (in-usersyms nil)
         ((mv initial-alist in-usersyms)  (stv-initial-lines-to-alist stv.initial in-usersyms mod))
         ((mv inputs gensyms in-usersyms) (stv-expand-input-lines stv.inputs nil in-usersyms))
         (restrict-alist (stv-add-suffixes-to-initial-alist initial-alist))
         (restrict-alist (stv-restrict-alist inputs restrict-alist))
         (restrict-alist (make-fast-alist restrict-alist))

         ;; Outputs and internals...
         (out-usersyms nil)
         ((mv outputs out-usersyms)   (stv-expand-output-lines stv.outputs out-usersyms))
         ((mv internals out-usersyms) (stv-expand-internal-lines stv.internals out-usersyms mod))
         (out-extract-alists (stv-extraction-alists (- nphases 1) outputs nil))
         (int-extract-alists (stv-extraction-alists (- nphases 1) internals nil))

         (all-in-bits (alist-keys restrict-alist))
         ((unless (uniquep all-in-bits))
          ;; This could be really bad because you'd be shadowing one value with
          ;; another, and it could easily happen to you if you gave two
          ;; different paths on :initial things that turned out to refer to the
          ;; same state bit.
          (er hard? 'stv-compile
              "Name clash.  Multiple input/initial bindings were generated for ~x0."
              (duplicated-members all-in-bits)))

         (in-simvars (alist-keys in-usersyms))
         (out-simvars (alist-keys out-usersyms))
         ((unless (and (uniquep in-simvars)
                       (uniquep out-simvars)
                       (symbol-listp in-simvars)
                       (symbol-listp out-simvars)))
          (er hard? 'stv-compile
              "Programming error.  in-simvars or out-simvars aren't unique ~
               symbols.  This shouldn't be possible."))

         (illegally-reused-simvars (duplicated-members (append in-simvars out-simvars)))
         ((when illegally-reused-simvars)
          ;; This is something the user could try to do.  It wouldn't *really*
          ;; be a problem, but certainly seems to indicate confusion on their
          ;; part.
          (er hard? 'stv-compile
              "Error: It is illegal to reuse the input simulation variables ~
               (from :input and :initial lines) as output simulation ~
               variables (from :output and :internal lines).  Illegally ~
               reused variables: ~x0" illegally-reused-simvars))

         (all-bits (vl::append-domains-exec in-usersyms gensyms))
         (all-bits (vl::append-domains-exec out-usersyms all-bits))
         ((unless (uniquep all-bits))
          ;; It's hard to imagine this happening, if the in-usersyms and
          ;; out-usersyms have unique keys.  But if somehow the user gave a
          ;; simulation variable name that clashed with a gensym, it'd be bad.
          (er hard? 'stv-compile "Name clash for ~x0." (duplicated-members all-bits)))

         (ret (make-compiled-stv
               :nphases        nphases
               :restrict-alist restrict-alist

               ;; These have to stay separate because we have to use them to
               ;; extract from different esim outputs
               :out-extract-alists out-extract-alists
               :int-extract-alists int-extract-alists

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
               :expanded-outs outputs
               :expanded-ints internals
               )))

      (fast-alist-free in-usersyms)
      (fast-alist-free out-usersyms)
      ret))

  ;; Compilation isn't necessarily slow, but memoizing it seems like a good
  ;; idea to make sure that all of the alists stay the same.
  (memoize 'stv-compile)

  (local (in-theory (enable stv-compile)))

  (defthm compiled-stv-p-of-stv-compile
    (equal (compiled-stv-p (stv-compile stv mod))
           (if (stv-compile stv mod)
               t
             nil))))


