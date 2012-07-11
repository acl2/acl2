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


; stv-expand.lisp -- expansion of names and hierarchical names for STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "../esim-vl")
(include-book "../esim-paths")
(include-book "centaur/vl/mlib/hid-tools" :dir :system)
(include-book "centaur/vl/mlib/expr-parse" :dir :system)
(local (include-book "centaur/vl/util/arithmetic" :dir :system))



(defsection stv-maybe-match-select
  :parents (stv-expand)

  (defund stv-maybe-match-select (x)
    "Returns (MV FROM MSB? LSB?)"
    (declare (xargs :guard (vl::vl-expr-p x)))
    (b* (((unless (vl::vl-nonatom-p x))
          (mv x nil nil))
         (op   (vl::vl-nonatom->op x))
         (args (vl::vl-nonatom->args x))

         ((when (eq op :vl-partselect-colon))
          (b* ((from (first args))
               (msb  (second args))
               (lsb  (third args))
               ((unless (and (vl::vl-expr-resolved-p msb)
                             (vl::vl-expr-resolved-p lsb)))
                (er hard? 'stv-maybe-match-select
                    "Part select indicies are not resolved: ~s0"
                    (vl::vl-pps-expr x))
                (mv x nil nil)))
            (mv from (vl::vl-resolved->val msb) (vl::vl-resolved->val lsb))))

         ((when (eq op :vl-bitselect))
          (b* ((from (first args))
               (bit  (second args))
               ((unless (vl::vl-expr-resolved-p bit))
                (er hard? 'stv-maybe-match-select
                    "Bit select index is not resolved: ~s0"
                    (vl::vl-pps-expr x))
                (mv x nil nil))
               (val (vl::vl-resolved->val bit)))
            (mv from val val))))
      (mv x nil nil)))

  (local (in-theory (enable stv-maybe-match-select)))

  (defthm vl-expr-of-stv-maybe-match-select
    (implies (force (vl::vl-expr-p x))
             (vl::vl-expr-p (mv-nth 0 (stv-maybe-match-select x)))))

  (defmvtypes stv-maybe-match-select
    (nil (or (not x) (natp x)) (or (not x) (natp x)))))



; -----------------------------------------------------------------------------
;
;                EXPANDING NAMES FOR :INPUT AND :OUTPUT LINES
;
; -----------------------------------------------------------------------------

; Here we only need to support ordinary identifiers (not hierarchical
; identifiers) and we can do extra sanity checking to make sure that, e.g.,
; :input lines mention inputs, and :output lines mention outputs.

(defsection stv-wirename-parse
  :parents (stv-expand)
  :short "Match a Verilog-style wire name, bit-select, or part-select."

  :long "<p><b>Signature:</b> @(call stv-wirename-parse) returns <tt>(mv
basename msb-idx lsb-idx)</tt>.</p>

<p>Examples:</p>

<ul>
 <li>\"foo\"      becomes (mv \"foo\" nil nil)</li>
 <li>\"foo[3]\"   becomes (mv \"foo\" 3 3)</li>
 <li>\"foo[5:3]\" becomes (mv \"foo\" 5 3)</li>
 <li>\"foo[3:5]\" becomes (mv \"foo\" 3 5)</li>
</ul>

<p>If the wire name isn't of an acceptable form, an error is caused.</p>"

  (defund stv-wirename-parse (str)
    (declare (xargs :guard (stringp str)))
    (b* ((expr (vl::vl-parse-expr-from-str str))
         ((unless expr)
          (er hard? 'stv-wirename-parse "Failed to parse: ~s0" str)
          (mv "" nil nil))
         ((mv from msb lsb) (stv-maybe-match-select expr))
         ((unless (vl::vl-idexpr-p from))
          (er hard? 'stv-wirename-parse "Invalid STV wire name: ~s0~%" str)
          (mv "" nil nil)))
      (mv (vl::vl-idexpr->name from) msb lsb)))

  (defmvtypes stv-wirename-parse
    (stringp (or (not x) (natp x)) (or (not x) (natp x))))

  (local
   (progn

     (assert! (b* (((mv name msb lsb) (stv-wirename-parse "foo")))
                (equal (list name msb lsb) '("foo" nil nil))))

     (assert! (b* (((mv name msb lsb) (stv-wirename-parse "foo[3]")))
                (equal (list name msb lsb) '("foo" 3 3))))

     (assert! (b* (((mv name msb lsb) (stv-wirename-parse "foo[3:5]")))
                (equal (list name msb lsb) '("foo" 3 5))))

     (assert! (b* (((mv name msb lsb) (stv-wirename-parse "foo[5:3]")))
                (equal (list name msb lsb) '("foo" 5 3)))))))


(defsection stv-expand-name
  :parents (stv-expand)
  :short "Expand a name from a symbolic test vector's line into explicit lists
of E bits."

  :long "<p><b>Signature:</b> @(call stv-expand-name) returns an LSB-first list
of E bits for a non-hierarchical valid STV signal name.</p>

<p>As described in @(see acl2::symbolic-test-vector-format), the signal names
for :input and :output lines can be either:</p>

<ul>
<li>A string that names a particular input bus,</li>
<li>A string that is a Veriog-style bit- or part-select from a particular input
bus, or</li>
<li>An explicit list of E bits (in LSB-first order).</li>
</ul>

<p>This function is given <tt>x</tt>, the actual name that occurs on such a
line.  Our goal is to convert <tt>x</tt> into the explicit bit list form.  If
<tt>x</tt> is already a list of bits then this is trivial.  Otherwise, we have
to look it up in the module.</p>

<p>Type is either <tt>:i</tt> or <tt>:o</tt> and says whether this should be
the name of an input or output, and <tt>mod</tt> is the whole E module so that
we can look up its inputs and outputs.</p>

<p>We do basic error checking to make sure that the name refers to valid input
or output bits.</p>"

  (defund stv-expand-name (x type mod)
    "Returns an LSB-first list of bit names, e.g., (|foo[0]| |foo[1]| ...)."
    (declare (xargs :guard (symbolp type)))
    (b* ((pat     (gpl type mod))
         (modname (gpl :n mod))

         ((when (stringp x))
          (b* ( ;; Note: for plain names msb/lsb will be nil.
               ((mv basename msb lsb) (stv-wirename-parse x))
               (basename-bits         (vl::esim-vl-find-io basename pat))
               ((unless basename-bits)
                (er hard? 'stv-expand-name
                    "Trying to expand ~s0, but there is no ~s1 named ~s2 in ~x3."
                    x
                    (if (equal type :i) "input" "output")
                    basename
                    modname))

               ((unless (and msb lsb))
                ;; The input name is just "foo", so get all of the wires of
                ;; foo.  This lets you refer to busses by name without having
                ;; to give their explicit indices in the STV.
                basename-bits)

               ;; Else, the input is "foo[5:3]" or similar, so we want to just
               ;; get bits 5-3.  But put them in LSB-first order so they'll line
               ;; up with the basename-bits
               (expect-bits
                ;; Stupid hack: it would be nicer to write:
                ;; (reverse (vl-emodwires-from-msb-to-lsb basename msb lsb))
                ;; But we just reverse the lsb/msb to avoid the extra consing
                (vl::vl-emodwires-from-msb-to-lsb basename lsb msb))
               ((unless (ordered-subsetp expect-bits basename-bits))
                (er hard? 'stv-expand-name
                    "Trying to expand ~s0, but the bits being asked for ~s1.~% ~
                    - Found wires: ~x2 through ~x3~% ~
                    - Want wires:  ~x4 through ~x5."
                    x
                    (if (subsetp-equal expect-bits basename-bits)
                        "are not in the right order"
                      "are not found")
                    (car basename-bits)
                    (car (last basename-bits))
                    (car expect-bits)
                    (car (last expect-bits)))))
            expect-bits))

         ;; Otherwise, we should have been given a list of valid input bits.
         ((unless (symbol-listp x))
          (er hard? 'stv-expand-name
              "Invalid input name (expected string or a list of e bits), but ~
              found ~x0."
              x))

         (flat-pat (pat-flatten1 pat))
         ((unless  (subsetp-equal x flat-pat))
          (er hard? 'stv-expand-name
              "Trying to provide bindings for ~s0 that don't exist: ~x1."
              (if (equal type :i) "inputs" "outputs")
              (set-difference-equal flat-pat x))))
      x)))

  #||

;; some test cases:

(stv-expand-name "mlResult_P" :i acl2::|*mmx*|)        ;; works -- 0 to 127
(stv-expand-name "mlResult_P[5:3]" :i acl2::|*mmx*|)   ;; works -- 3 to 5
(stv-expand-name "mlResult_P[15:3]" :i acl2::|*mmx*|)  ;; works -- 3 to 15
(stv-expand-name "mlResult_P[130:3]" :i acl2::|*mmx*|) ;; error -- out of range, good
(stv-expand-name "mlResult_P[3:5]" :i acl2::|*mmx*|)   ;; error -- wrong order, good
  ||#



(defsection stv-expand-names-in-lines
  :parents (stv-expand)
  :short "@(call stv-expand-names-in-lines) expands all of the names in a list
of STV :input or :output lines."

  (defund stv-expand-names-in-lines (lines type mod)
    (declare (xargs :guard (and (or (eq type :i)
                                    (eq type :o))
                                (true-list-listp lines))))
    (b* (((when (atom lines))
          nil)
         (line1              (car lines))
         ((cons name phases) line1)
         (new-name           (stv-expand-name name type mod)))
      (cons (cons new-name phases)
            (stv-expand-names-in-lines (cdr lines) type mod))))

  (local (in-theory (enable stv-expand-names-in-lines)))

  (defthm alistp-of-stv-expand-names-in-lines
    (alistp (stv-expand-names-in-lines lines type mod)))

  (defthm true-list-listp-of-stv-expand-names-in-lines
    (implies (true-list-listp lines)
             (true-list-listp (stv-expand-names-in-lines lines type mod)))))




; -----------------------------------------------------------------------------
;
;               EXPANDING NAMES FOR :INTERNAL AND :INITIAL LINES
;
; -----------------------------------------------------------------------------

; Here we need to support both hierarchical and non-hierarchical identifiers.
; E.g., the user might want to pull out or initialize some signal in the
; top-level module, or in some submodule.

(defsection stv-hid-split
  :parents (stv-expand)
  :short "Splits up a HID into a list of instance names and a wire name."

  (defund stv-hid-split (hid)
    "Returns (MV INSTNAMES WIRENAME) or causes an error."
    (declare (xargs :guard (and (vl::vl-expr-p hid)
                                (vl::vl-hidexpr-p hid))))
    (b* (((unless (vl::vl-hid-indicies-resolved-p hid))
          (er hard? 'stv-hid-split
              "HID has unresolved indices: ~s0~%" (vl::vl-pps-expr hid))
          (mv nil ""))
         (parts (vl::vl-explode-hid hid))
         ((unless (string-listp parts))
          ;; Parts is like ("foo" "bar" 3 "baz") for foo.bar[3].baz, too hard
          (er hard? 'stv-hid-split
              "We don't currently support hierarchical identifiers that go ~
             through array instances, like foo.bar[3].baz.  The HID that ~
             triggered this error was: ~s0~%" (vl::vl-pps-expr hid))
          (mv nil ""))
         ((when (< (len parts) 2))
          ;; I don't really see how this could happen.  Maybe it can't happen.
          (er hard? 'stv-hid-split
              "Somehow the HID has only one piece?  ~s0~%"
              (vl::vl-pps-expr hid))
          (mv nil ""))
         (instnames (butlast parts 1))
         (wirename  (car (last parts))))
      (mv instnames wirename)))

  (local (in-theory (enable stv-hid-split)))

  (defthm true-listp-of-stv-hid-split
    (true-listp (mv-nth 0 (stv-hid-split hid)))
    :rule-classes :type-prescription)

  (local (defthm l0
           (implies (and (string-listp x)
                         (consp x))
                    (stringp (car (last x))))
           :hints(("Goal" :expand (last x)))))

  (defthm stringp-of-stv-hid-split
    (stringp (mv-nth 1 (stv-hid-split hid)))
    :rule-classes :type-prescription
    :hints(("goal" :use ((:instance l0 (x (vl::vl-explode-hid hid)))))))

  (defthm string-listp-of-stv-hid-split
    (string-listp (mv-nth 0 (stv-hid-split hid)))))


(defsection stv-hid-parse
  :parents (stv-expand)
  :short "Match a Verilog-style plain or hierarchical name, perhaps with a bit-
or part-select on the end of it."

  :long "<p><b>Signature:</b> @(call stv-hid-parse) returns <tt>(mv
instnames wirename msb-idx lsb-idx)</tt></p>

<p>This is sort of misnamed because it works for normal identifiers as well as
hierarchical identifiers.</p>

<p>Examples:</p>

<ul>
 <li>\"foo[3]\" becomes <tt>(mv nil \"foo\" 3 3)</tt></li>
 <li>\"foo.bar.baz\" becomes <tt>(mv '(\"foo\" \"bar\") \"baz\" nil nil)</tt></li>
 <li>\"foo.bar.baz[3]\" becomes <tt>(mv '(\"foo\" \"bar\") \"baz\" 3 3)</tt></li>
 <li>\"foo.bar.baz[3:0]\" becomes <tt>(mv '(\"foo\" \"bar\") \"baz\" 3 0)</tt></li>
</ul>

<p>If the input string name isn't of an acceptable form, an error is
caused.</p>"

  (defund stv-hid-parse (str)
    (declare (xargs :guard (stringp str)))
    (b* ((expr (vl::vl-parse-expr-from-str str))
         ((unless expr)
          (er hard? 'stv-hid-parse "Failed to parse: ~s0" str)
          (mv nil "" nil nil))
         ((mv from msb lsb) (stv-maybe-match-select expr))

         ((when (vl::vl-idexpr-p from))
          ;; This is legitimate for top-level internal wires like foo[3]; There
          ;; just aren't any instnames to follow.
          (mv nil (vl::vl-idexpr->name from) msb lsb))

         ((unless (vl::vl-hidexpr-p from))
          (er hard? 'stv-hid-parse "Invalid STV wire name: ~s0" str)
          (mv nil "" nil nil))

         ((mv instnames wirename) (stv-hid-split from)))
      (mv instnames wirename msb lsb)))

  (local (in-theory (enable stv-hid-parse)))

  (defmvtypes stv-hid-parse
    (true-listp stringp (or (not x) (natp x)) (or (not x) (natp x))))

  (defthm string-listp-of-stv-hid-parse
    (string-listp (mv-nth 0 (stv-hid-parse str))))

  (local
   (progn

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo")))
                (equal (list instnames wirename msb lsb)
                       '(nil "foo" nil nil))))

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo[3]")))
                (equal (list instnames wirename msb lsb)
                       '(nil "foo" 3 3))))

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo[3:5]")))
                (equal (list instnames wirename msb lsb)
                       '(nil "foo" 3 5))))

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo[5:3]")))
                (equal (list instnames wirename msb lsb)
                       '(nil "foo" 5 3))))

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo.bar")))
                (equal (list instnames wirename msb lsb)
                       '(("foo") "bar" nil nil))))

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo.bar[3]")))
                (equal (list instnames wirename msb lsb)
                       '(("foo") "bar" 3 3))))

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo.bar[3:5]")))
                (equal (list instnames wirename msb lsb)
                       '(("foo") "bar" 3 5))))

     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo.bar[5:3]")))
                (equal (list instnames wirename msb lsb)
                       '(("foo") "bar" 5 3))))


     (assert! (b* (((mv instnames wirename msb lsb) (stv-hid-parse "foo.bar.baz[5:3]")))
                (equal (list instnames wirename msb lsb)
                       '(("foo" "bar") "baz" 5 3))))

     ;; (stv-hid-parse "foo.bar[2].baz[5:3]") -- error, good, not supported yet
     ;; (stv-hid-parse "faz[w:3]") -- error, not resolved
     )))



(defsection stv-hid-to-paths
  :parents (stv-expand)
  :short "Convert a Verilog-style plain or hierarchical name (optionally with a
bit- or part-select) into an LSB-ordered list of <b>non-canonical</b> ESIM
paths."

  :long "<p>@(call stv-hid-to-paths) returns a list of LSB-first ordered paths
in the sense of @(see acl2::mod-internal-paths).</p>

<ul>

<li><tt>x</tt> is a string like <tt>foo</tt>, <tt>foo[3:0]</tt>,
<tt>foo.bar.baz</tt>, <tt>foo.bar.baz[3]</tt>, etc.  That is, it should either
be a plain or hierarchical Verilog identifier, perhaps with a bit or
part-select on the end.</li>

<li><tt>mod</tt> is the E module that X is based in.</li>

</ul>"

  (defund stv-turn-bits-into-non-canonical-paths
    (instname-list  ;; (foo bar)
     bits           ;; (baz[3] baz[2] baz[1] baz[0])
     )
    ;; ---> ( (foo bar . baz[3])
    ;;        (foo bar . baz[2])
    ;;        ...
    ;;        (foo bar . baz[0]) )
    (declare (xargs :guard (true-listp instname-list)))
    (if (atom bits)
        nil
      (cons (append instname-list (car bits))
            (stv-turn-bits-into-non-canonical-paths instname-list (cdr bits)))))

  (defund stv-hid-to-paths (x mod)
    (declare (xargs :guard (stringp x)))
    (b* (((mv instnames wirename msb lsb) (stv-hid-parse x))

         ;; 1. Find the submod that this HID points to.
         (instnames (intern-list-in-package-of-symbol instnames (pkg-witness "ACL2")))
         (submod    (follow-esim-path instnames mod))
         ((unless submod)
          (er hard? 'stv-hid-to-paths
              "Error following path ~x0 in ~x1." x (gpl :n mod)))

         ;; 2. Look up this E names for this wire in the wire alist.  Note that
         ;; the WALIST has the bits in MSB-First order!
         (walist (vl::esim-vl-wirealist submod))
         (lookup (hons-assoc-equal wirename walist))
         ((unless lookup)
          (er hard? 'stv-hid-to-paths
              "Can't follow ~s0: followed the instances ~x1 to an ~x2 ~
               submodule, but then there was no wire named ~s3 in the wire ~
               alist." x instnames (gpl :n submod) wirename))
         (msb-first-wires (cdr lookup))
         (lsb-first-wires (reverse msb-first-wires))

         ((unless (and msb lsb))
          ;; X is something like "foo" or "foo.bar.baz" with no bit- or
          ;; part-select, so the user is asking for the whole wire!
          (stv-turn-bits-into-non-canonical-paths instnames lsb-first-wires))

         ;; Otherwise, X is something like "foo[3]" or "foo.bar.baz[5:3]", so
         ;; we need to make sure this range is in bounds and going in the right
         ;; direction.
         (expect-bits
          ;; Stupid hack: it would be nicer to write:
          ;; (reverse (vl-emodwires-from-msb-to-lsb basename msb lsb))
          ;; But we just reverse the lsb/msb to avoid the extra consing
          (vl::vl-emodwires-from-msb-to-lsb wirename lsb msb))

         ;; Make sure that the bits exist and are properly ordered for this wire
         ((unless (ordered-subsetp expect-bits lsb-first-wires))
          (er hard? 'stv-hid-to-paths
              "Trying to expand ~s0, but the bits being asked for ~s1.~% ~
               - Found wires: ~x2 through ~x3~% ~
               - Want wires:  ~x4 through ~x5."
              x
              (if (subsetp-equal expect-bits lsb-first-wires)
                  "are not in the right order"
                "are not found")
              (car lsb-first-wires)
              (car (last lsb-first-wires))
              (car expect-bits)
              (car (last expect-bits)))))

      (stv-turn-bits-into-non-canonical-paths instnames expect-bits))))

  #||

;; This one is an input:

(stv-hid-to-paths "mmxdphi.logicops001.mxdp_a_i" acl2::|*mmx*|)
 ;; -- good, gets mdpABus_loc_BrdCast_I[64...127] in superior module

(stv-hid-to-paths "mmxdphi.logicops001.mxdp_a_i[0]" acl2::|*mmx*|)
 ;; -- good, just bit 64 of superior wire

(stv-hid-to-paths "mmxdphi.logicops001.mxdp_a_i[1]" acl2::|*mmx*|)
 ;; -- good, just bit 65 of superior wire

(stv-hid-to-paths "mmxdphi.logicops001.mxdp_a_i[5:0]" acl2::|*mmx*|)
 ;; -- good, bits 64-69 of superior wire

(stv-hid-to-paths "mmxdphi.logicops001.mxdp_a_i[0:5]" acl2::|*mmx*|)
 ;; -- good, error, order is wrong

(stv-hid-to-paths "mmxdphi.logicops001.mxdp_a_i[72:0]" acl2::|*mmx*|)
  ;; -- good, error, out of order

;; This one is an internal wire:

(stv-hid-to-paths "mmxdphi.logicops001.sm5" acl2::|*mmx*|)
   ;; -- good, sm5[0] through [2]

(stv-hid-to-paths "mmxdphi.logicops001.sm5[0]" acl2::|*mmx*|)
   ;; -- good, sm5[0]

(stv-hid-to-paths "mmxdphi.logicops001.sm5[3]" acl2::|*mmx*|)
   ;; -- good, range error

;; This one is an output:

(stv-hid-to-paths "mmxdphi.logicops001.mdpmmxlogres_e" acl2::|*mmx*|)
   ;; -- good, suerior module's wire, 64-127

  ||#



(defsection stv-expand-hids-in-lines
  :parents (stv-expand)
  :short "@(call stv-expand-hids-in-lines) expands all of the HIDs in a list of
STV internal lines into lists of esim paths."

  (defund stv-expand-hids-in-lines (lines mod)
    (declare (xargs :guard (true-list-listp lines)))
    (b* (((when (atom lines))
          nil)
         (line1              (car lines))
         ((cons name phases) line1)
         ((unless (stringp name))
          (er hard? 'stv-expand-hids-in-lines
              "Internals line name is not a string: ~x0" name))
         (lsb-paths (stv-hid-to-paths name mod)))
      (cons (cons lsb-paths phases)
            (stv-expand-hids-in-lines (cdr lines) mod))))

  (local (in-theory (enable stv-expand-hids-in-lines)))

  (defthm alistp-of-stv-expand-hids-in-lines
    (alistp (stv-expand-hids-in-lines lines mod)))

  (defthm true-list-listp-of-stv-expand-hids-in-lines
    (implies (true-list-listp lines)
             (true-list-listp (stv-expand-hids-in-lines lines mod)))))



(defsection stv-expand
  :parents (symbolic-test-vectors)
  :short "Expand Verilog-style names throughout an STV into LSB-ordered ESIM
style paths."

  :long "<p><b>Signature:</b> @(call stv-expand) returns a new @(see
stvdata-p).</p>

<p>This is an STV preprocessing step which can be run before or after @(see
stv-widen).  It only affects the names in each STV line.</p>

<p>During this step, we resolve Verilog-style names like \"foo[3:0]\" and
\"foo.bar.baz[6:0],\" replacing them with LSB-ordered lists of ESIM bits or
paths.  This keeps the Verilog-specific stuff out of the rest of the STV
compiler.</p>"

  (defund stv-expand (stv mod)
    (declare (xargs :guard (stvdata-p stv)))
    (b* (((stvdata stv) stv))
      (make-stvdata :inputs    (stv-expand-names-in-lines stv.inputs :i mod)
                    :outputs   (stv-expand-names-in-lines stv.outputs :o mod)
                    :initial   (stv-expand-hids-in-lines stv.initial mod)
                    :internals (stv-expand-hids-in-lines stv.internals mod))))

  (local (in-theory (enable stv-expand)))

  (defthm stvdata-p-of-stv-expand
    (implies (force (stvdata-p stv))
             (stvdata-p (stv-expand stv mod)))))

