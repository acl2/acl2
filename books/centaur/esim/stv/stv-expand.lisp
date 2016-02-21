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


; stv-expand.lisp -- expansion of names and hierarchical names for STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "../esim-vl")
(include-book "../esim-paths")
(include-book "centaur/vl2014/mlib/hid-tools" :dir :system)
(include-book "centaur/vl2014/mlib/expr-parse" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))


(define stv-maybe-match-select ((x vl2014::vl-expr-p))
  :returns (mv (err? vl2014::maybe-stringp :rule-classes :type-prescription)
               (from vl2014::vl-expr-p :hyp :fguard)
               (msb? vl2014::maybe-natp :rule-classes :type-prescription)
               (lsb? vl2014::maybe-natp :rule-classes :type-prescription))
  :parents (stv-expand)
  :short "Match an expression with an optional bit- or part-select."
  (b* (((when (vl2014::vl-atom-p x))
        (mv nil x nil nil))
       (op   (vl2014::vl-nonatom->op x))
       (args (vl2014::vl-nonatom->args x))

       ((when (eq op :vl-select-colon))
        (b* ((from (first args))
             (msb  (second args))
             (lsb  (third args))
             ((unless (and (vl2014::vl-expr-resolved-p msb)
                           (vl2014::vl-expr-resolved-p lsb)))
              (mv (str::cat (symbol-name __function__)
                            ": part select indicies are not resolved: "
                            (vl2014::vl-pps-expr x))
                  x nil nil)))
          (mv nil from (vl2014::vl-resolved->val msb) (vl2014::vl-resolved->val lsb))))

       ((when (eq op :vl-index))
        (b* ((from (first args))
             (bit  (second args))
             ((unless (vl2014::vl-expr-resolved-p bit))
              (mv (str::cat (symbol-name __function__)
                            ": bit select index is not resolved: "
                            (vl2014::vl-pps-expr x))
                  x nil nil))
             (val (vl2014::vl-resolved->val bit)))
          (mv nil from val val))))
    (mv nil x nil nil)))



; -----------------------------------------------------------------------------
;
;                EXPANDING NAMES FOR :INPUT AND :OUTPUT LINES
;
; -----------------------------------------------------------------------------

; Here we only need to support ordinary identifiers (not hierarchical
; identifiers) and we can do extra sanity checking to make sure that, e.g.,
; :input lines mention inputs, and :output lines mention outputs.

(define stv-wirename-parse ((str stringp))
  :returns (mv (err?     vl2014::maybe-stringp :rule-classes :type-prescription)
               (basename stringp)
               (msb?     vl2014::maybe-natp :rule-classes :type-prescription)
               (lsb?     vl2014::maybe-natp :rule-classes :type-prescription))
  :parents (stv-expand)
  :short "Match a Verilog-style wire name, bit-select, or part-select."
  :long "<p>Examples:</p>

<ul>
 <li>\"foo\"      becomes (mv nil \"foo\" nil nil)</li>
 <li>\"foo[3]\"   becomes (mv nil \"foo\" 3 3)</li>
 <li>\"foo[5:3]\" becomes (mv nil \"foo\" 5 3)</li>
 <li>\"foo[3:5]\" becomes (mv nil \"foo\" 3 5)</li>
</ul>

<p>If the wire name isn't of an acceptable form, an error message is returned
as the first return value.</p>"

  (b* ((expr (vl2014::vl-parse-expr-from-str str))
       ((unless expr)
        (mv (str::cat (symbol-name __function__)
                      ": failed to parse: " str)
            "" nil nil))
       ((mv err from msb lsb) (stv-maybe-match-select expr))
       ((when err)
        (mv err "" nil nil))
       ((unless (vl2014::vl-idexpr-p from))
        (mv (str::cat (symbol-name __function__)
                      ": invalid wire name: " str)
            "" nil nil)))
    (mv nil (vl2014::vl-idexpr->name from) msb lsb))
  ///
  (local
   (progn
     (assert! (b* (((mv ?err name msb lsb) (stv-wirename-parse "foo")))
                (equal (list name msb lsb) '("foo" nil nil))))
     (assert! (b* (((mv ?err name msb lsb) (stv-wirename-parse "foo[3]")))
                (equal (list name msb lsb) '("foo" 3 3))))
     (assert! (b* (((mv ?err name msb lsb) (stv-wirename-parse "foo[3:5]")))
                (equal (list name msb lsb) '("foo" 3 5))))
     (assert! (b* (((mv ?err name msb lsb) (stv-wirename-parse "foo[5:3]")))
                (equal (list name msb lsb) '("foo" 5 3)))))))


(define stv-expand-name
  :parents (stv-expand)
  :short "Expand a name from a symbolic test vector's line into explicit lists
of E bits."

  ((x    "The name that the user put at the start of some STV line.")
   (type "Either @(':i') or @(':o') and says whether this should be the name
          of an input or output."
         (or (eq type :i)
             (eq type :o)))
   (mod  "The @(see esim) module we are working in, so we can look up names."))

  :returns (lsb-bits "An LSB-first list of E bits for a non-hierarchical valid
                      STV signal name, e.g., @('(|foo[0]| |foo[1]| ...)').")

  :long "<p>Recall from @(see acl2::symbolic-test-vector-format) that signal
names for :input and :output lines can be either:</p>

<ul>
<li>A string that names a particular input bus,</li>
<li>A string that is a Veriog-style bit- or part-select from a particular input
bus, or</li>
<li>An explicit list of E bits (in LSB-first order).</li>
</ul>

<p>Here, our goal is to convert any such name, @('x'), into the explicit bit
list form.  If @('x') is already a list of bits then this is trivial.
Otherwise, we have to look it up in the module.  We do basic error checking to
make sure that the name refers to valid input or output bits.</p>"

  (b* ((pat     (gpl type mod))
       (modname (gpl :n mod))

       ((when (stringp x))
        (b* ( ;; Note: for plain names msb/lsb will be nil.
             ((mv ?err basename msb lsb) (stv-wirename-parse x))
             ((when err)
              (raise "~s0" err))
             (basename-bits         (vl2014::esim-vl-find-io basename pat))
             ((unless basename-bits)
              (raise "Trying to expand ~s0, but there is no ~s1 named ~s2 in ~
                      ~x3."
                     x
                     (if (eq type :i) "input" "output")
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
              (vl2014::vl-emodwires-from-msb-to-lsb basename lsb msb))
             ((unless (ordered-subsetp expect-bits basename-bits))
              (raise "Trying to expand ~s0, but the bits being asked for ~s1.~% ~
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
        (raise "Invalid input name (expected string or a list of e bits), but ~
                found ~x0."
               x))

       (flat-pat (pat-flatten1 pat))
       ((unless  (subsetp-equal x flat-pat))
        (raise "Trying to provide bindings for ~s0 that don't exist: ~x1."
               (if (eq type :i) "inputs" "outputs")
               (set-difference-equal flat-pat x))))
    x))

  #||

;; some test cases:

(stv-expand-name "mlResult_P" :i acl2::|*mmx*|)        ;; works -- 0 to 127
(stv-expand-name "mlResult_P[5:3]" :i acl2::|*mmx*|)   ;; works -- 3 to 5
(stv-expand-name "mlResult_P[15:3]" :i acl2::|*mmx*|)  ;; works -- 3 to 15
(stv-expand-name "mlResult_P[130:3]" :i acl2::|*mmx*|) ;; error -- out of range, good
(stv-expand-name "mlResult_P[3:5]" :i acl2::|*mmx*|)   ;; error -- wrong order, good
  ||#



(define stv-expand-names-in-lines
  :parents (stv-expand)
  :short "Expands all of the names in a list of STV :input or :output lines."
  ((lines true-list-listp)
   (type  (or (eq type :i) (eq type :o)))
   mod)
  :returns (new-lines)
  (b* (((when (atom lines))
        nil)
       (line1              (car lines))
       ((cons name phases) line1)
       (new-name           (stv-expand-name name type mod)))
    (cons (cons new-name phases)
          (stv-expand-names-in-lines (cdr lines) type mod)))
  ///
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

#!VL2014
(define vl-explode-hidindex
  :parents (acl2::stv-hid-parse)
  :short "Explode a (resolved) @(see vl2014::vl-hidindex-p) into a flat list of
          its components."
  ((x vl-expr-p "The hidindex to explode, e.g., @('foo[3][4][5]')"))
  :guard (and (vl-hidindex-p x)
              (vl-hidindex-resolved-p x))
  :guard-hints(("Goal" :in-theory (enable vl-hidindex-resolved-p)))
  :returns (pieces true-listp :rule-classes :type-prescription
                   "A flat, mixed list of strings and numbers, e.g.,
                   @('(\"foo\" 3 4 5)').")
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  (b* ((name    (vl-hidindex->name x))
       (indices (vl-hidindex->indices x)))
    (cons name (vl-exprlist-resolved->vals indices))))

#!VL2014
(define vl-explode-hid
  :parents (acl2::stv-hid-parse)
  :short "Explode a (resolved) @(see vl2014::vl-hidexpr-p) into a flat list of its
          components."
  ((x vl-expr-p "The hidexpr to explode, e.g., foo.bar[2][3].baz."))
  :guard (and (vl-hidexpr-p x)
              (vl-hidexpr-resolved-p x))
  :returns
  (pieces true-listp :rule-classes :type-prescription
          "A flat, mixed list of strings and numbers, e.g.,
           @('(\"foo\" \"bar\" 2 3 \"baz\")').")
  :measure (vl-expr-count x)
  (if (vl-hidexpr->endp x)
      (list (vl-hidname->name x))
    (append (vl-explode-hidindex (vl-hidexpr->first x))
            (vl-explode-hid (vl-hidexpr->rest x)))))

(define stv-hid-split
  :parents (stv-expand)
  :short "Splits up a HID into a list of instance names and a wire name."

  ((hid (and (vl2014::vl-expr-p hid)
             (vl2014::vl-hidexpr-p hid))))

  :returns (mv (instnames true-listp :rule-classes :type-prescription)
               (wirename stringp :rule-classes :type-prescription))

  (b* (((unless (vl2014::vl-hidexpr-resolved-p hid))
        (raise "HID has unresolved indices: ~s0~%" (vl2014::vl-pps-expr hid))
        (mv nil ""))
       (parts (vl2014::vl-explode-hid hid))
       ((unless (string-listp parts))
        ;; Parts is like ("foo" "bar" 3 "baz") for foo.bar[3].baz, too hard
        (raise "We don't currently support hierarchical identifiers that go ~
                through array instances, like foo.bar[3].baz.  The HID that ~
                triggered this error was: ~s0~%" (vl2014::vl-pps-expr hid))
        (mv nil ""))
       ((when (< (len parts) 2))
        ;; I don't really see how this could happen.  Maybe it can't happen.
        (raise "Somehow the HID has only one piece?  ~s0~%"
               (vl2014::vl-pps-expr hid))
        (mv nil ""))
       (instnames (butlast parts 1))
       (wirename  (car (last parts))))
    (mv instnames wirename))

  ///
  (defthm string-listp-of-stv-hid-split
    (string-listp (mv-nth 0 (stv-hid-split hid)))))


(define stv-hid-parse
  :parents (stv-expand)
  :short "Match a Verilog-style plain or hierarchical name, perhaps with a bit-
or part-select on the end of it."

  :long "<p>This is sort of misnamed; it works for normal identifiers as well
as hierarchical identifiers.</p>

<p>Examples:</p>

@({
                       instnames    wirename   msb    lsb
 foo[3]           -->  nil          foo        3      3
 foo.bar.baz      -->  (foo bar)    baz        nil    nil
 foo.bar.baz[3]   -->  (foo bar)    baz        3      3
 foo.bar.baz[3:0] -->  (foo bar)    baz        3      0
})

<p>If the input string name isn't of an acceptable form, we cause an
error.</p>"

  ((str stringp "The string to parse and split up."))

  :returns
  (mv (instnames true-listp :rule-classes :type-prescription)
      (wirename  stringp    :rule-classes :type-prescription)
      (msb-idx   (or (not msb-idx) (natp msb-idx)) :rule-classes :type-prescription)
      (lsb-idx   (or (not lsb-idx) (natp lsb-idx)) :rule-classes :type-prescription))

  (b* ((expr (vl2014::vl-parse-expr-from-str str))
       ((unless expr)
        (raise "Failed to parse: ~s0" str)
        (mv nil "" nil nil))
       ((mv err from msb lsb) (stv-maybe-match-select expr))
       ((when err)
        (raise "~s0" err)
        (mv nil "" nil nil))

       ((when (vl2014::vl-idexpr-p from))
        ;; This is legitimate for top-level internal wires like foo[3]; There
        ;; just aren't any instnames to follow.
        (mv nil (vl2014::vl-idexpr->name from) msb lsb))

       ((unless (vl2014::vl-hidexpr-p from))
        (raise "Invalid STV wire name: ~s0" str)
        (mv nil "" nil nil))

       ((mv instnames wirename) (stv-hid-split from)))
    (mv instnames wirename msb lsb))

  ///

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



(define stv-turn-bits-into-non-canonical-paths
  :parents (stv-hid-to-paths)
  ((instname-list  true-listp
                   "e.g., (foo bar)")
   (bits           "e.g., (baz[3] baz[2] baz[1] baz[0])"))
  :returns (merged "e.g., @({
                               ((foo bar . baz[3])
                                (foo bar . baz[2])
                                ...
                                (foo bar . baz[0]))
                          })")
  (if (atom bits)
      nil
    (cons (append instname-list (car bits))
          (stv-turn-bits-into-non-canonical-paths instname-list (cdr bits)))))


(define stv-hid-to-paths
  :parents (stv-expand)
  :short "Convert a Verilog-style plain or hierarchical name (optionally with a
bit- or part-select) into an LSB-ordered list of <b>non-canonical</b> ESIM
paths."

  ((x stringp "A string like @('foo'), @('foo[3:0]'), @('foo.bar.baz'),
               @('foo.bar.baz[3]'), etc.  That is, it should either be a plain
               or hierarchical Verilog identifier, perhaps with a bit or
               part-select on the end.")

   (mod "The @(see esim) module that this path should be relative to."))

  :returns (lsb-paths "LSB-first list of non-canonical paths for @('x'), in the
                       sense of @(see acl2::mod-internal-paths).")

  (b* (((mv instnames wirename msb lsb) (stv-hid-parse x))

       ;; 1. Find the submod that this HID points to.
       (instnames (str::intern-list instnames))
       (submod    (follow-esim-path instnames mod))
       ((unless submod)
        (raise "Error following path ~x0 in ~x1." x (gpl :n mod)))

       ;; 2. Look up this E names for this wire in the wire alist.  Note that
       ;; the WALIST has the bits in MSB-First order!
       (walist (vl2014::esim-vl-wirealist submod))
       (lookup (hons-assoc-equal wirename walist))
       ((unless lookup)
        (raise "Can't follow ~s0: followed the instances ~x1 to an ~x2 ~
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
        (vl2014::vl-emodwires-from-msb-to-lsb wirename lsb msb))

       ;; Make sure that the bits exist and are properly ordered for this wire
       ((unless (ordered-subsetp expect-bits lsb-first-wires))
        (raise "Trying to expand ~s0, but the bits being asked for ~s1.~% ~
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

    (stv-turn-bits-into-non-canonical-paths instnames expect-bits)))

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
   ;; -- good, superior module's wire, 64-127

  ||#


(define stv-check-noncanonical-paths (paths mod)
  :parents (stv-expand)
  :short "Checks that the listed paths all exist in the module"
  (b* (((when (atom paths)) nil)
       (path (car paths))
       (submod (follow-esim-path path mod))
       (wirename (if (atom path) path (cdr (last path)))))
    (if (and wirename (symbolp wirename))
        (or (member-of-pat-flatten wirename (gpl :i submod))
            (find-in-occs-field :o wirename (gpl :occs submod))
            (raise "Path ~x0 does not exist" path))
      (raise "~x0 is not a valid wirename" wirename))
    (stv-check-noncanonical-paths (cdr paths) mod)))




(define stv-expand-hid
  :parents (stv-expand)
  :short "@(call stv-expand-hid) expands a signal name when it is allowed to be
hierarchical, i.e. a hid or a list of esim paths."
  :returns (lsb-paths "LSB-first list of non-canonical paths for @('x'), in the
                       sense of @(see acl2::mod-internal-paths).")
  ((name "the name at the start of the STV line")
   mod)

  (if (stringp name)
      ;; assume it's a hid
      (stv-hid-to-paths name mod)
    (prog2$ (stv-check-noncanonical-paths name mod)
            name)))

(define stv-expand-hids-in-lines
  :parents (stv-expand)
  :short "@(call stv-expand-hids-in-lines) expands all of the HIDs in a list of
STV internal lines into lists of esim paths."
  ((lines true-list-listp) mod)
  :returns (new-lines "Copy of @('lines') except with expanded names.")

  (b* (((when (atom lines))
        nil)
       (line1              (car lines))
       ((cons name phases) line1)
       (lsb-paths (stv-expand-hid name mod)))
    (cons (cons lsb-paths phases)
          (stv-expand-hids-in-lines (cdr lines) mod)))
  ///
  (defthm alistp-of-stv-expand-hids-in-lines
    (alistp (stv-expand-hids-in-lines lines mod)))
  (defthm true-list-listp-of-stv-expand-hids-in-lines
    (implies (true-list-listp lines)
             (true-list-listp (stv-expand-hids-in-lines lines mod)))))



(define stv-expand
  :parents (symbolic-test-vectors)
  :short "Expand Verilog-style names throughout an STV into LSB-ordered ESIM
style paths."


  ((stv stvdata-p)
   mod)
  :returns (new-stv stvdata-p :hyp :fguard
                    "Copy of @('stv') but with all names expanded.")

  :long "<p>This is an STV preprocessing step which can be run before or after
@(see stv-widen).  It only affects the names in each STV line.</p>

<p>During this step, we resolve Verilog-style names like \"foo[3:0]\" and
\"foo.bar.baz[6:0],\" replacing them with LSB-ordered lists of ESIM bits or
paths.  This keeps the Verilog-specific stuff out of the rest of the STV
compiler.</p>"

  (b* (((stvdata stv) stv))
    (make-stvdata :inputs    (stv-expand-names-in-lines stv.inputs :i mod)
                  :outputs   (stv-expand-names-in-lines stv.outputs :o mod)
                  :internals (stv-expand-hids-in-lines stv.internals mod)
                  :overrides (stv-expand-hids-in-lines stv.overrides mod))))

