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
;
; This is a big pile of code to do something very simple.  We want to be able
; to write STVs with Verilog names like "foo[3:0]" and "foo.bar.baz[6:0]", and
; have everything just work.  But that means we need to be able to convert
; these names into the right E bits, etc.  This turns out to be very, very
; tricky because we have to follow modules, deal with canonical versus
; non-canonical paths, and so forth.

(in-package "VL")

#||

;; For testing, it's good to have some modules available

(include-book
 "tools/plev" :dir :system)
(include-book
  "../../../proofs/acl2cn/acl2cn")
(acl2::cn-install :cnr)

||#

(include-book "esim-vl")
(include-book "esim-paths")
(include-book "centaur/vl/mlib/hid-tools" :dir :system)
(include-book "centaur/vl/loader/lexer" :dir :system)
(include-book "centaur/vl/loader/parse-expressions" :dir :system)
(include-book "centaur/vl/loader/parse-error" :dir :system)
(local (include-book "centaur/vl/util/arithmetic" :dir :system))
(local (include-book "esim-sexpr-support-thms"))



(defund ordered-subsetp (x y)
  ;; BOZO find me a home
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (if (equal (car x) (car y))
               (ordered-subsetp (cdr x) (cdr y))
             (ordered-subsetp x (cdr y))))
    t))

(defund intern-list-in-package-of-symbol (x y)
  ;; BOZO find me a home
  (declare (xargs :guard (and (string-listp x)
                              (symbolp y))))
  (if (atom x)
      nil
    (cons (intern-in-package-of-symbol (car x) y)
          (intern-list-in-package-of-symbol (cdr x) y))))


; -----------------------------------------------------------------------------
;
;               EXPANDING INPUT AND OUTPUT NAMES INTO E NAMES
;
; -----------------------------------------------------------------------------

(defsection vl-parse-expr-from-str

; It seems nice to just piggy-back on VL's verilog parser, and read in the
; expressions from STV lines as real Verilog expressions.  This gives us
; automatic support for hierarchical identifiers, escaped identifiers, etc.

  (defund vl-parse-expr-from-str (str)
    (declare (xargs :guard (stringp str)))
    (b* ((echars (vl-echarlist-from-str str))
         ((mv successp tokens warnings) (vl-lex echars nil))
         ((unless successp)
          (er hard? 'vl-parse-expr-from-str "Lexing failed for ~s0." str))
         ((when warnings)
          (vl-cw-ps-seq
           (vl-println "Warnings from VL-PARSE-EXPR-FROM-STR:")
           (vl-print-warnings warnings))
          (er hard? 'vl-parse-expr-from-str "Lexing produced warnings for ~s0." str))
         ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
         ((mv err val tokens warnings) (vl-parse-expression tokens nil))
         ((when err)
          (vl-report-parse-error err tokens)
          (er hard? 'vl-parse-expr-from-str "Parsing failed for ~s0.~%" str))
         ((when warnings)
          (vl-cw-ps-seq
           (vl-println "Warnings from VL-PARSE-EXPR-FROM-STR:")
           (vl-print-warnings warnings))
          (er hard? 'vl-parse-expr-from-str "Parsing produced warnings for ~s0." str))
         ((when tokens)
          (er hard? 'vl-parse-expr-from-str
              "Content remains after parsing an expression from the string.~% ~
              - Original string: ~s0~% ~
              - First expr: ~s1~% ~
              - Remaining after parse: ~s2~%"
              str
              (vl-pps-expr val)
              (vl-tokenlist->string-with-spaces tokens))))
      val))

  (local (in-theory (enable vl-parse-expr-from-str)))

  (defthm vl-expr-p-of-vl-parse-expr-from-string
    (equal (vl-expr-p (vl-parse-expr-from-str str))
           (if (vl-parse-expr-from-str str)
               t
             nil))))


 #||

;; some test cases:

(vl-parse-expr-from-str "foo[3]")     ;; works, bitselect
(vl-parse-expr-from-str "foo[3:0]")   ;; works, partselect
(vl-parse-expr-from-str "foo")        ;; works, simple id
(vl-parse-expr-from-str "foo, bar")   ;; error -- content remains, good
 ||#


(defsection stv-maybe-match-select

  (defund stv-maybe-match-select (x)
    "Returns (MV FROM MAYBE-MSB MAYBE-LSB)"
    (declare (xargs :guard (vl-expr-p x)))
    (b* (((unless (vl-nonatom-p x))
          (mv x nil nil))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))

         ((when (eq op :vl-partselect-colon))
          (b* ((from (first args))
               (msb  (second args))
               (lsb  (third args))
               ((unless (and (vl-expr-resolved-p msb)
                             (vl-expr-resolved-p lsb)))
                (er hard? 'stv-maybe-match-select
                    "Part select indicies are not resolved: ~s0"
                    (vl-pps-expr x))
                (mv x nil nil)))
            (mv from (vl-resolved->val msb) (vl-resolved->val lsb))))

         ((when (eq op :vl-bitselect))
          (b* ((from (first args))
               (bit  (second args))
               ((unless (vl-expr-resolved-p bit))
                (er hard? 'stv-maybe-match-select
                    "Bit select index is not resolved: ~s0"
                    (vl-pps-expr x))
                (mv x nil nil))
               (val (vl-resolved->val bit)))
            (mv from val val))))
      (mv x nil nil)))

  (local (in-theory (enable stv-maybe-match-select)))

  (defthm vl-expr-of-stv-maybe-match-select
    (implies (force (vl-expr-p x))
             (vl-expr-p (mv-nth 0 (stv-maybe-match-select x)))))

  (defmvtypes stv-maybe-match-select (nil vl-maybe-natp vl-maybe-natp)))



(defsection stv-wirename-parse
  :parents (stv-expand-name)
  :short "Match a Verilog-style wire name, bit-select, or part-select."

  :long "<p><b>Signature:</b> @(call stv-wirename-parse) returns <tt>(mv
basename msb-idx lsb-idx)</tt></p>

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
    (b* ((expr (vl-parse-expr-from-str str))
         ((unless expr)
          (er hard? 'stv-wirename-parse "Failed to parse: ~s0" str)
          (mv "" nil nil))
         ((mv from msb lsb) (stv-maybe-match-select expr))
         ((unless (vl-idexpr-p from))
          (er hard? 'stv-wirename-parse "Invalid STV wire name: ~s0~%" str)
          (mv "" nil nil)))
      (mv (vl-idexpr->name from) msb lsb)))

  (defmvtypes stv-wirename-parse
    (stringp vl-maybe-natp vl-maybe-natp))

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
  :parents (acl2::stv-expand-names)
  :short "Expand a name from a symbolic test vector's line into explicit lists
of E bits."

  :long "<p><b>Signature:</b> @(call stv-expand-name) returns an LSB-first list
of E bits for any valid STV signal name.</p>

<p>As described in @(see acl2::symbolic-test-vectors), the signal names for STV
lines can be either:</p>

<ul>
<li>A string that names a particular input bus,</li>
<li>A string that is a Veriog-style bit- or part-select from a particular input
bus, or</li>
<li>An explicit list of E bits (in LSB-first order).</li>
</ul>

<p>This function is given <tt>x</tt>, the actual name that occurs in an STV
line.  Our goal is to convert <tt>x</tt> into its explicit bit list form.  If
it is already a list of bits then this is trivial.  Otherwise, we have to look
it up in the module.</p>

<p>Type is either <tt>:i</tt> or <tt>:o</tt> and says whether this should be
the name of an input or output, and <tt>mod</tt> is the whole E module so that
we can look up its inputs and outputs.</p>

<p>We do some basic error checking to make sure that the name refers to valid
input or output bits.</p>"

  (defund stv-expand-name (x type mod)
    "Returns an LSB-first list of bit names, e.g., (|foo[0]| |foo[1]| ...)."
    (declare (xargs :guard (symbolp type)))
    (b* ((pat     (acl2::gpl type mod))
         (modname (acl2::gpl :n mod))

         ((when (stringp x))
          (b* ( ;; Note: for plain names msb/lsb will be nil.
               ((mv basename msb lsb) (stv-wirename-parse x))
               (basename-bits         (esim-vl-find-io basename pat))
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
                (vl-emodwires-from-msb-to-lsb basename lsb msb))
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

         (flat-pat (acl2::pat-flatten1 pat))
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




; -----------------------------------------------------------------------------
;
;                       EXPANDING INTERNAL SIGNAL NAMES
;
; -----------------------------------------------------------------------------

; A first step is the purely syntactic matter of parsing the user's input.  We
; want to allow the user to write things like foo.bar.baz[3:0].  Actually it's
; worse than this because they might want to refer to an internal wire of the
; top module, or to an internal wire of a submodule.  So we first write a
; matcher that recognizes identifiers and simple hierarchical identifiers with
; optional bit/part selects.

(defsection stv-hid-split

  (defund stv-hid-split (hid)
    "Returns (MV INSTNAMES WIRENAME) or causes an error."
    (declare (xargs :guard (and (vl-expr-p hid)
                                (vl-hidexpr-p hid))))
    (b* (((unless (vl-hid-indicies-resolved-p hid))
          (er hard? 'stv-hid-split
              "HID has unresolved indices: ~s0~%" (vl-pps-expr hid))
          (mv nil ""))
         (parts (vl-explode-hid hid))
         ((unless (string-listp parts))
          ;; Parts is like ("foo" "bar" 3 "baz") for foo.bar[3].baz, too hard
          (er hard? 'stv-hid-split
              "We don't currently support hierarchical identifiers that go ~
             through array instances, like foo.bar[3].baz.  The HID that ~
             triggered this error was: ~s0~%" (vl-pps-expr hid))
          (mv nil ""))
         ((when (< (len parts) 2))
          ;; I don't really see how this could happen.  Maybe it can't happen.
          (er hard? 'stv-hid-split
              "Somehow the HID has only one piece?  ~s0~%"
              (vl-pps-expr hid))
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
    :hints(("goal" :use ((:instance l0 (x (vl-explode-hid hid)))))))

  (defthm string-listp-of-stv-hid-split
    (string-listp (mv-nth 0 (stv-hid-split hid)))))


(defsection stv-hid-parse
  :parents (stv-expand-hids)
  :short "Match a Verilog-style plain or hierarchical name, perhaps with a bit-
or part-select on the end of it."

  :long "<p><b>Signature:</b> @(call stv-hid-parse) returns <tt>(mv
instnames wirename msb-idx lsb-idx)</tt></p>

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
    (b* ((expr (vl-parse-expr-from-str str))
         ((unless expr)
          (er hard? 'stv-hid-parse "Failed to parse: ~s0" str)
          (mv nil "" nil nil))
         ((mv from msb lsb) (stv-maybe-match-select expr))

         ((when (vl-idexpr-p from))
          ;; This is legitimate for top-level internal wires like foo[3]; There
          ;; just aren't any instnames to follow.
          (mv nil (vl-idexpr->name from) msb lsb))

         ((unless (vl-hidexpr-p from))
          (er hard? 'stv-hid-parse "Invalid STV wire name: ~s0" str)
          (mv nil "" nil nil))

         ((mv instnames wirename) (stv-hid-split from)))
      (mv instnames wirename msb lsb)))

  (local (in-theory (enable stv-hid-parse)))

  (defmvtypes stv-hid-parse (true-listp stringp vl-maybe-natp vl-maybe-natp))

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





; -----------------------------------------------------------------------------
;
;            EXPANDING INTERNAL SIGNAL NAMES INTO CANONICAL PATHS
;
; -----------------------------------------------------------------------------

; This is subtle because we want to let the user write a path to any wire, but
; esim only produces paths to canonical wires.

(defsection stv-follow-path
  :parents (stv-expand-hids)
  :short "Walk down a list of instance names and retrieve the ESIM module they
refer to."

  :long "<p>@(call stv-follow-path) returns <tt>(mv successp result)</tt>.</p>

<p>We are given <tt>instnames</tt>, which should be a list of instance names,
and <tt>mod</tt>, which should be a good @(see esim) module.  We try to follow
these names down through the occurrences of <tt>mod</tt> and return the
submodule they point to.</p>

<p>On success, <tt>successp</tt> is <tt>t</tt> and the <tt>result</tt> is
itself a good esim module.</p>

<p>On failure, <tt>successp</tt> is <tt>nil</tt> and <tt>result</tt> is a short
string that says where the failure occurred.</p>"

  (defund stv-follow-path (instnames mod)
    "Returns (MV SUCCESSP SUBMOD)"
    (declare (xargs :guard (acl2::good-esim-modulep mod)))
    (b* (((when (atom instnames))
          (mv t mod))
         (name1 (car instnames))
         (occ   (cdr (hons-get name1 (acl2::occmap mod))))
         ((unless occ)
          (mv nil (str::cat "There is no submodule named "
                            (acl2::stringify name1)
                            " within module "
                            (acl2::stringify (acl2::gpl :n mod))))))
      (stv-follow-path (cdr instnames) (acl2::gpl :op occ))))

  (local (in-theory (enable stv-follow-path)))

  (defthm good-esim-modulep-of-stv-follow-path
    (implies (and (mv-nth 0 (stv-follow-path instnames mod))
                  (acl2::good-esim-modulep mod))
             (acl2::good-esim-modulep (mv-nth 1 (stv-follow-path instnames mod))))
    :hints(("Goal"
            :induct (stv-follow-path instnames mod)
            :in-theory (disable acl2::stringify acl2::good-esim-modulep)))))


  #||

some test cases:

(acl2::plev)

(stv-follow-path nil acl2::|*mmx*|)

(stv-follow-path (list 'acl2::|mmxdphi|
                       'acl2::|logicops001|)
                 acl2::|*mmx*|)
  ||#



(defsection stv-hid-to-paths
  :parents (acl2::stv-expand-hids)
  :short "Parse a Verilog-style plain or hierarchical name, perhaps with a bit-
or part-select on the end of it, into an LSB-ordered list of canonical ESIM
paths."

  :long "<p>@(call stv-hid-to-paths) returns a list of LSB-first
ordered paths in the sense of @(see acl2::mod-internal-paths).</p>

<ul>

<li><tt>x</tt> is a string like <tt>foo</tt>, <tt>foo[3:0]</tt>,
<tt>foo.bar.baz</tt>, <tt>foo.bar.baz[3]</tt>, etc.  That is, it should either
be a plain or hierarchical Verilog identifier, optionally with a bit or
part-select on the end.</li>

<li><tt>mod</tt> is the E module that X is based in.</li>

</ul>

<p>We use @(see stv-hid-parse) to normalize the HID into a list of instance
names, a wire name, and perhaps MSB/LSB indices.  We then use @(see
stv-follow-path) to go down to the right submodule.  Once we're there, we have
to look up this wire name and make sure the indicies are valid for it.  Finally
we jam the instance names back onto each bit of the answer to turn them into
paths, and canonicalize those paths.</p>"

  (defund stv-turn-bits-into-non-canonical-paths (instname-list bits)
    (declare (xargs :guard (true-listp instname-list)))
    (if (atom bits)
        nil
      (cons (append instname-list (car bits))
            (stv-turn-bits-into-non-canonical-paths instname-list (cdr bits)))))

  (defund stv-hid-to-paths (x mod)
    (declare (xargs :guard (and (stringp x)
                                (acl2::good-esim-modulep mod))))
    (b* (((mv instnames wirename msb lsb) (stv-hid-parse x))

         ;; 1. Find the submod that this HID points to.
         (instnames (intern-list-in-package-of-symbol instnames (pkg-witness "ACL2")))
         ((mv successp submod) (stv-follow-path instnames mod))
         ((unless successp)
          ;; naming bozo: submod is actually an error message in this case
          (er hard? 'stv-hid-to-paths "Can't follow ~s0: ~s1" x submod))

         ;; 2. Look up this E names for this wire in the wire alist.  Note that
         ;; the WALIST has the bits in MSB-First order!
         (walist (esim-vl-wirealist submod))
         (lookup (hons-assoc-equal wirename walist))
         ((unless lookup)
          (er hard? 'stv-hid-to-paths
              "Can't follow ~s0: followed the instances ~x1 to an ~x2 ~
               submodule, but then there was no wire named ~s3 in the wire ~
               alist." x instnames (acl2::gpl :n submod) wirename))
         (msb-first-wires (cdr lookup))
         (lsb-first-wires (reverse msb-first-wires))

         ((unless (and msb lsb))
          ;; X is something like "foo" or "foo.bar.baz" with no bit- or
          ;; part-select, so the user is asking for the whole wire!
          (b* ((nc-paths (stv-turn-bits-into-non-canonical-paths instnames lsb-first-wires))
               ((mv okp paths) (acl2::fast-canonicalize-paths nc-paths mod))
               ((unless okp)
                ;; Don't really expect this to happen... *maybe* it could happen
                ;; if you ask for a wire that exists in the Verilog but is not
                ;; driven?
                (er hard? 'stv-hid-to-paths
                    "failed to canonicalize all the paths for ~s0" x)))
            paths))

         ;; Otherwise, X is something like "foo[3]" or "foo.bar.baz[5:3]", so
         ;; we need to make sure this range is in bounds and going in the right
         ;; direction.
         (expect-bits
          ;; Stupid hack: it would be nicer to write:
          ;; (reverse (vl-emodwires-from-msb-to-lsb basename msb lsb))
          ;; But we just reverse the lsb/msb to avoid the extra consing
          (vl-emodwires-from-msb-to-lsb wirename lsb msb))

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
              (car (last expect-bits))))

         (nc-paths (stv-turn-bits-into-non-canonical-paths instnames expect-bits))
         ((mv okp paths) (acl2::fast-canonicalize-paths nc-paths mod))
         ((unless okp)
          ;; Don't really expect this to happen... *maybe* it could happen
          ;; if you ask for a wire that exists in the Verilog but is not
          ;; driven?
          (er hard? 'stv-hid-to-paths
              "failed to canonicalize all the paths for ~s0" x)))
      paths)))

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



