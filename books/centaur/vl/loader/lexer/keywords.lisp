; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../../util/defs")
(local (include-book "../../util/arithmetic"))
(include-book "std/testing/assert" :dir :system)

(defsection lex-keywords
  :parents (lexer)
  :short "Handling of keywords in the lexer."

  :long "<p>The @(see lexer) can be configured to accept different sets of
keywords.  This allows us to, e.g., recognize different keywords depending on
the particular @(see vl-edition-p) we are implementing.</p>

<p>No matter which set of keywords is being used, the general strategy is the
same: when we encounter a keyword such as @('inout'), we will produce a @(see
vl-plaintoken-p) whose type is, e.g., @(':vl-kwd-inout').</p>")

(local (xdoc::set-default-parents lex-keywords))

(defval *vl-2005-keywords*
  :short "IEEE STD 1364-2005, Annex B, List of Keywords."

  '("always"         "ifnone"               "rnmos"
    "and"            "incdir"               "rpmos"
    "assign"         "include"              "rtran"
    "automatic"      "initial"              "rtranif0"
    "begin"          "inout"                "rtranif1"
    "buf"            "input"                "scalared"
    "bufif0"         "instance"             "showcancelled"
    "bufif1"         "integer"              "signed"
    "case"           "join"                 "small"
    "casex"          "large"                "specify"
    "casez"          "liblist"              "specparam"
    "cell"           "library"              "strong0"
    "cmos"           "localparam"           "strong1"
    "config"         "macromodule"          "supply0"
    "deassign"       "medium"               "supply1"
    "default"        "module"               "table"
    "defparam"       "nand"                 "task"
    "design"         "negedge"              "time"
    "disable"        "nmos"                 "tran"
    "edge"           "nor"                  "tranif0"
    "else"           "noshowcancelled"      "tranif1"
    "end"            "not"                  "tri"
    "endcase"        "notif0"               "tri0"
    "endconfig"      "notif1"               "tri1"
    "endfunction"    "or"                   "triand"
    "endgenerate"    "output"               "trior"
    "endmodule"      "parameter"            "trireg"
    "endprimitive"   "pmos"                 "unsigned"
    "endspecify"     "posedge"              "use"
    "endtable"       "primitive"            "uwire"
    "endtask"        "pull0"                "vectored"
    "event"          "pull1"                "wait"
    "for"            "pulldown"             "wand"
    "force"          "pullup"               "weak0"
    "forever"        "pulsestyle_onevent"   "weak1"
    "fork"           "pulsestyle_ondetect"  "while"
    "function"       "rcmos"                "wire"
    "generate"       "real"                 "wor"
    "genvar"         "realtime"             "xnor"
    "highz0"         "reg"                  "xor"
    "highz1"         "release"
    "if"             "repeat"))

(defval *vl-2012-keywords*
  :short "IEEE STD 1800-2012, Table B-1, Reserved Keywords."

  '(;; Page 1145
    "accept_on"            "default"               "forkjoin"
    "alias"                "defparam"              "function"
    "always"               "design"                "generate"
    "always_comb"          "disable"               "genvar"
    "always_ff"            "dist"                  "global"
    "always_latch"         "do"                    "highz0"
    "and"                  "edge"                  "highz1"
    "assert"               "else"                  "if"
    "assign"               "end"                   "iff"
    "assume"               "endcase"               "ifnone"
    "automatic"            "endchecker"            "ignore_bins"
    "before"               "endclass"              "illegal_bins"
    "begin"                "endclocking"           "implements"
    "bind"                 "endconfig"             "implies"
    "bins"                 "endfunction"           "import"
    "binsof"               "endgenerate"           "incdir"
    "bit"                  "endgroup"              "include"
    "break"                "endinterface"          "initial"
    "buf"                  "endmodule"             "inout"
    "bufif0"               "endpackage"            "input"
    "bufif1"               "endprimitive"          "inside"
    "byte"                 "endprogram"            "instance"
    "case"                 "endproperty"           "int"
    "casex"                "endspecify"            "integer"
    "casez"                "endsequence"           "interconnect"
    "cell"                 "endtable"              "interface"
    "chandle"              "endtask"               "intersect"
    "checker"              "enum"                  "join"
    "class"                "event"                 "join_any"
    "clocking"             "eventually"            "join_none"
    "cmos"                 "expect"                "large"
    "config"               "export"                "let"
    "const"                "extends"               "liblist"
    "constraint"           "extern"                "library"
    "context"              "final"                 "local"
    "continue"             "first_match"           "localparam"
    "cover"                "for"                   "logic"
    "covergroup"           "force"                 "longint"
    "coverpoint"           "foreach"               "macromodule"
    "cross"                "forever"               "matches"
    "deassign"             "fork"                  "medium"

    ;; Page 1146
    "modport"              "reject_on"             "time"
    "module"               "release"               "timeprecision"
    "nand"                 "repeat"                "timeunit"
    "negedge"              "restrict"              "tran"
    "nettype"              "return"                "tranif0"
    "new"                  "rnmos"                 "tranif1"
    "nexttime"             "rpmos"                 "tri"
    "nmos"                 "rtran"                 "tri0"
    "nor"                  "rtranif0"              "tri1"
    "noshowcancelled"      "rtranif1"              "triand"
    "not"                  "s_always"              "trior"
    "notif0"               "s_eventually"          "trireg"
    "notif1"               "s_nexttime"            "type"
    "null"                 "s_until"               "typedef"
    "or"                   "s_until_with"          "union"
    "output"               "scalared"              "unique"
    "package"              "sequence"              "unique0"
    "packed"               "shortint"              "unsigned"
    "parameter"            "shortreal"             "until"
    "pmos"                 "showcancelled"         "until_with"
    "posedge"              "signed"                "untyped"
    "primitive"            "small"                 "use"
    "priority"             "soft"                  "uwire"
    "program"              "solve"                 "var"
    "property"             "specify"               "vectored"
    "protected"            "specparam"             "virtual"
    "pull0"                "static"                "void"
    "pull1"                "string"                "wait"
    "pulldown"             "strong"                "wait_order"
    "pullup"               "strong0"               "wand"
    "pulsestyle_ondetect"  "strong1"               "weak"
    "pulsestyle_onevent"   "struct"                "weak0"
    "pure"                 "super"                 "weak1"
    "rand"                 "supply0"               "while"
    "randc"                "supply1"               "wildcard"
    "randcase"             "sync_accept_on"        "wire"
    "randsequence"         "sync_reject_on"        "with"
    "rcmos"                "table"                 "within"
    "real"                 "tagged"                "wor"
    "realtime"             "task"                  "xnor"
    "ref"                  "this"                  "xor"
    "reg"                  "throughout"))

(assert! (subsetp-equal *vl-2005-keywords* *vl-2012-keywords*))

(defval *vl-extra-keywords*
  :short "Special, extra keywords that are aren't part of the Verilog
standards, but are instead added by VL."

  :long "<p>There's nothing here.  Originally we had added some keyword as part
of a special, VL-only \"overrides\" mechanism.  I leave this list here in case
we ever want to add our own keywords again.</p>"

  '(;; "VL_OVERRIDE"
    ;; "VL_ORIGINAL"
    ;; "VL_REPLACEMENT"
    ;; "VL_REQUIRE"
    ;; "VL_ENDOVERRIDE"
    ))

(define vl-make-keyword-table ((x string-listp))
  :short "A keyword table binds the names of keywords (strings) to their
corresponding @(':vl-kwd-xxx') symbols."
  :returns (fast-alist)
  (if (consp x)
      (hons-acons (car x)
                  (intern (cat "VL-KWD-" (str::upcase-string (car x))) "KEYWORD")
                  (vl-make-keyword-table (cdr x)))
    nil))

(defval *vl-2005-keyword-table-strict*
  :showval t
  (vl-make-keyword-table *vl-2005-keywords*))

(defval *vl-2005-keyword-table*
  :showval t
  (vl-make-keyword-table (append *vl-extra-keywords* *vl-2005-keywords*)))

(defval *vl-2012-keyword-table-strict*
  :showval t
  (vl-make-keyword-table *vl-2012-keywords*))

(defval *vl-2012-keyword-table*
  :showval t
  (vl-make-keyword-table (append *vl-extra-keywords* *vl-2012-keywords*)))

(assert! (uniquep (alist-keys *vl-2012-keyword-table*)))
(assert! (uniquep (alist-vals *vl-2012-keyword-table*)))

(assert! (subsetp-equal *vl-2005-keyword-table-strict*
                        *vl-2012-keyword-table*))

(assert! (subsetp-equal *vl-2005-keyword-table*
                        *vl-2012-keyword-table*))

(assert! (subsetp-equal *vl-2005-keyword-table-strict*
                        *vl-2012-keyword-table-strict*))

(assert! (subsetp-equal *vl-2012-keyword-table-strict*
                        *vl-2012-keyword-table*))


(define vl-full-keyword-table ()
  :short "A fast alist binding all currently supported keyword names to
their corresponding @(':vl-kwd-xxx') symbols."
  *vl-2012-keyword-table*
  ///
  (in-theory (disable (:executable-counterpart vl-full-keyword-table)))

  (defthm symbol-listp-of-alist-vals-of-vl-full-keyword-table
    (symbol-listp (alist-vals (vl-full-keyword-table))))

  (defthm symbolp-of-lookup-in-vl-full-keyword-table
    (symbolp (cdr (hons-assoc-equal key (vl-full-keyword-table))))))


(define vl-keyword-table-p (x)
  :short "Recognize any valid subset of the @(see vl-full-keyword-table)."
  (or (atom x)
      (and (consp (car x))
           (equal (car x) (hons-get (caar x) (vl-full-keyword-table)))
           (vl-keyword-table-p (cdr x))))
  ///
  (assert! (vl-keyword-table-p *vl-2005-keyword-table-strict*))
  (assert! (vl-keyword-table-p *vl-2005-keyword-table*))
  (assert! (vl-keyword-table-p *vl-2012-keyword-table-strict*))
  (assert! (vl-keyword-table-p *vl-2012-keyword-table*))

  (defthm vl-keyword-table-p-of-vl-full-keyword-table
    (vl-keyword-table-p (vl-full-keyword-table))
    :hints(("Goal" :in-theory (executable-counterpart-theory :here))))

  (defthm symbol-listp-of-alist-vals-when-vl-keyword-table-p
    (implies (vl-keyword-table-p x)
             (symbol-listp (alist-vals x))))

  (defthm symbolp-of-lookup-when-vl-keyword-table-p
    (implies (vl-keyword-table-p table)
             (symbolp (cdr (hons-assoc-equal key table))))))


(define vl-keyword-lookup
  :short "Determine if a string is a Verilog keyword."
  ((x     stringp
          "An identifier that has just been lexed, which may or may not
           be a valid Verilog keyword.")
   (table vl-keyword-table-p
          "Table of currently acceptable keywords."))
  :returns
  (sym "When @('x') is a keyword, the associated @(':vl-kwd-???') symbol;
        otherwise @('nil').")
  :inline t
  ;; BOZO generalize me to handle variable keyword tables.
  (cdr (hons-get x table))
  ///
  (defthm symbolp-of-vl-keyword-lookup
    (implies (vl-keyword-table-p table)
             (symbolp (vl-keyword-lookup x table)))))
