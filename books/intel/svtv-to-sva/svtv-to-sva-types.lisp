; Copyright (C) Intel Corporation
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

(in-package "SV")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/strings/hexify" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(include-book "centaur/sv/svex/4vec" :dir :system)

;;;;

;; This type is a concession needed to document dimensions of arrays in order
;; to get the generated references correct, could pull from other sources
;; but would prefer to keep this as "only with svtv and env" as possible..

(fty::defalist svtv-sva-sizes
  :key-type stringp
  :val-type posp
  :true-listp t)

(fty::defalist svtv-out-sizes
  :key-type symbolp
  :val-type posp
  :true-listp t)

(fty::defalist svtv-run-tbl
  :key-type symbolp
  :val-type stringp
  :true-listp t)

(fty::deflist string-list-list
  :elt-type string-listp
  :true-listp t)

(defthm string-list-list-nth
  (implies (string-list-list-p x)
           (string-listp (nth i x)))
  :hints (("Goal" :in-theory (enable string-list-list-p))))

(fty::defprod svtv-sva-cfg
  :parents (|Generating SVAs from SVTVs|)
  :short "Configuration structure and state for generating SVAs from SVTVs"
  ((run-name        symbolp            "name of run or svtv basis")
   (target-mod      stringp            "name of target module that prop-mod should be bound" :default '"")
   (clk             stringp            "base clock name used for design" :default '"")
   (rst             stringp            "reset signal name used for design" :default '"")
   (out-file        stringp            "name of the file used for sva output" :default '"")
   (tmp-dir         stringp            "name of the directory used for temporary sva output" :default '"")
   (prop-mod        stringp            "name of the surrounding module for properties" :default '"")
   (repo-path       stringp            "path to the top of current repo" :default '"")
   (make-cmd        stringp            "generated make command to be run for Jasper" :default '"")
   (cp-cmd          stringp            "copy command for copying the generated files" :default '"")
   (out-sizes       svtv-out-sizes-p   "alist mapping output symbol names to sizes")
   (sizes           svtv-sva-sizes-p   "list of any svtv var dimensions needed to generate correct ref.s")
   (needs-xmr       string-listp       "list of ins and outs which need xmrs when we are abusing xmrs")
   (out-vars        symbol-listp       "list of vars which should be ignored for input assumptions")
   (abuse-xmrs      booleanp           "use xmrs for all non-clock/reset ref.s to utilize variable structure better" :default 't)
   (double-clock    booleanp           "sets whether we have both clock edges or a single clock phase")
   (disable-prune   booleanp           "disable pruning of svtv phases to only include relevant phases")
   (negate-conclude booleanp           "negate the conclusion to check for non match of results")
   (filename-suffix stringp            "suffix for generated sva filename, producing sva_generated&lt;suffix&gt;.sv" :default '"")))

;;;;

(define repeat-n ((n natp) x)
  :returns (r true-listp)
  (if (zp n) () (cons x (repeat-n (1- n) x))))

(defmacro alist-type-thms (name)
  (b* ((thm1 (intern-in-package-of-symbol
              (str::cat (symbol-name name) "-ALISTP")
              name))
       (thm2 (intern-in-package-of-symbol
              (str::cat (symbol-name name) "-ASSOC-EQUAL")
              name)))
    `(progn
       (defthm ,thm1
         (implies (,name x)
                  (alistp x))
         :hints (("Goal" :in-theory (enable ,name))))
       (defthm ,thm2
         (implies (and (,name x)
                       (assoc-equal e x))
                  (consp (assoc-equal e x)))
         :hints (("Goal" :in-theory (enable ,name)))))))

(alist-type-thms svtv-sva-sizes-p)
(alist-type-thms svtv-out-sizes-p)
(alist-type-thms svtv-run-tbl-p)

;;;;

;; some auxiliary functions used in translation:

(define mk-hex (x)
  :returns (r stringp)
  (b* ((x (str::hexify x)))
    (if (> (length x) 3)
        (subseq x 3 nil)
      (prog2$ (raise "unexpected result from hexify:~x0" x)
              ""))))

(define indent ((x string-listp))
  :returns (r string-listp)
  (if (endp x) ()
    (cons (str::cat "  " (first x))
          (indent (rest x)))))

(define add-conjuncts ((x string-listp))
  :returns (r string-listp)
  (if (endp x) ()
    (cons (if (endp (rest x))
              (acl2::str-fix (first x))
            (str::cat (first x) " && "))
          (add-conjuncts (rest x)))))
;;;;

(define char-to-verilog ((x characterp))
  :returns (r characterp :hyp :guard)
  (b* ((xc (char-code x)))
    (cond ((and (>= xc (char-code #\0))
                (<= xc (char-code #\9)))
           x)
          ((and (>= xc (char-code #\a))
                (<= xc (char-code #\z)))
           x)
          ((and (>= xc (char-code #\A))
                (<= xc (char-code #\Z)))
           (code-char (+ (- xc (char-code #\A))
                         (char-code #\a))))
          ((member x '(#\_ #\-))
           #\_)
          (t (prog2$ (raise "Don't know how to translate to verilog:~x0" x)
                     #\_)))))
         
(define chars-to-verilog ((x character-listp))
  :returns (r character-listp :hyp :guard)
  (if (endp x) ()
    (cons (char-to-verilog (first x))
          (chars-to-verilog (rest x)))))
          
(define symb-to-verilog ((x symbolp))
  :returns (r stringp)
  (coerce (chars-to-verilog (coerce (symbol-name x) 'list)) 'string))

;;;;

(define 4v-bit-to-str ((up integerp) (lo integerp))
  :returns (r stringp)
  (cond ((and (eql up 0) (eql lo 0))
         "0")
        ((and (eql up 1) (eql lo 1))
         "1")
        ((and (eql up 0) (eql lo 1))
         "Z")
        ((and (eql up 1) (eql lo 0))
         "X")
        (t (prog2$ (raise "expected 4vec-bit:~x0" (cons up lo))
                   ""))))

(define 4vec-to-ver-str ((upper integerp) (lower integerp) (n natp))
  :returns (r stringp)
  (if (zp n) ""
    (str::cat (4vec-to-ver-str (logcdr upper) (logcdr lower) (1- n))
              (4v-bit-to-str (logcar upper) (logcdr lower)))))

(define 4vec-to-verilog ((x sv::4vec-p) size)
  :returns (r stringp)
  (cond
    ((not (posp size))
     (prog2$ (raise "size should be posp:~x0" size)
             ""))
    ((integerp x)
     (str::cat (str::natstr size) "'h"
               (mk-hex (loghead size x))))
    (t
     (str::cat (str::natstr size) "'b"
               (4vec-to-ver-str (sv::4vec->upper x)
                                (sv::4vec->lower x)
                                size)))))

;;;;
