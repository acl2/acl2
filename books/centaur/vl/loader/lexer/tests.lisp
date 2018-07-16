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
(include-book "top")
(local (include-book "../../util/arithmetic"))

(program)


;; This will get run any time the book is included.
(make-event (prog2$ (cw "VL's lexer tests are being included.  You ~
                         almost certainly do not want to do this.~%")
                    (value '(value-triple :invisible)))
            :check-expansion t)


(defmacro vl-lex-op-testcase
  (&key input             ;; Input to lex
        successp          ;; Expected success/failure
        (remainder '"")   ;; Expected remainder
        type              ;; Expected resulting token type
        (config '*vl-default-loadconfig*) ;; Configuration to use
        (nwarnings '0))
  `(assert!
    (b* ((echars (vl-echarlist-from-str ,input))
         (breakp nil)
         (st     (vl-lexstate-init ,config))
         ((mv tok remainder warnings) (vl-lex-token echars breakp st nil))
         (- (cw "Echars: ~x0~%Tok: ~x1~%Remainder: ~x2~%Warnings:~x3~%"
                echars tok remainder warnings)))
        (debuggable-and ,@(if successp
                              `((vl-plaintoken-p tok)
                                (equal (vl-plaintoken->type tok) ,type)
                                (equal (append (vl-token->etext tok)
                                               remainder)
                                       echars)
                                (equal (vl-echarlist->string remainder) ,remainder)
                                (equal (len warnings) ,nwarnings)
                                )
                            `((not tok)
                              (equal remainder echars)
                              (equal (len warnings) ,nwarnings)))))))


(defconst *verilog-2005-punctuation-alist*
  '(("["   . :vl-lbrack)
    ("]"   . :vl-rbrack)
    ("("   . :vl-lparen)
    (")"   . :vl-rparen)
    ("{"   . :vl-lcurly)
    ("}"   . :vl-rcurly)
    (":"   . :vl-colon)
    ("+:"  . :vl-pluscolon)
    ("-:"  . :vl-minuscolon)
    (";"   . :vl-semi)
    ("#"   . :vl-pound)
    (","   . :vl-comma)
    ("."   . :vl-dot)
    ("@"   . :vl-atsign)
    ("(*"  . :vl-beginattr)
    ("*)"  . :vl-endattr)
    ("="   . :vl-equalsign)
    ("+"   . :vl-plus)
    ("-"   . :vl-minus)
    ("*"   . :vl-times)
    ("/"   . :vl-div)
    ("%"   . :vl-rem)
    ("**"  . :vl-power)
    ("^"   . :vl-xor)
    ("?"   . :vl-qmark)
    ("<"   . :vl-lt)
    ("<="  . :vl-lte)
    ("<<"  . :vl-shl)
    ("<<<" . :vl-ashl)
    (">"   . :vl-gt)
    (">="  . :vl-gte)
    (">>"  . :vl-shr)
    (">>>" . :vl-ashr)
    ("!==" . :vl-cne)
    ("!="  . :vl-neq)
    ("!"   . :vl-lognot)
    ("~&"  . :vl-nand)
    ("~|"  . :vl-nor)
    ("~^"  . :vl-xnor)
    ("^~"  . :vl-xnor)
    ("~"   . :vl-bitnot)
    ("||"  . :vl-logor)
    ("|"   . :vl-bitor)
    ("&&"  . :vl-logand)
    ("&"   . :vl-bitand)
    ("===" . :vl-ceq)
    ("=="  . :vl-eq)
    ("&&&" . :vl-andandand)))

(defconst *verilog-2012-punctuation-alist*
  (append *verilog-2005-punctuation-alist*
          '(("=>"   . :vl-eqarrow)
            ("->>"  . :vl-arrowgt)
            ("*>"   . :vl-stararrow)
            ("|->"  . :vl-bararrow)
            ("|=>"  . :vl-bareqarrow)
            ("<->"  . :vl-equiv)
            ("==?"  . :vl-wildeq)
            ("!=?"  . :vl-wildneq)
            (".*"   . :vl-dotstar)
            (":="   . :vl-coloneq)
            (":/"   . :vl-colonslash)
            ("::"   . :vl-scope)
            ("#-#"  . :vl-pounddash)
            ("#=#"  . :vl-poundequal)
            ("##"   . :vl-poundpound)
            ("+="   . :vl-pluseq)
            ("-="   . :vl-minuseq)
            ("*="   . :vl-timeseq)
            ("/="   . :vl-diveq)
            ("%="   . :vl-remeq)
            ("&="   . :vl-andeq)
            ("|="   . :vl-oreq)
            ("^="   . :vl-xoreq)
            ("<<="  . :vl-shleq)
            (">>="  . :vl-shreq)
            ("<<<=" . :vl-ashleq)
            (">>>=" . :vl-ashreq)
            ("'"    . :vl-quote)
            ("$"    . :vl-$)
            ("1step" . :vl-1step))))

(defun make-punctuation-tests (alist config)
  (b* (((when (atom alist))
        nil)
       (ans (make-punctuation-tests (cdr alist) config))
       (ans (list*
             ;; Does it work for OP itself?
             `(vl-lex-op-testcase :input ,(caar alist)
                                  :config ',config
                                  :successp t
                                  :type ,(cdar alist))
             ;; How about for "OP foo"?
             `(vl-lex-op-testcase :input ,(cat (caar alist) " foo")
                                  :config ',config
                                  :successp t
                                  :remainder " foo"
                                  :type ,(cdar alist))
             ans))
       (ans
        ;; How about for "OP1"?  This doesn't work for $1, because that's a
        ;; valid system identifier.  So, gross hack to avoid that.  It also
        ;; doesn't work for quote, because '1 is an extended integer, so
        ;; another gross hack to avoid that.
        (if (or (equal (caar alist) "$")
                (equal (caar alist) "'"))
            ans
          (cons `(vl-lex-op-testcase :input ,(cat (caar alist) "1")
                                     :config ',config
                                     :successp t
                                     :remainder "1"
                                     :type ,(cdar alist))
                ans))))
    ans))



(make-event
 `(progn
    (value-triple (cw "Checking operator handling for Verilog-2005.~%"))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-loadconfig :edition :verilog-2005
                                                  :strictp nil))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-loadconfig :edition :verilog-2005
                                                  :strictp t))
    (value-triple (cw "Checking old operator handling for SystemVerilog-2012.~%"))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-loadconfig :edition :system-verilog-2012
                                                  :strictp nil))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-loadconfig :edition :system-verilog-2012
                                                  :strictp t))
    (value-triple (cw "Checking new operator handling for SystemVerilog-2012.~%"))
    ,@(make-punctuation-tests *verilog-2012-punctuation-alist*
                              (make-vl-loadconfig :edition :system-verilog-2012
                                                  :strictp nil))
    ,@(make-punctuation-tests *verilog-2012-punctuation-alist*
                              (make-vl-loadconfig :edition :system-verilog-2012
                                                  :strictp t))
    ))



(defun make-keyword-tests (alist config)
  (if (consp alist)
      (list* `(vl-lex-op-testcase :input ,(caar alist)
                                  :successp t
                                  :config ',config
                                  :type ,(cdar alist))
             `(vl-lex-op-testcase :input ,(cat (caar alist) " foo")
                                  :successp t
                                  :config ',config
                                  :remainder " foo"
                                  :type ,(cdar alist))
             (make-keyword-tests (cdr alist) config))
    nil))

;; BOZO generalize to other keywords, etc.
(make-event
 `(progn ,@(make-keyword-tests *vl-2005-keyword-table-strict*
                               (make-vl-loadconfig :edition :verilog-2005
                                                   :strictp t))
         ,@(make-keyword-tests *vl-2005-keyword-table*
                               (make-vl-loadconfig :edition :verilog-2005
                                                   :strictp nil))
         ,@(make-keyword-tests *vl-2012-keyword-table-strict*
                               (make-vl-loadconfig :edition :system-verilog-2012
                                                   :strictp t))
         ,@(make-keyword-tests *vl-2012-keyword-table*
                               (make-vl-loadconfig :edition :system-verilog-2012
                                                   :strictp nil))
         ))



(defaggregate strtest
  ((input     stringp)
   (successp  booleanp :default t)
   (expansion maybe-stringp)
   (remainder stringp :default "")
   (nwarnings natp    :default 0)))

(deflist strtest-list-p (x)
  (strtest-p x))

(define strtest-okp ((test strtest-p)
                     (config vl-loadconfig-p))
  (b* (((strtest test) test)
       (echars    (vl-echarlist-from-str test.input))
       (st        (vl-lexstate-init config))
       (breakp    nil)
       ((mv tok remainder) (vl-lex-string echars breakp st))
       (- (cw "Echars: ~x0~%"      (vl-echarlist->string echars)))
       (- (cw "Result: ~x0~%"      (and (vl-stringtoken-p tok)
                                        (vl-stringtoken->expansion tok))))
       (- (cw "Remainder: ~x0~%~%" (vl-echarlist->string remainder)))

       ;; Also check vl-lex-token instead of just vl-lex-string...
       ((mv lextok lexrem warnings) (vl-lex-token echars breakp st nil))

       ((unless test.successp)
        (debuggable-and (not tok)
                        (equal remainder echars)
                        (not (cw "lex-string failed, as required.~%"))
                        ;; full lexer ok?
                        (equal tok lextok)
                        (equal remainder lexrem)
                        (equal (len warnings) test.nwarnings)
                        (not (cw "lex-token failed, as required.~%")))))
    (debuggable-and
     ;; Success and got the right thing?
     (vl-stringtoken-p tok)
     (equal (vl-stringtoken->expansion tok) test.expansion)
     (equal (vl-echarlist->string remainder) test.remainder)
     ;; Preserved all characters?
     (equal (append (vl-token->etext tok) remainder) echars)
     (not (cw "lex-string result seems ok.~%"))
     ;; Now try vl-lex (instead of vl-lex-string).
     ;; Does it get the same answer?
     (equal tok lextok)
     (equal remainder lexrem)
     (equal (len warnings) test.nwarnings)
     (not (cw "lex-token result seems ok.~%")))))

(define run-strtest ((test strtest-p)
                     (config vl-loadconfig-p))
  (or (strtest-okp test config)
      (raise "test failed: ~x0.~%" test)))

(deflist run-strtests (x config)
  :guard (and (strtest-list-p x)
              (vl-loadconfig-p config))
  (run-strtest x config))



; Should succeed string tests

(defconst *strtests1*
  (list
   (make-strtest :input "\"Hello\""
                 :expansion "Hello")
   (make-strtest :input "\"Hello\" world"
                 :remainder " world"
                 :expansion "Hello")

   (make-strtest :input "\"\\103allista\""
                 :expansion "Callista")

   (make-strtest :input "\"my \\44.02\""
                 :expansion "my $.02")

   (make-strtest :input "\"crazy \\7\""
                 :expansion (cat "crazy "
                                 (implode (list (code-char 7)))))

   (make-strtest :input "\"\\\\ another \\n basic \\t escape \\\" test\""
                 :expansion (cat "\\ another "
                                 (implode (list #\Newline))
                                 " basic "
                                 (implode (list #\Tab))
                                 " escape \" test"))

   (make-strtest :input "\"not terminated"
                 :successp nil)

   (make-strtest :input "\"out of range \\400 octal sequence\""
                 :successp nil)

   (make-strtest :input "\"not closed before
                           newline\""
                 :successp nil)

   (make-strtest :input "\"octal with x digit \\01x not ok\"" :successp nil)
   (make-strtest :input "\"octal with X digit \\01X not ok\"" :successp nil)
   (make-strtest :input "\"octal with z digit \\01z not ok\"" :successp nil)
   (make-strtest :input "\"octal with z digit \\01? not ok\"" :successp nil)
   (make-strtest :input "\"octal with z digit \\01Z not ok\"" :successp nil)

   (make-strtest :input "\"octal with x digit \\01x\"" :successp nil)
   (make-strtest :input "\"octal with z digit \\01z\"" :successp nil)
   (make-strtest :input "\"octal with z digit \\01?\"" :successp nil)
   (make-strtest :input "\"octal with z digit \\01X\"" :successp nil)
   (make-strtest :input "\"octal with z digit \\01Z\"" :successp nil)))

(progn
  (assert!
   (run-strtests *strtests1*
                 (make-vl-loadconfig :edition :verilog-2005
                                     :strictp nil)))
  (assert!
   (run-strtests *strtests1*
                 (make-vl-loadconfig :edition :verilog-2005
                                     :strictp t)))

  (assert!
   (run-strtests *strtests1*
                 (make-vl-loadconfig :edition :system-verilog-2012
                                     :strictp nil)))
  (assert!
   (run-strtests *strtests1*
                 (make-vl-loadconfig :edition :system-verilog-2012
                                     :strictp t))))


(defconst *strtests2*
  ;; Tests for SystemVerilog that must fail in ordinary Verilog.
  (list
   (make-strtest :input "\"system verilog \\f escape\""
                 :expansion (cat "system verilog "
                                 (implode (list (code-char 12)))
                                 " escape"))

   (make-strtest :input "\"system verilog escape \\f\""
                 :expansion (cat "system verilog escape "
                                 (implode (list (code-char 12)))))

   (make-strtest :input "\"system verilog \\a escape\""
                 :expansion (cat "system verilog "
                                 (implode (list (code-char 7)))
                                 " escape"))

   (make-strtest :input "\"system verilog escape \\a\""
                 :expansion (cat "system verilog escape "
                                 (implode (list (code-char 7)))))

   (make-strtest :input "\"system verilog \\v escape\""
                 :expansion (cat "system verilog "
                                 (implode (list (code-char 11)))
                                 " escape"))

   (make-strtest :input "\"system verilog escape \\v\""
                 :expansion (cat "system verilog escape "
                                 (implode (list (code-char 11)))))


   (make-strtest :input "\"new \\
line\""
                 :expansion "new line")


   ;; SystemVerilog hex handling

   (make-strtest :input "\"sudden eof \\x" :successp nil)
   (make-strtest :input "\"sudden eof \\x1" :successp nil)
   (make-strtest :input "\"sudden eof \\x12" :successp nil)

   (make-strtest :input "\"ends without hex digit \\x\"" :successp nil)
   (make-strtest :input "\"hex but no digits \\xg\"" :successp nil)

   (make-strtest :input "\"hex test \\x0\""
                 :expansion (cat "hex test "
                                 (implode (list (code-char 0)))))

   (make-strtest :input "\"hex test \\x00\""
                 :expansion (cat "hex test "
                                 (implode (list (code-char 0)))))

   (make-strtest :input "\"hex test \\x10\""
                 :expansion (cat "hex test "
                                 (implode (list (code-char #x10)))))

   (make-strtest :input "\"hex test \\x12\""
                 :expansion (cat "hex test "
                                 (implode (list (code-char #x12)))))

   (make-strtest :input "\"hex test \\xFF\""
                 :expansion (cat "hex test "
                                 (implode (list (code-char #xFF)))))

   (make-strtest :input "\"subsequent stuff \\xFFF\""
                 :expansion (cat "subsequent stuff "
                                 (implode (list (code-char #xFF)))
                                 "F"))

   (make-strtest :input "\"invalid x digits \\xx\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\xX\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\xZ\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\xz\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\x?\"" :successp nil)

   (make-strtest :input "\"invalid x digits \\x0x\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\x1X\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\x2Z\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\x3z\"" :successp nil)
   (make-strtest :input "\"invalid x digits \\x4?\"" :successp nil)

   (make-strtest :input "\"subsequent x \\x65x\""
                 :expansion (cat "subsequent x "
                                 (implode (list (code-char #x65)))
                                 "x"))

   (make-strtest :input "\"subsequent z \\x65z\""
                 :expansion (cat "subsequent z "
                                 (implode (list (code-char #x65)))
                                 "z"))

   (make-strtest :input "\"subsequent ? \\x65?\""
                 :expansion (cat "subsequent ? "
                                 (implode (list (code-char #x65)))
                                 "?"))

   (make-strtest :input "\"invalid x digits \\x0x\"" :successp nil)))

(define make-strtests-fail ((x strtest-list-p))
  (if (atom x)
      nil
    (cons (change-strtest (car x) :successp nil)
          (make-strtests-fail (cdr x)))))

(progn
  (assert!
   (run-strtests *strtests2*
                 (make-vl-loadconfig :edition :system-verilog-2012
                                     :strictp nil)))
  (assert!
   (run-strtests *strtests2*
                 (make-vl-loadconfig :edition :system-verilog-2012
                                     :strictp t)))
  (assert!
   (run-strtests (make-strtests-fail *strtests2*)
                 (make-vl-loadconfig :edition :verilog-2005
                                     :strictp nil)))
  (assert!
   (run-strtests (make-strtests-fail *strtests2*)
                 (make-vl-loadconfig :edition :verilog-2005
                                     :strictp t))))



(defaggregate itest
  :tag :itest
  ((input      stringp)
   (successp   booleanp :default t)
   (remainder  stringp :default "")
   (width      maybe-posp :default nil)
   (signedp    booleanp :default nil)
   (value      maybe-natp :default nil)
   (bits       stringp :default "") ;; msb bits like "1101XXZ"
   (wasunsized booleanp :default nil)
   (nwarnings  natp :default 0)))

(deflist itest-list-p (x)
  (itest-p x))

(define itest-okp ((test itest-p)
                   (config vl-loadconfig-p))
  (b* (((itest test) test)
       (echars (vl-echarlist-from-str test.input))
       (breakp nil)
       (?st    (vl-lexstate-init config))
       ((mv tok remainder warnings) (vl-lex-integer echars breakp nil))
       (- (cw "input: ~x0~%" test.input))
       (- (cw "tok: ~x0~%" (and tok
                                (vl-inttoken-p tok)
                                (vl-echarlist->string (vl-inttoken->etext tok)))))
       (- (cw "rem: ~x0~%" remainder))
       (- (cw "warnings: ~x0.~%" warnings))
       ((mv lextok lexrem lexwrn) (vl-lex-token echars breakp st nil))
       ((unless test.successp)
        (debuggable-and (not tok)
                        (equal remainder echars)
                        (equal (len warnings) test.nwarnings)
                        (not (cw "lex-integer failed as required~%"))
                        (equal tok lextok)
                        (equal lexrem remainder)
                        (equal lexwrn warnings)
                        (not (cw "lex-token failed as required~%")))))
    (debuggable-and
     (vl-inttoken-p tok)
     (equal (vl-inttoken->width tok) test.width)
     (equal (vl-inttoken->signedp tok) test.signedp)
     (equal (vl-inttoken->value tok) test.value)
     (equal (vl-inttoken->wasunsized tok) test.wasunsized)
     (equal (vl-bitlist->string (vl-inttoken->bits tok)) test.bits)
     (equal (append (vl-token->etext tok) remainder) echars)
     (equal (vl-echarlist->string remainder) test.remainder)
     (equal (len warnings) test.nwarnings)
     (not (cw "lex-integer seems correct~%"))
     (equal lextok tok)
     (equal lexrem remainder)
     (equal lexwrn warnings)
     (not (cw "lex-token seems correct~%")))))

(define run-itest ((test itest-p)
                     (config vl-loadconfig-p))
  (or (itest-okp test config)
      (raise "test failed: ~x0.~%" test)))

(deflist run-itests (x config)
  :guard (and (itest-list-p x)
              (vl-loadconfig-p config))
  (run-itest x config))

(defconst *itests*
  (list
   (make-itest :input "0"
               :successp t
               :width 32
               :signedp t
               :value 0
               :wasunsized t
               :bits "")

   (make-itest :input "123_456 foo"
               :successp t
               :remainder " foo"
               :width 32
               :signedp t
               :value 123456
               :wasunsized t
               :bits "")

   (make-itest :input "123 'sh BEEF"
               :successp t
               :width 123
               :signedp t
               :value #xBEEF
               :wasunsized nil
               :bits "")

   (make-itest :input "'sh BEEF"
               :successp t
               :width 32
               :signedp t
               :value #xBEEF
               :wasunsized t
               :bits "")

   (make-itest :input "16'hBE_EF"
               :successp t
               :width 16
               :signedp nil
               :value #xBEEF
               :wasunsized nil
               :bits "")

   (make-itest :input "15'hBEEF" ;; too large
               :successp t
               :width 15
               :value (mod #xBEEF (expt 2 15))
               :signedp nil
               :bits ""
               :wasunsized nil
               :nwarnings 1)

   (make-itest :input "0'h0" ;; size 0 illegal
               :successp t
               :width 32
               :value 0
               :signedp nil
               :bits ""
               :wasunsized t
               :nwarnings 1)

   (make-itest :input "1'h" ;; no value is illegal
               :successp nil)

   (make-itest :input "1'op" ;; no value is illegal
               :successp nil)

   (make-itest :input "1'o___" ;; no value is illegal
               :successp nil)

   (make-itest :input "2_147_483_647"
               ;; biggest plain number allowed without a warning
               :successp t
               :width 32
               :signedp t
               :value 2147483647
               :wasunsized t
               :bits "")

   (make-itest :input "2_147_483_648"
               ;; smallest plain number that causes a warning
               :successp t
               :width 32
               :signedp t
               :value 2147483648
               :wasunsized t
               :bits ""
               :nwarnings 1)

   (make-itest :input "'sh 8000_0000"
               ;; too large warning
               :successp t
               :width 32
               :signedp t
               :value #x80000000
               :wasunsized t
               :bits ""
               :nwarnings 1)

   (make-itest :input "'sh 8000_8000_0000"
               ;; much too large warning
               :successp t
               :width 32
               :signedp t
               :value #x80000000 ;; gets truncated
               :wasunsized t
               :bits ""
               :nwarnings 1)

   (make-itest :input "0 1 2 3"
               :successp t
               :remainder " 1 2 3"
               :width 32
               :wasunsized t
               :signedp t
               :value 0
               :bits "")

   (make-itest :input "9 'o 1____3____7___"
               :successp t
               :remainder ""
               :width 9
               :signedp nil
               :value #o137
               :wasunsized nil
               :bits "")

   (make-itest :input "4'bx"
               :successp t
               :remainder ""
               :width 4
               :signedp nil
               :value nil
               :wasunsized nil
               :bits "XXXX")

   (make-itest :input "4'bz"
               :successp t
               :remainder ""
               :width 4
               :signedp nil
               :value nil
               :wasunsized nil
               :bits "ZZZZ")

   (make-itest :input "4'dz"
               :successp t
               :remainder ""
               :width 4
               :signedp nil
               :value nil
               :wasunsized nil
               :bits "ZZZZ")

   (make-itest :input "4'b1x"
               :successp t
               :remainder ""
               :width 4
               :signedp nil
               :value nil
               :wasunsized nil
               :bits "001X")

   (make-itest :input "4'bx1"
               :successp t
               :remainder ""
               :width 4
               :signedp nil
               :value nil
               :wasunsized nil
               :bits "XXX1")


   (make-itest :input "'bx"
               :successp t
               :remainder ""
               :width 32
               :signedp nil
               :value nil
               :wasunsized t
               :bits (implode (replicate 32 #\X))
               :nwarnings 1)

   (make-itest :input "'hxxx"
               :successp t
               :remainder ""
               :width 32
               :signedp nil
               :value nil
               :wasunsized t
               :bits (implode (replicate 32 #\X))
               :nwarnings 1)

   (make-itest :input "'bz"
               :successp t
               :remainder ""
               :width 32
               :signedp nil
               :value nil
               :wasunsized t
               :bits (implode (replicate 32 #\Z))
               :nwarnings 1)

   (make-itest :input "'o zzz"
               :successp t
               :remainder ""
               :width 32
               :signedp nil
               :value nil
               :wasunsized t
               :bits (implode (replicate 32 #\Z))
               :nwarnings 1)

   (make-itest :input "'bx1"
               :successp t
               :remainder ""
               :width 32
               :signedp nil
               :value nil
               :wasunsized t
               :bits (implode (append (replicate 31 #\X) (list #\1)))
               :nwarnings 1)

   ;; This seems sort of reasonable, but probably isn't ideal.  Maybe we should
   ;; try to read a hex-value always, and then see if it's range for this radix?
   ;; I guess these are probably always prohibited, with numbers always being
   ;; separated by some other token.

   (make-itest :input "9 'o 138"
               :successp t
               :remainder "8"
               :width 9
               :signedp nil
               :value #o13
               :wasunsized nil
               :bits "")))

(assert!
 (and (run-itests *itests* (make-vl-loadconfig :edition :verilog-2005
                                               :strictp nil))
      (run-itests *itests* (make-vl-loadconfig :edition :verilog-2005
                                               :strictp t))
      (run-itests *itests* (make-vl-loadconfig :edition :system-verilog-2012
                                               :strictp nil))
      (run-itests *itests* (make-vl-loadconfig :edition :system-verilog-2012
                                               :strictp t))))



(defmacro vl-lex-real-testcase (&key input
                                     successp
                                     value
                                     (remainder '"")
                                     (nwarnings '0)
                                     (config '*vl-default-loadconfig*))
  `(assert!
    (b* ((echars             (vl-echarlist-from-str ,input))
         (breakp             nil)
         (?st                (vl-lexstate-init ,config))
         ((mv tok remainder warnings)
          (vl-lex-token echars breakp st nil))
         (-                  (cw "Echars: ~x0~%Tok: ~x1~%Remainder: ~x2~%~%" echars tok remainder)))
        (debuggable-and ,@(if successp
                              `((vl-realtoken-p tok)
                                (equal (append (vl-token->etext tok)
                                               remainder)
                                       echars)
                                (equal (vl-echarlist->string (vl-token->etext tok))
                                       ,value)
                                (equal (vl-echarlist->string remainder) ,remainder)
                                (equal (len warnings) ,nwarnings))
                            '((not tok)
                              (equal remainder echars)))))))

(vl-lex-real-testcase :input "123.456"
                      :successp t
                      :value "123.456")

(vl-lex-real-testcase :input "123.456e78"
                      :successp t
                      :value "123.456e78")

(vl-lex-real-testcase :input "123.456E+78"
                      :successp t
                      :value "123.456E+78")

(vl-lex-real-testcase :input "123.456e-78"
                      :successp t
                      :value "123.456e-78")

(vl-lex-real-testcase :input "0.0"
                      :successp t
                      :value "0.0")

(vl-lex-real-testcase :input "0.0 e 0"
                      :successp t
                      :value "0.0"
                      :remainder " e 0")

(vl-lex-real-testcase :input "0.0+0"
                      :successp t
                      :value "0.0"
                      :remainder "+0")




(defmacro vl-lex-misc-testcase (&key input
                                     successp
                                     value
                                     type
                                     (remainder '"")
                                     (nwarnings '0)
                                     (config '*vl-default-loadconfig*))
  `(assert!
    (b* ((echars             (vl-echarlist-from-str ,input))
         (breakp             nil)
         (?st                (vl-lexstate-init ,config))
         ((mv tok remainder ?warnings)
          (vl-lex-token echars breakp st nil))
         (-                  (cw "Echars: ~x0~%Tok: ~x1~%Remainder: ~x2~%~%" echars tok remainder)))
        (debuggable-and ,@(if successp
                              `((equal (append (vl-token->etext tok)
                                               remainder)
                                       echars)
                                (equal (vl-token->type tok) ,type)
                                (equal (vl-echarlist->string (vl-token->etext tok))
                                       ,value)
                                (equal (vl-echarlist->string remainder) ,remainder)
                                (equal (len warnings) ,nwarnings))
                            '((not tok)
                              (equal remainder echars)))))))

(vl-lex-misc-testcase :input "// foo bar baz
4 5 6"
  :successp t
  :value "// foo bar baz
"
  :type :vl-comment
  :remainder "4 5 6")

(vl-lex-misc-testcase :input "`timescale 1ns/1ps"
  :successp t
  :value "`timescale 1ns/1ps"
  :type :vl-ws
  :remainder "")

(vl-lex-misc-testcase :input "`timescale 1 ns / 10 ps 5 6 7"
  :successp t
  :value "`timescale 1 ns / 10 ps"
  :type :vl-ws
  :remainder " 5 6 7")

(vl-lex-misc-testcase :input "`timescale 1 s /100us
a b c"
  :successp t
  :value "`timescale 1 s /100us"
  :type :vl-ws
  :remainder "
a b c")

(vl-lex-misc-testcase :input "`timescale bogus"
  :successp nil)

(vl-lex-misc-testcase :input "1step"
  :successp t
  :value "1step"
  :type :vl-1step
  :remainder ""
  :config (change-vl-loadconfig *vl-default-loadconfig*
                                :edition :system-verilog-2012))

(vl-lex-misc-testcase :input "1step"
  :successp t
  :value "1"
  :type :vl-inttoken
  :remainder "step"
  :config (change-vl-loadconfig *vl-default-loadconfig*
                                :edition :verilog-2005))
