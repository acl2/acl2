; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "lexer")
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
        (config '*vl-default-lexconfig*) ;; Configuration to use
        (nwarnings '0))
  `(assert!
    (b* ((echars (vl-echarlist-from-str ,input))
         (st     (vl-lexstate-init ,config))
         ((mv tok remainder warnings) (vl-lex-token echars st nil))
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
            ("'{"   . :vl-assignpat))))

(defun make-punctuation-tests (alist config)
  (if (consp alist)
      (list*
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
       ;; How about for "OP1"?
       `(vl-lex-op-testcase :input ,(cat (caar alist) "1")
                            :config ',config
                            :successp t
                            :remainder "1"
                            :type ,(cdar alist))
       (make-punctuation-tests (cdr alist) config))
    nil))



(make-event
 `(progn
    (value-triple (cw "Checking operator handling for Verilog-2005.~%"))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-lexconfig :edition :verilog-2005
                                                 :strictp nil))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-lexconfig :edition :verilog-2005
                                                 :strictp t))
    (value-triple (cw "Checking old operator handling for SystemVerilog-2012.~%"))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-lexconfig :edition :system-verilog-2012
                                                 :strictp nil))
    ,@(make-punctuation-tests *verilog-2005-punctuation-alist*
                              (make-vl-lexconfig :edition :system-verilog-2012
                                                 :strictp t))
    (value-triple (cw "Checking new operator handling for SystemVerilog-2012.~%"))
    ,@(make-punctuation-tests *verilog-2012-punctuation-alist*
                              (make-vl-lexconfig :edition :system-verilog-2012
                                                 :strictp nil))
    ,@(make-punctuation-tests *verilog-2012-punctuation-alist*
                              (make-vl-lexconfig :edition :system-verilog-2012
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
                               (make-vl-lexconfig :edition :verilog-2005
                                                  :strictp t))
         ,@(make-keyword-tests *vl-2005-keyword-table*
                               (make-vl-lexconfig :edition :verilog-2005
                                                  :strictp nil))
         ,@(make-keyword-tests *vl-2012-keyword-table-strict*
                               (make-vl-lexconfig :edition :system-verilog-2012
                                                  :strictp t))
         ,@(make-keyword-tests *vl-2012-keyword-table*
                               (make-vl-lexconfig :edition :system-verilog-2012
                                                  :strictp nil))
         ))



(defmacro vl-lex-string-testcase (&key input
                                       successp
                                       (remainder '"")
                                       expansion
                                       (nwarnings '0)
                                       (config '*vl-default-lexconfig*))
  `(assert!
    (b* ((echars    (vl-echarlist-from-str ,input))
         (?st        (vl-lexstate-init ,config))
         ((mv tok remainder)
          (vl-lex-string echars))
         (- (cw "Echars: ~x0~%Tok: ~x1~%Remainder: ~x2~%~%"
                echars tok remainder)))
        (debuggable-and ,@(if successp
                              `((vl-stringtoken-p tok)
                                (equal (vl-stringtoken->expansion tok) ,expansion)
                                (equal (append (vl-token->etext tok)
                                               remainder)
                                       echars)
                                (equal (vl-echarlist->string remainder) ,remainder)
                                (mv-let (lextok lexrem warnings)
                                        (vl-lex-token echars st nil)
                                        (debuggable-and (equal tok lextok)
                                                        (equal remainder lexrem)
                                                        (equal (len warnings) ,nwarnings)
                                                        )))
                            `((not tok)
                              (equal remainder echars)))))))

;; Should succeed string tests

(vl-lex-string-testcase :input "\"Hello\""
                        :successp t
                        :expansion "Hello")

(vl-lex-string-testcase :input "\"Hello\" world"
                        :successp t
                        :remainder " world"
                        :expansion "Hello")

(vl-lex-string-testcase :input "\"\\103allista\""
                        :successp t
                        :expansion "Callista")

(vl-lex-string-testcase :input "\"my \\44.02\""
                        :successp t
                        :expansion "my $.02")

(vl-lex-string-testcase :input "\"crazy \\7\""
                        :successp t
                        :expansion (cat "crazy "
                                        (implode (list (code-char 7)))))

(vl-lex-string-testcase :input "\"\\\\ another \\n basic \\t escape \\\" test\""
                        :successp t
                        :expansion (cat "\\ another "
                                        (implode (list #\Newline))
                                        " basic "
                                        (implode (list #\Tab))
                                        " escape \" test"))

;; Should fail string tests

(vl-lex-string-testcase :input "\"not terminated"
                        :successp nil)

(vl-lex-string-testcase :input "\"invalid escape sequence \\f is no good\""
                        :successp nil)

(vl-lex-string-testcase :input "\"out of range \\400 octal sequence\""
                        :successp nil)

(vl-lex-string-testcase :input "\"not closed before
                                 newline\""
                        :successp nil)






(defmacro vl-lex-integer-testcase (&key input
                                        successp
                                        (remainder '"")
                                        width
                                        signedp
                                        value
                                        bits
                                        wasunsized
                                        (nwarnings '0)
                                        (config '*vl-default-lexconfig*))
  `(assert!
    (b* ((echars (vl-echarlist-from-str ,input))
         (?st (vl-lexstate-init ,config))
         ((mv tok remainder warnings)
          (vl-lex-integer echars nil))
         (- (cw "lex-integer: tok is ~x0~%rem is ~x1~%warnings is ~x2~%"
                tok remainder warnings)))
        (debuggable-and ,@(if successp
                              `((vl-inttoken-p tok)
                                (equal (vl-inttoken->width tok) ,width)
                                (equal (vl-inttoken->signedp tok) ,signedp)
                                (equal (vl-inttoken->value tok) ,value)
                                (equal (vl-inttoken->wasunsized tok) ,wasunsized)
                                (equal (vl-bitlist->string (vl-inttoken->bits tok))
                                       ,bits)
                                (equal (append (vl-token->etext tok)
                                               remainder)
                                       echars)
                                (equal (vl-echarlist->string remainder) ,remainder)
                                (equal (len warnings) ,nwarnings)
                                (mv-let (lextok lexrem lexwrn)
                                        (vl-lex-token echars st nil)
                                        (debuggable-and
                                         (equal lextok tok)
                                         (equal lexrem remainder)
                                         (equal (len lexwrn) ,nwarnings))))
                            `((not tok)
                              (equal remainder echars)
                              (equal (len warnings) ,nwarnings)
                              ))))))

(vl-lex-integer-testcase :input "0"
                         :successp t
                         :width 32
                         :signedp t
                         :value 0
                         :wasunsized t
                         :bits "")

(vl-lex-integer-testcase :input "123_456 foo"
                         :successp t
                         :remainder " foo"
                         :width 32
                         :signedp t
                         :value 123456
                         :wasunsized t
                         :bits "")

(vl-lex-integer-testcase :input "123 'sh BEEF"
                         :successp t
                         :width 123
                         :signedp t
                         :value #xBEEF
                         :wasunsized nil
                         :bits "")

(vl-lex-integer-testcase :input "'sh BEEF"
                         :successp t
                         :width 32
                         :signedp t
                         :value #xBEEF
                         :wasunsized t
                         :bits "")

(vl-lex-integer-testcase :input "16'hBE_EF"
                         :successp t
                         :width 16
                         :signedp nil
                         :value #xBEEF
                         :wasunsized nil
                         :bits "")

(vl-lex-integer-testcase :input "15'hBEEF"   ;; too large
                         :successp t
                         :width 15
                         :value (mod #xBEEF (expt 2 15))
                         :signedp nil
                         :bits ""
                         :wasunsized nil
                         :nwarnings 1)

(vl-lex-integer-testcase :input "0'h0"  ;; size 0 illegal
                         :successp nil
                         )

(vl-lex-integer-testcase :input "1'h"  ;; no value is illegal
                         :successp nil
                         )

(vl-lex-integer-testcase :input "1'op"  ;; no value is illegal
                         :successp nil
                         )

(vl-lex-integer-testcase :input "1'o___"  ;; no value is illegal
                         :successp nil
                         )

(vl-lex-integer-testcase :input "2_147_483_647" ;; biggest plain number allowed without a warning
                         :successp t
                         :width 32
                         :signedp t
                         :value 2147483647
                         :wasunsized t
                         :bits "")

(vl-lex-integer-testcase :input "2_147_483_648" ;; smallest plain number that causes a warning
                         :successp t
                         :width 32
                         :signedp t
                         :value 2147483648
                         :wasunsized t
                         :bits ""
                         :nwarnings 1
                         )

(vl-lex-integer-testcase :input "'sh 8000_0000"  ;; too large warning
                         :successp t
                         :width 32
                         :signedp t
                         :value #x80000000
                         :wasunsized t
                         :bits ""
                         :nwarnings 1)

(vl-lex-integer-testcase :input "'sh 8000_8000_0000"  ;; much too large warning
                         :successp t
                         :width 32
                         :signedp t
                         :value #x80000000 ;; gets truncated
                         :wasunsized t
                         :bits ""
                         :nwarnings 1)

(vl-lex-integer-testcase :input "0 1 2 3"
                         :successp t
                         :remainder " 1 2 3"
                         :width 32
                         :wasunsized t
                         :signedp t
                         :value 0
                         :bits "")

(vl-lex-integer-testcase :input "9 'o 1____3____7___"
                         :successp t
                         :remainder ""
                         :width 9
                         :signedp nil
                         :value #o137
                         :wasunsized nil
                         :bits "")

(vl-lex-integer-testcase :input "4'bx"
                         :successp t
                         :remainder ""
                         :width 4
                         :signedp nil
                         :value nil
                         :wasunsized nil
                         :bits "XXXX")

(vl-lex-integer-testcase :input "4'bz"
                         :successp t
                         :remainder ""
                         :width 4
                         :signedp nil
                         :value nil
                         :wasunsized nil
                         :bits "ZZZZ")

(vl-lex-integer-testcase :input "4'dz"
                         :successp t
                         :remainder ""
                         :width 4
                         :signedp nil
                         :value nil
                         :wasunsized nil
                         :bits "ZZZZ")

(vl-lex-integer-testcase :input "4'b1x"
                         :successp t
                         :remainder ""
                         :width 4
                         :signedp nil
                         :value nil
                         :wasunsized nil
                         :bits "001X")

(vl-lex-integer-testcase :input "4'bx1"
                         :successp t
                         :remainder ""
                         :width 4
                         :signedp nil
                         :value nil
                         :wasunsized nil
                         :bits "XXX1")


(vl-lex-integer-testcase :input "'bx"
                         :successp t
                         :remainder ""
                         :width 32
                         :signedp nil
                         :value nil
                         :wasunsized t
                         :bits (implode (repeat #\X 32))
                         :nwarnings 1)

(vl-lex-integer-testcase :input "'hxxx"
                         :successp t
                         :remainder ""
                         :width 32
                         :signedp nil
                         :value nil
                         :wasunsized t
                         :bits (implode (repeat #\X 32))
                         :nwarnings 1)

(vl-lex-integer-testcase :input "'bz"
                         :successp t
                         :remainder ""
                         :width 32
                         :signedp nil
                         :value nil
                         :wasunsized t
                         :bits (implode (repeat #\Z 32))
                         :nwarnings 1)

(vl-lex-integer-testcase :input "'o zzz"
                         :successp t
                         :remainder ""
                         :width 32
                         :signedp nil
                         :value nil
                         :wasunsized t
                         :bits (implode (repeat #\Z 32))
                         :nwarnings 1)

(vl-lex-integer-testcase :input "'bx1"
                         :successp t
                         :remainder ""
                         :width 32
                         :signedp nil
                         :value nil
                         :wasunsized t
                         :bits (implode (append (repeat #\X 31) (list #\1)))
                         :nwarnings 1)



;; This seems sort of reasonable, but probably isn't ideal.  Maybe we should
;; try to read a hex-value always, and then see if it's range for this radix?
;; I guess these are probably always prohibited, with numbers always being
;; separated by some other token.

(vl-lex-integer-testcase :input "9 'o 138"
                         :successp t
                         :remainder "8"
                         :width 9
                         :signedp nil
                         :value #o13
                         :wasunsized nil
                         :bits "")




(defmacro vl-lex-real-testcase (&key input
                                     successp
                                     value
                                     (remainder '"")
                                     (nwarnings '0)
                                     (config '*vl-default-lexconfig*))
  `(assert!
    (b* ((echars             (vl-echarlist-from-str ,input))
         (?st                (vl-lexstate-init ,config))
         ((mv tok remainder warnings)
          (vl-lex-token echars st nil))
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


