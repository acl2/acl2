; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(local (include-book "../util/arithmetic"))

(program)


;; This will get run any time the book is included.
(make-event (prog2$ (cw "lexer-tests.lisp is being included.  You ~
                         almost certainly do not want to do this.~%")
                    (value '(value-triple :invisible)))
            :check-expansion t)


(defmacro vl-lex-op-testcase (&key input
                                   successp
                                   (remainder '"")
                                   type
                                   (nwarnings '0))
  `(assert!
    (b* ((echars             (vl-echarlist-from-str ,input))
         ((mv tok remainder warnings)
          (vl-lex-token echars nil))
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


(defconst *punctuation-alist*
  (list (cons "[" :vl-lbrack)
        (cons "]" :vl-rbrack)
        (cons "(" :vl-lparen)
        (cons ")" :vl-rparen)
        (cons "{" :vl-lcurly)
        (cons "}" :vl-rcurly)
        (cons ":" :vl-colon)
        (cons "+:" :vl-pluscolon)
        (cons "-:" :vl-minuscolon)
        (cons ";" :vl-semi)
        (cons "#" :vl-pound)
        (cons "," :vl-comma)
        (cons "." :vl-dot)
        (cons "@" :vl-atsign)
        (cons "(*" :vl-beginattr)
        (cons "*)" :vl-endattr)
        (cons "=" :vl-equalsign)
        (cons "+" :vl-plus)
        (cons "-" :vl-minus)
        (cons "*" :vl-times)
        (cons "/" :vl-div)
        (cons "%" :vl-rem)
        (cons "**" :vl-power)
        (cons "^" :vl-xor)
        (cons "?" :vl-qmark)
        (cons "<" :vl-lt)
        (cons "<=" :vl-lte)
        (cons "<<" :vl-shl)
        (cons "<<<" :vl-ashl)
        (cons ">" :vl-gt)
        (cons ">=" :vl-gte)
        (cons ">>" :vl-shr)
        (cons ">>>" :vl-ashr)
        (cons "!==" :vl-cne)
        (cons "!=" :vl-neq)
        (cons "!" :vl-lognot)
        (cons "~&" :vl-nand)
        (cons "~|" :vl-nor)
        (cons "~^" :vl-xnor)
        (cons "^~" :vl-xnor)
        (cons "~" :vl-bitnot)
        (cons "||" :vl-logor)
        (cons "|" :vl-bitor)
        (cons "&&" :vl-logand)
        (cons "&" :vl-bitand)
        (cons "===" :vl-ceq)
        (cons "==" :vl-eq)
        (cons "&&&" :vl-andandand)))

(defun make-punctuation-tests (alist)
  (if (consp alist)
      (list* `(vl-lex-op-testcase :input ,(caar alist)
                                 :successp t
                                 :type ,(cdar alist))
             `(vl-lex-op-testcase :input ,(cat (caar alist) " foo")
                                  :successp t
                                  :remainder " foo"
                                  :type ,(cdar alist))
             `(vl-lex-op-testcase :input ,(cat (caar alist) "1")
                                  :successp t
                                  :remainder "1"
                                  :type ,(cdar alist))
            (make-punctuation-tests (cdr alist)))
    nil))

(make-event `(progn ,@(make-punctuation-tests *punctuation-alist*)))


(defun make-keyword-tests (alist)
  (if (consp alist)
      (list* `(vl-lex-op-testcase :input ,(caar alist)
                                 :successp t
                                 :type ,(cdar alist))
             `(vl-lex-op-testcase :input ,(cat (caar alist) " foo")
                                  :successp t
                                  :remainder " foo"
                                  :type ,(cdar alist))
             (make-keyword-tests (cdr alist)))
    nil))

(make-event `(progn ,@(make-keyword-tests *vl-keyword-table*)))






(defmacro vl-lex-string-testcase (&key input
                                       successp
                                       (remainder '"")
                                       expansion
                                       (nwarnings '0))
  `(assert!
    (b* ((echars             (vl-echarlist-from-str ,input))
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
                                        (vl-lex-token echars nil)
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
                                        (nwarnings '0))
  `(assert!
    (b* ((echars (vl-echarlist-from-str ,input))
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
                                        (vl-lex-token echars nil)
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
                                     (nwarnings '0))
  `(assert!
    (b* ((echars             (vl-echarlist-from-str ,input))
         ((mv tok remainder warnings)
          (vl-lex-token echars nil))
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


