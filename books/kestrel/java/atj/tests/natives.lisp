; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../implementation" :ttags (:open-input-channel (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for AIJ's natively implemented ACL2 functions.
; For now we only have tests for well-guarded calls of these functions,
; because ATJ does not yet handle (RETURN-LAST 'WITH-GUARD-CHECKING1-RAW ...),
; which arises if we wrap the ill-guarded calls to test
; with (WITH-GUARD-CHECKING :NONE ...);
; thus, in particular, we have no tests for BAD-ATOM<=,
; because all its calls with constructible ACL2 values are ill-guarded.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *characterp-tests*
  '(;; on integer:
    ("CharacterpInt0" (characterp 0))
    ("CharacterpInt1" (characterp 1))
    ("CharacterpInt2" (characterp 2))
    ("CharacterpInt3" (characterp 3))
    ("CharacterpInt4" (characterp -1))
    ("CharacterpInt5" (characterp -2))
    ("CharacterpInt6" (characterp -3))
    ("CharacterpInt7" (characterp 100))
    ("CharacterpInt8" (characterp -8729987598718752783873857302))
    ("CharacterpInt9" (characterp 2521010330117103048402292920))
    ;; on ratio:
    ("CharacterpRat0" (characterp 3/4))
    ("CharacterpRat1" (characterp 1/2))
    ("CharacterpRat2" (characterp -7778/27272))
    ("CharacterpRat3" (characterp 88/3))
    ;; on complex rational:
    ("CharacterpCompRat0" (characterp #c(2 3)))
    ("CharacterpCompRat1" (characterp #c(3/4 -1727382984328200202020202)))
    ("CharacterpCompRat2" (characterp #c(-1/2 7/17)))
    ("CharacterpCompRat3" (characterp #c(0 1)))
    ;; on character:
    ("CharacterpChar0" (characterp #\a))
    ("CharacterpChar1" (characterp #\Space))
    ("CharacterpChar2" (characterp #\Tab))
    ("CharacterpChar3" (characterp #\A))
    ("CharacterpChar4" (characterp #\#))
    ("CharacterpChar5" (characterp #\.))
    ("CharacterpChar6" (characterp #\Rubout))
    ("CharacterpChar7" (characterp #\1))
    ("CharacterpChar8" (characterp #\0))
    ;; on string:
    ("CharacterpStr0" (characterp "abc"))
    ("CharacterpStr1" (characterp ""))
    ("CharacterpStr2" (characterp "XY zr"))
    ("CharacterpStr3" (characterp "123"))
    ("CharacterpStr4" (characterp "0"))
    ("CharacterpStr5" (characterp "\""))
    ;; on symbol:
    ("CharacterpSymb0" (characterp 'abcde))
    ("CharacterpSymb1" (characterp 'list))
    ("CharacterpSymb2" (characterp 'java::jsymbol))
    ("CharacterpSymb3" (characterp '||))
    ("CharacterpSymb4" (characterp '|lowercase|))
    ("CharacterpSymb5" (characterp nil))
    ("CharacterpSymb6" (characterp t))
    ("CharacterpSymb7" (characterp :keyword))
    ;; on CONS pair:
    ("CharacterpCons0" (characterp '(0 . 0)))
    ("CharacterpCons1" (characterp '(nil . 3/4)))
    ("CharacterpCons2" (characterp '("ab" . #\-)))
    ("CharacterpCons3" (characterp '(1 2 3)))
    ("CharacterpCons4" (characterp '(x y z)))
    ("CharacterpCons5" (characterp '(acl2-numberp x)))
    ("CharacterpCons6" (characterp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *stringp-tests*
  '(;; on integer:
    ("StringpInt0" (stringp 0))
    ("StringpInt1" (stringp 1))
    ("StringpInt2" (stringp 2))
    ("StringpInt3" (stringp 3))
    ("StringpInt4" (stringp -1))
    ("StringpInt5" (stringp -2))
    ("StringpInt6" (stringp -3))
    ("StringpInt7" (stringp 100))
    ("StringpInt8" (stringp -8729987598718752783873857302))
    ("StringpInt9" (stringp 2521010330117103048402292920))
    ;; on ratio:
    ("StringpRat0" (stringp 3/4))
    ("StringpRat1" (stringp 1/2))
    ("StringpRat2" (stringp -7778/27272))
    ("StringpRat3" (stringp 88/3))
    ;; on complex rational:
    ("StringpCompRat0" (stringp #c(2 3)))
    ("StringpCompRat1" (stringp #c(3/4 -1727382984328200202020202)))
    ("StringpCompRat2" (stringp #c(-1/2 7/17)))
    ("StringpCompRat3" (stringp #c(0 1)))
    ;; on character:
    ("StringpChar0" (stringp #\a))
    ("StringpChar1" (stringp #\Space))
    ("StringpChar2" (stringp #\Tab))
    ("StringpChar3" (stringp #\A))
    ("StringpChar4" (stringp #\#))
    ("StringpChar5" (stringp #\.))
    ("StringpChar6" (stringp #\Rubout))
    ("StringpChar7" (stringp #\1))
    ("StringpChar8" (stringp #\0))
    ;; on string:
    ("StringpStr0" (stringp "abc"))
    ("StringpStr1" (stringp ""))
    ("StringpStr2" (stringp "XY zr"))
    ("StringpStr3" (stringp "123"))
    ("StringpStr4" (stringp "0"))
    ("StringpStr5" (stringp "\""))
    ;; on symbol:
    ("StringpSymb0" (stringp 'abcde))
    ("StringpSymb1" (stringp 'list))
    ("StringpSymb2" (stringp 'java::jsymbol))
    ("StringpSymb3" (stringp '||))
    ("StringpSymb4" (stringp '|lowercase|))
    ("StringpSymb5" (stringp nil))
    ("StringpSymb6" (stringp t))
    ("StringpSymb7" (stringp :keyword))
    ;; on CONS pair:
    ("StringpCons0" (stringp '(0 . 0)))
    ("StringpCons1" (stringp '(nil . 3/4)))
    ("StringpCons2" (stringp '("ab" . #\-)))
    ("StringpCons3" (stringp '(1 2 3)))
    ("StringpCons4" (stringp '(x y z)))
    ("StringpCons5" (stringp '(acl2-numberp x)))
    ("StringpCons6" (stringp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *symbolp-tests*
  '(;; on integer:
    ("SymbolpInt0" (symbolp 0))
    ("SymbolpInt1" (symbolp 1))
    ("SymbolpInt2" (symbolp 2))
    ("SymbolpInt3" (symbolp 3))
    ("SymbolpInt4" (symbolp -1))
    ("SymbolpInt5" (symbolp -2))
    ("SymbolpInt6" (symbolp -3))
    ("SymbolpInt7" (symbolp 100))
    ("SymbolpInt8" (symbolp -8729987598718752783873857302))
    ("SymbolpInt9" (symbolp 2521010330117103048402292920))
    ;; on ratio:
    ("SymbolpRat0" (symbolp 3/4))
    ("SymbolpRat1" (symbolp 1/2))
    ("SymbolpRat2" (symbolp -7778/27272))
    ("SymbolpRat3" (symbolp 88/3))
    ;; on complex rational:
    ("SymbolpCompRat0" (symbolp #c(2 3)))
    ("SymbolpCompRat1" (symbolp #c(3/4 -1727382984328200202020202)))
    ("SymbolpCompRat2" (symbolp #c(-1/2 7/17)))
    ("SymbolpCompRat3" (symbolp #c(0 1)))
    ;; on character:
    ("SymbolpChar0" (symbolp #\a))
    ("SymbolpChar1" (symbolp #\Space))
    ("SymbolpChar2" (symbolp #\Tab))
    ("SymbolpChar3" (symbolp #\A))
    ("SymbolpChar4" (symbolp #\#))
    ("SymbolpChar5" (symbolp #\.))
    ("SymbolpChar6" (symbolp #\Rubout))
    ("SymbolpChar7" (symbolp #\1))
    ("SymbolpChar8" (symbolp #\0))
    ;; on string:
    ("SymbolpStr0" (symbolp "abc"))
    ("SymbolpStr1" (symbolp ""))
    ("SymbolpStr2" (symbolp "XY zr"))
    ("SymbolpStr3" (symbolp "123"))
    ("SymbolpStr4" (symbolp "0"))
    ("SymbolpStr5" (symbolp "\""))
    ;; on symbol:
    ("SymbolpSymb0" (symbolp 'abcde))
    ("SymbolpSymb1" (symbolp 'list))
    ("SymbolpSymb2" (symbolp 'java::jsymbol))
    ("SymbolpSymb3" (symbolp '||))
    ("SymbolpSymb4" (symbolp '|lowercase|))
    ("SymbolpSymb5" (symbolp nil))
    ("SymbolpSymb6" (symbolp t))
    ("SymbolpSymb7" (symbolp :keyword))
    ;; on CONS pair:
    ("SymbolpCons0" (symbolp '(0 . 0)))
    ("SymbolpCons1" (symbolp '(nil . 3/4)))
    ("SymbolpCons2" (symbolp '("ab" . #\-)))
    ("SymbolpCons3" (symbolp '(1 2 3)))
    ("SymbolpCons4" (symbolp '(x y z)))
    ("SymbolpCons5" (symbolp '(acl2-numberp x)))
    ("SymbolpCons6" (symbolp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *integerp-tests*
  '(;; on integer:
    ("IntegerpInt0" (integerp 0))
    ("IntegerpInt1" (integerp 1))
    ("IntegerpInt2" (integerp 2))
    ("IntegerpInt3" (integerp 3))
    ("IntegerpInt4" (integerp -1))
    ("IntegerpInt5" (integerp -2))
    ("IntegerpInt6" (integerp -3))
    ("IntegerpInt7" (integerp 100))
    ("IntegerpInt8" (integerp -8729987598718752783873857302))
    ("IntegerpInt9" (integerp 2521010330117103048402292920))
    ;; on ratio:
    ("IntegerpRat0" (integerp 3/4))
    ("IntegerpRat1" (integerp 1/2))
    ("IntegerpRat2" (integerp -7778/27272))
    ("IntegerpRat3" (integerp 88/3))
    ;; on complex rational:
    ("IntegerpCompRat0" (integerp #c(2 3)))
    ("IntegerpCompRat1" (integerp #c(3/4 -1727382984328200202020202)))
    ("IntegerpCompRat2" (integerp #c(-1/2 7/17)))
    ("IntegerpCompRat3" (integerp #c(0 1)))
    ;; on character:
    ("IntegerpChar0" (integerp #\a))
    ("IntegerpChar1" (integerp #\Space))
    ("IntegerpChar2" (integerp #\Tab))
    ("IntegerpChar3" (integerp #\A))
    ("IntegerpChar4" (integerp #\#))
    ("IntegerpChar5" (integerp #\.))
    ("IntegerpChar6" (integerp #\Rubout))
    ("IntegerpChar7" (integerp #\1))
    ("IntegerpChar8" (integerp #\0))
    ;; on string:
    ("IntegerpStr0" (integerp "abc"))
    ("IntegerpStr1" (integerp ""))
    ("IntegerpStr2" (integerp "XY zr"))
    ("IntegerpStr3" (integerp "123"))
    ("IntegerpStr4" (integerp "0"))
    ("IntegerpStr5" (integerp "\""))
    ;; on symbol:
    ("IntegerpSymb0" (integerp 'abcde))
    ("IntegerpSymb1" (integerp 'list))
    ("IntegerpSymb2" (integerp 'java::jsymbol))
    ("IntegerpSymb3" (integerp '||))
    ("IntegerpSymb4" (integerp '|lowercase|))
    ("IntegerpSymb5" (integerp nil))
    ("IntegerpSymb6" (integerp t))
    ("IntegerpSymb7" (integerp :keyword))
    ;; on CONS pair:
    ("IntegerpCons0" (integerp '(0 . 0)))
    ("IntegerpCons1" (integerp '(nil . 3/4)))
    ("IntegerpCons2" (integerp '("ab" . #\-)))
    ("IntegerpCons3" (integerp '(1 2 3)))
    ("IntegerpCons4" (integerp '(x y z)))
    ("IntegerpCons5" (integerp '(acl2-numberp x)))
    ("IntegerpCons6" (integerp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *rationalp-tests*
  '(;; on integer:
    ("RationalpInt0" (rationalp 0))
    ("RationalpInt1" (rationalp 1))
    ("RationalpInt2" (rationalp 2))
    ("RationalpInt3" (rationalp 3))
    ("RationalpInt4" (rationalp -1))
    ("RationalpInt5" (rationalp -2))
    ("RationalpInt6" (rationalp -3))
    ("RationalpInt7" (rationalp 100))
    ("RationalpInt8" (rationalp -8729987598718752783873857302))
    ("RationalpInt9" (rationalp 2521010330117103048402292920))
    ;; on ratio:
    ("RationalpRat0" (rationalp 3/4))
    ("RationalpRat1" (rationalp 1/2))
    ("RationalpRat2" (rationalp -7778/27272))
    ("RationalpRat3" (rationalp 88/3))
    ;; on complex rational:
    ("RationalpCompRat0" (rationalp #c(2 3)))
    ("RationalpCompRat1" (rationalp #c(3/4 -1727382984328200202020202)))
    ("RationalpCompRat2" (rationalp #c(-1/2 7/17)))
    ("RationalpCompRat3" (rationalp #c(0 1)))
    ;; on character:
    ("RationalpChar0" (rationalp #\a))
    ("RationalpChar1" (rationalp #\Space))
    ("RationalpChar2" (rationalp #\Tab))
    ("RationalpChar3" (rationalp #\A))
    ("RationalpChar4" (rationalp #\#))
    ("RationalpChar5" (rationalp #\.))
    ("RationalpChar6" (rationalp #\Rubout))
    ("RationalpChar7" (rationalp #\1))
    ("RationalpChar8" (rationalp #\0))
    ;; on string:
    ("RationalpStr0" (rationalp "abc"))
    ("RationalpStr1" (rationalp ""))
    ("RationalpStr2" (rationalp "XY zr"))
    ("RationalpStr3" (rationalp "123"))
    ("RationalpStr4" (rationalp "0"))
    ("RationalpStr5" (rationalp "\""))
    ;; on symbol:
    ("RationalpSymb0" (rationalp 'abcde))
    ("RationalpSymb1" (rationalp 'list))
    ("RationalpSymb2" (rationalp 'java::jsymbol))
    ("RationalpSymb3" (rationalp '||))
    ("RationalpSymb4" (rationalp '|lowercase|))
    ("RationalpSymb5" (rationalp nil))
    ("RationalpSymb6" (rationalp t))
    ("RationalpSymb7" (rationalp :keyword))
    ;; on CONS pair:
    ("RationalpCons0" (rationalp '(0 . 0)))
    ("RationalpCons1" (rationalp '(nil . 3/4)))
    ("RationalpCons2" (rationalp '("ab" . #\-)))
    ("RationalpCons3" (rationalp '(1 2 3)))
    ("RationalpCons4" (rationalp '(x y z)))
    ("RationalpCons5" (rationalp '(acl2-numberp x)))
    ("RationalpCons6" (rationalp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *complex-rationalp-tests*
  '(;; on integer:
    ("ComplexRationalpInt0" (complex-rationalp 0))
    ("ComplexRationalpInt1" (complex-rationalp 1))
    ("ComplexRationalpInt2" (complex-rationalp 2))
    ("ComplexRationalpInt3" (complex-rationalp 3))
    ("ComplexRationalpInt4" (complex-rationalp -1))
    ("ComplexRationalpInt5" (complex-rationalp -2))
    ("ComplexRationalpInt6" (complex-rationalp -3))
    ("ComplexRationalpInt7" (complex-rationalp 100))
    ("ComplexRationalpInt8" (complex-rationalp -8729987598718752783873857302))
    ("ComplexRationalpInt9" (complex-rationalp 2521010330117103048402292920))
    ;; on ratio:
    ("ComplexRationalpRat0" (complex-rationalp 3/4))
    ("ComplexRationalpRat1" (complex-rationalp 1/2))
    ("ComplexRationalpRat2" (complex-rationalp -7778/27272))
    ("ComplexRationalpRat3" (complex-rationalp 88/3))
    ;; on complex rational:
    ("ComplexRationalpCompRat0" (complex-rationalp #c(2 3)))
    ("ComplexRationalpCompRat1" (complex-rationalp
                                 #c(3/4 -1727382984328200202020202)))
    ("ComplexRationalpCompRat2" (complex-rationalp #c(-1/2 7/17)))
    ("ComplexRationalpCompRat3" (complex-rationalp #c(0 1)))
    ;; on character:
    ("ComplexRationalpChar0" (complex-rationalp #\a))
    ("ComplexRationalpChar1" (complex-rationalp #\Space))
    ("ComplexRationalpChar2" (complex-rationalp #\Tab))
    ("ComplexRationalpChar3" (complex-rationalp #\A))
    ("ComplexRationalpChar4" (complex-rationalp #\#))
    ("ComplexRationalpChar5" (complex-rationalp #\.))
    ("ComplexRationalpChar6" (complex-rationalp #\Rubout))
    ("ComplexRationalpChar7" (complex-rationalp #\1))
    ("ComplexRationalpChar8" (complex-rationalp #\0))
    ;; on string:
    ("ComplexRationalpStr0" (complex-rationalp "abc"))
    ("ComplexRationalpStr1" (complex-rationalp ""))
    ("ComplexRationalpStr2" (complex-rationalp "XY zr"))
    ("ComplexRationalpStr3" (complex-rationalp "123"))
    ("ComplexRationalpStr4" (complex-rationalp "0"))
    ("ComplexRationalpStr5" (complex-rationalp "\""))
    ;; on symbol:
    ("ComplexRationalpSymb0" (complex-rationalp 'abcde))
    ("ComplexRationalpSymb1" (complex-rationalp 'list))
    ("ComplexRationalpSymb2" (complex-rationalp 'java::jsymbol))
    ("ComplexRationalpSymb3" (complex-rationalp '||))
    ("ComplexRationalpSymb4" (complex-rationalp '|lowercase|))
    ("ComplexRationalpSymb5" (complex-rationalp nil))
    ("ComplexRationalpSymb6" (complex-rationalp t))
    ("ComplexRationalpSymb7" (complex-rationalp :keyword))
    ;; on CONS pair:
    ("ComplexRationalpCons0" (complex-rationalp '(0 . 0)))
    ("ComplexRationalpCons1" (complex-rationalp '(nil . 3/4)))
    ("ComplexRationalpCons2" (complex-rationalp '("ab" . #\-)))
    ("ComplexRationalpCons3" (complex-rationalp '(1 2 3)))
    ("ComplexRationalpCons4" (complex-rationalp '(x y z)))
    ("ComplexRationalpCons5" (complex-rationalp '(acl2-numberp x)))
    ("ComplexRationalpCons6" (complex-rationalp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *acl2-numberp-tests*
  '(;; on integer:
    ("Acl2NumberpInt0" (acl2-numberp 0))
    ("Acl2NumberpInt1" (acl2-numberp 1))
    ("Acl2NumberpInt2" (acl2-numberp 2))
    ("Acl2NumberpInt3" (acl2-numberp 3))
    ("Acl2NumberpInt4" (acl2-numberp -1))
    ("Acl2NumberpInt5" (acl2-numberp -2))
    ("Acl2NumberpInt6" (acl2-numberp -3))
    ("Acl2NumberpInt7" (acl2-numberp 100))
    ("Acl2NumberpInt8" (acl2-numberp -8729987598718752783873857302))
    ("Acl2NumberpInt9" (acl2-numberp 2521010330117103048402292920))
    ;; on ratio:
    ("Acl2NumberpRat0" (acl2-numberp 3/4))
    ("Acl2NumberpRat1" (acl2-numberp 1/2))
    ("Acl2NumberpRat2" (acl2-numberp -7778/27272))
    ("Acl2NumberpRat3" (acl2-numberp 88/3))
    ;; on complex rational:
    ("Acl2NumberpCompRat0" (acl2-numberp #c(2 3)))
    ("Acl2NumberpCompRat1" (acl2-numberp #c(3/4 -1727382984328200202020202)))
    ("Acl2NumberpCompRat2" (acl2-numberp #c(-1/2 7/17)))
    ("Acl2NumberpCompRat3" (acl2-numberp #c(0 1)))
    ;; on character:
    ("Acl2NumberpChar0" (acl2-numberp #\a))
    ("Acl2NumberpChar1" (acl2-numberp #\Space))
    ("Acl2NumberpChar2" (acl2-numberp #\Tab))
    ("Acl2NumberpChar3" (acl2-numberp #\A))
    ("Acl2NumberpChar4" (acl2-numberp #\#))
    ("Acl2NumberpChar5" (acl2-numberp #\.))
    ("Acl2NumberpChar6" (acl2-numberp #\Rubout))
    ("Acl2NumberpChar7" (acl2-numberp #\1))
    ("Acl2NumberpChar8" (acl2-numberp #\0))
    ;; on string:
    ("Acl2NumberpStr0" (acl2-numberp "abc"))
    ("Acl2NumberpStr1" (acl2-numberp ""))
    ("Acl2NumberpStr2" (acl2-numberp "XY zr"))
    ("Acl2NumberpStr3" (acl2-numberp "123"))
    ("Acl2NumberpStr4" (acl2-numberp "0"))
    ("Acl2NumberpStr5" (acl2-numberp "\""))
    ;; on symbol:
    ("Acl2NumberpSymb0" (acl2-numberp 'abcde))
    ("Acl2NumberpSymb1" (acl2-numberp 'list))
    ("Acl2NumberpSymb2" (acl2-numberp 'java::jsymbol))
    ("Acl2NumberpSymb3" (acl2-numberp '||))
    ("Acl2NumberpSymb4" (acl2-numberp '|lowercase|))
    ("Acl2NumberpSymb5" (acl2-numberp nil))
    ("Acl2NumberpSymb6" (acl2-numberp t))
    ("Acl2NumberpSymb7" (acl2-numberp :keyword))
    ;; on CONS pair:
    ("Acl2NumberpCons0" (acl2-numberp '(0 . 0)))
    ("Acl2NumberpCons1" (acl2-numberp '(nil . 3/4)))
    ("Acl2NumberpCons2" (acl2-numberp '("ab" . #\-)))
    ("Acl2NumberpCons3" (acl2-numberp '(1 2 3)))
    ("Acl2NumberpCons4" (acl2-numberp '(x y z)))
    ("Acl2NumberpCons5" (acl2-numberp '(acl2-numberp x)))
    ("Acl2NumberpCons6" (acl2-numberp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *consp-tests*
  '(;; on integer:
    ("ConspInt0" (consp 0))
    ("ConspInt1" (consp 1))
    ("ConspInt2" (consp 2))
    ("ConspInt3" (consp 3))
    ("ConspInt4" (consp -1))
    ("ConspInt5" (consp -2))
    ("ConspInt6" (consp -3))
    ("ConspInt7" (consp 100))
    ("ConspInt8" (consp -8729987598718752783873857302))
    ("ConspInt9" (consp 2521010330117103048402292920))
    ;; on ratio:
    ("ConspRat0" (consp 3/4))
    ("ConspRat1" (consp 1/2))
    ("ConspRat2" (consp -7778/27272))
    ("ConspRat3" (consp 88/3))
    ;; on complex rational:
    ("ConspCompRat0" (consp #c(2 3)))
    ("ConspCompRat1" (consp #c(3/4 -1727382984328200202020202)))
    ("ConspCompRat2" (consp #c(-1/2 7/17)))
    ("ConspCompRat3" (consp #c(0 1)))
    ;; on character:
    ("ConspChar0" (consp #\a))
    ("ConspChar1" (consp #\Space))
    ("ConspChar2" (consp #\Tab))
    ("ConspChar3" (consp #\A))
    ("ConspChar4" (consp #\#))
    ("ConspChar5" (consp #\.))
    ("ConspChar6" (consp #\Rubout))
    ("ConspChar7" (consp #\1))
    ("ConspChar8" (consp #\0))
    ;; on string:
    ("ConspStr0" (consp "abc"))
    ("ConspStr1" (consp ""))
    ("ConspStr2" (consp "XY zr"))
    ("ConspStr3" (consp "123"))
    ("ConspStr4" (consp "0"))
    ("ConspStr5" (consp "\""))
    ;; on symbol:
    ("ConspSymb0" (consp 'abcde))
    ("ConspSymb1" (consp 'list))
    ("ConspSymb2" (consp 'java::jsymbol))
    ("ConspSymb3" (consp '||))
    ("ConspSymb4" (consp '|lowercase|))
    ("ConspSymb5" (consp nil))
    ("ConspSymb6" (consp t))
    ("ConspSymb7" (consp :keyword))
    ;; on CONS pair:
    ("ConspCons0" (consp '(0 . 0)))
    ("ConspCons1" (consp '(nil . 3/4)))
    ("ConspCons2" (consp '("ab" . #\-)))
    ("ConspCons3" (consp '(1 2 3)))
    ("ConspCons4" (consp '(x y z)))
    ("ConspCons5" (consp '(acl2-numberp x)))
    ("ConspCons6" (consp '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-char-code-tests ((code natp))
  (if (and (mbt (natp code))
           (< code 256))
      (cons (list (str::cat "CharCode" (str::natstr code))
                  `(char-code ,(code-char code)))
            (make-char-code-tests (1+ code)))
    nil)
  :measure (nfix (- 256 (nfix code))))

(defconst *char-code-tests*
  ;; test all 256 characters:
  (make-char-code-tests 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-code-char-tests ((code natp))
  (if (and (mbt (natp code))
           (< code 256))
      (cons (list (str::cat "CodeChar" (str::natstr code))
                  `(code-char ,code))
            (make-code-char-tests (1+ code)))
    nil)
  :measure (nfix (- 256 (nfix code))))

(defconst *code-char-tests*
  ;; test all 256 codes:
  (make-code-char-tests 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *coerce-tests*
  '(;; on string:
    ("CoerceString0" (coerce "" 'list))
    ("CoerceString1" (coerce "abc" 'list))
    ("CoerceString2" (coerce "AZ09-." 'list))
    ("CoerceString3" (coerce "Longer String" 'list))
    ;; on list:
    ("CoerceList0" (coerce nil 'string))
    ("CoerceList1" (coerce '(#\x #\y #\z) 'string))
    ("CoerceList2" (coerce '(#\A #\G) 'string))
    ("CoerceList3" (coerce '(#\A #\a #\. #\. #\.) 'string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *intern-in-package-of-symbol-tests*
  '(("InternInPackageOfSymbol0" (intern-in-package-of-symbol "" '||))
    ("InternInPackageOfSymbol1" (intern-in-package-of-symbol "LEN" 'len))
    ("InternInPackageOfSymbol2" (intern-in-package-of-symbol "name" 'symb))
    ("InternInPackageOfSymbol3" (intern-in-package-of-symbol "X" 'cons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *symbol-package-name-tests*
  '(("SymbolPackageName0" (symbol-package-name '||))
    ("SymbolPackageName1" (symbol-package-name 'cons))
    ("SymbolPackageName2" (symbol-package-name 'len))
    ("SymbolPackageName3" (symbol-package-name 'java::atj))
    ("SymbolPackageName4" (symbol-package-name 'acl2::atj))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *symbol-name-tests*
  '(("SymbolName0" (symbol-name '||))
    ("SymbolName1" (symbol-name 'cons))
    ("SymbolName2" (symbol-name 'len))
    ("SymbolName3" (symbol-name 'java::atj))
    ("SymbolName4" (symbol-name 'acl2::atj))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *pkg-imports-tests*
  '(("PkgImports0" (pkg-imports "COMMON-LISP"))
    ("PkgImports1" (pkg-imports "ACL2"))
    ("PkgImports2" (pkg-imports "KEYWORD"))
    ("PkgImports3" (pkg-imports "STD"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *pkg-witness-tests*
  '(("PkgWitness0" (pkg-witness "COMMON-LISP"))
    ("PkgWitness1" (pkg-witness "ACL2"))
    ("PkgWitness2" (pkg-witness "KEYWORD"))
    ("PkgWitness3" (pkg-witness "STD"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *unary---tests*
  '(;; on integer:
    ("UnaryMinusInt0" (unary-- 0))
    ("UnaryMinusInt1" (unary-- 1))
    ("UnaryMinusInt2" (unary-- 10))
    ("UnaryMinusInt3" (unary-- 999))
    ("UnaryMinusInt4" (unary-- -1))
    ("UnaryMinusInt5" (unary-- -2839292020202020200281871772828282))
    ("UnaryMinusInt6" (unary-- -647))
    ;; on ratio:
    ("UnaryMinusRat0" (unary-- 1/2))
    ("UnaryMinusRat1" (unary-- -55/34))
    ("UnaryMinusRat2" (unary-- 83200000/3333322222))
    ("UnaryMinusRat3" (unary-- -37373/123))
    ;; on complex rational:
    ("UnaryMinusCompRat0" (unary-- #c(0 1)))
    ("UnaryMinusCompRat1" (unary-- #c(-2/3 929292)))
    ("UnaryMinusCompRat2" (unary-- #c(100 -3/4)))
    ("UnaryMinusCompRat3" (unary-- #c(2/3 3/2)))
    ("UnaryMinusCompRat4" (unary-- #c(8200000000000000000000 -1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *unary-/-tests*
  '(;; on integer:
    ("UnarySlashInt0" (unary-/ 88))
    ("UnarySlashInt1" (unary-/ 1))
    ("UnarySlashInt2" (unary-/ 10))
    ("UnarySlashInt3" (unary-/ 999))
    ("UnarySlashInt4" (unary-/ -1))
    ("UnarySlashInt5" (unary-/ -2839292020202020200281871772828282))
    ("UnarySlashInt6" (unary-/ -647))
    ;; on ratio:
    ("UnarySlashRat0" (unary-/ 1/2))
    ("UnarySlashRat1" (unary-/ -55/34))
    ("UnarySlashRat2" (unary-/ 83200000/3333322222))
    ("UnarySlashRat3" (unary-/ -37373/123))
    ;; on complex rational:
    ("UnarySlashCompRat0" (unary-/ #c(0 1)))
    ("UnarySlashCompRat1" (unary-/ #c(-2/3 929292)))
    ("UnarySlashCompRat2" (unary-/ #c(100 -3/4)))
    ("UnarySlashCompRat3" (unary-/ #c(2/3 3/2)))
    ("UnarySlashCompRat4" (unary-/ #c(8200000000000000000000 -1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *binary-*-tests*
  '(;; on integer and integer:
    ("BinaryStarIntInt0" (binary-* 0 1))
    ("BinaryStarIntInt1" (binary-* 1 8))
    ("BinaryStarIntInt2" (binary-* 88888 0))
    ("BinaryStarIntInt3" (binary-* 749393 11))
    ("BinaryStarIntInt4" (binary-* -78 78))
    ("BinaryStarIntInt5" (binary-* 900 -1))
    ("BinaryStarIntInt6" (binary-* -1234 852983457283478527845827922002022002))
    ;; on integer and ratio:
    ("BinaryStarIntRat0" (binary-* 5 3/4))
    ("BinaryStarIntRat1" (binary-* 37373 3883/17))
    ("BinaryStarIntRat2" (binary-* 0 8/9999))
    ("BinaryStarIntRat3" (binary-* 1 443/123))
    ("BinaryStarIntRat4" (binary-* -5 3/4))
    ("BinaryStarIntRat5" (binary-* 37373 -3883/17))
    ("BinaryStarIntRat6" (binary-* 0 -8/9999))
    ("BinaryStarIntRat7" (binary-* -1 -443/123))
    ;; on integer and complex rational:
    ("BinaryStarIntCompRat0" (binary-* 23 #c(0 27292)))
    ("BinaryStarIntCompRat1" (binary-* -1 #c(0 733/234)))
    ("BinaryStarIntCompRat2" (binary-* 55 #c(1/2 128000)))
    ("BinaryStarIntCompRat3" (binary-* 0 #c(1/2 65536/3)))
    ("BinaryStarIntCompRat4" (binary-* 18 #c(-10 144/13)))
    ;; on ratio and integer:
    ("BinaryStarRatInt0" (binary-* 3/4 5))
    ("BinaryStarRatInt1" (binary-* 3883/17 37373))
    ("BinaryStarRatInt2" (binary-* 8/9999 0))
    ("BinaryStarRatInt3" (binary-* 443/123 1))
    ("BinaryStarRatInt4" (binary-* 3/4 -5))
    ("BinaryStarRatInt5" (binary-* -3883/17 37373))
    ("BinaryStarRatInt6" (binary-* -8/9999 0))
    ("BinaryStarRatInt7" (binary-* -443/123 -1))
    ;; on ratio and ratio:
    ("BinaryStarRatRat0" (binary-* 73/4 9/23))
    ("BinaryStarRatRat1" (binary-* 7387598328575/4 9/23840875240523))
    ("BinaryStarRatRat2" (binary-* -738/22 8/3))
    ("BinaryStarRatRat3" (binary-* -7338/222222 -1/2))
    ("BinaryStarRatRat4" (binary-* 8/15 -1/2))
    ;; on ratio and complex rational:
    ("BinaryStarRatCompRat0" (binary-* -2/3 #c(99 101)))
    ("BinaryStarRatCompRat1" (binary-* 22/3311 #c(0 -1)))
    ("BinaryStarRatCompRat2" (binary-* 5/12 #c(8383/2 -1234)))
    ("BinaryStarRatCompRat3" (binary-* -1/2 #c(8383/2 555)))
    ;; on complex rational and integer:
    ("BinaryStarCompRatInt0" (binary-* #c(0 27292) 23))
    ("BinaryStarCompRatInt1" (binary-* #c(0 733/234) -1))
    ("BinaryStarCompRatInt2" (binary-* #c(1/2 128000) 55))
    ("BinaryStarCompRatInt3" (binary-* #c(1/2 65536/3) 0))
    ("BinaryStarCompRatInt4" (binary-* #c(-10 144/13) 18))
    ;; on complex rational and ratio:
    ("BinaryStarCompRatRat0" (binary-* #c(99 101) -2/3))
    ("BinaryStarCompRatRat1" (binary-* #c(0 -1) 22/3311))
    ("BinaryStarCompRatRat2" (binary-* #c(8383/2 -1234) 5/12))
    ("BinaryStarCompRatRat3" (binary-* #c(8383/2 555) -1/2))
    ;; on complex rational and complex rational:
    ("BinaryStarCompRatCompRat0" (binary-* #c(0 22) #c(33 0)))
    ("BinaryStarCompRatCompRat1" (binary-* #c(8/3 -22) #c(0 77/2)))
    ("BinaryStarCompRatCompRat2" (binary-* #c(9/100 23) #c(-23 1/2)))
    ("BinaryStarCompRatCompRat3" (binary-* #c(314/100 100/313) #c(-12 -4)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *binary-+-tests*
  '(;; on integer and integer:
    ("BinaryPlusIntInt0" (binary-+ 0 1))
    ("BinaryPlusIntInt1" (binary-+ 1 8))
    ("BinaryPlusIntInt2" (binary-+ 88888 0))
    ("BinaryPlusIntInt3" (binary-+ 749393 11))
    ("BinaryPlusIntInt4" (binary-+ -78 78))
    ("BinaryPlusIntInt5" (binary-+ 900 -1))
    ("BinaryPlusIntInt6" (binary-+ -1234 852983457283478527845827922002022002))
    ;; on integer and ratio:
    ("BinaryPlusIntRat0" (binary-+ 5 3/4))
    ("BinaryPlusIntRat1" (binary-+ 37373 3883/17))
    ("BinaryPlusIntRat2" (binary-+ 0 8/9999))
    ("BinaryPlusIntRat3" (binary-+ 1 443/123))
    ("BinaryPlusIntRat4" (binary-+ -5 3/4))
    ("BinaryPlusIntRat5" (binary-+ 37373 -3883/17))
    ("BinaryPlusIntRat6" (binary-+ 0 -8/9999))
    ("BinaryPlusIntRat7" (binary-+ -1 -443/123))
    ;; on integer and complex rational:
    ("BinaryPlusIntCompRat0" (binary-+ 23 #c(0 27292)))
    ("BinaryPlusIntCompRat1" (binary-+ -1 #c(0 733/234)))
    ("BinaryPlusIntCompRat2" (binary-+ 55 #c(1/2 128000)))
    ("BinaryPlusIntCompRat3" (binary-+ 0 #c(1/2 65536/3)))
    ("BinaryPlusIntCompRat4" (binary-+ 18 #c(-10 144/13)))
    ;; on ratio and integer:
    ("BinaryPlusRatInt0" (binary-+ 3/4 5))
    ("BinaryPlusRatInt1" (binary-+ 3883/17 37373))
    ("BinaryPlusRatInt2" (binary-+ 8/9999 0))
    ("BinaryPlusRatInt3" (binary-+ 443/123 1))
    ("BinaryPlusRatInt4" (binary-+ 3/4 -5))
    ("BinaryPlusRatInt5" (binary-+ -3883/17 37373))
    ("BinaryPlusRatInt6" (binary-+ -8/9999 0))
    ("BinaryPlusRatInt7" (binary-+ -443/123 -1))
    ;; on ratio and ratio:
    ("BinaryPlusRatRat0" (binary-+ 73/4 9/23))
    ("BinaryPlusRatRat1" (binary-+ 7387598328575/4 9/23840875240523))
    ("BinaryPlusRatRat2" (binary-+ -738/22 8/3))
    ("BinaryPlusRatRat3" (binary-+ -7338/222222 -1/2))
    ("BinaryPlusRatRat4" (binary-+ 8/15 -1/2))
    ;; on ratio and complex rational:
    ("BinaryPlusRatCompRat0" (binary-+ -2/3 #c(99 101)))
    ("BinaryPlusRatCompRat1" (binary-+ 22/3311 #c(0 -1)))
    ("BinaryPlusRatCompRat2" (binary-+ 5/12 #c(8383/2 -1234)))
    ("BinaryPlusRatCompRat3" (binary-+ -1/2 #c(8383/2 555)))
    ;; on complex rational and integer:
    ("BinaryPlusCompRatInt0" (binary-+ #c(0 27292) 23))
    ("BinaryPlusCompRatInt1" (binary-+ #c(0 733/234) -1))
    ("BinaryPlusCompRatInt2" (binary-+ #c(1/2 128000) 55))
    ("BinaryPlusCompRatInt3" (binary-+ #c(1/2 65536/3) 0))
    ("BinaryPlusCompRatInt4" (binary-+ #c(-10 144/13) 18))
    ;; on complex rational and ratio:
    ("BinaryPlusCompRatRat0" (binary-+ #c(99 101) -2/3))
    ("BinaryPlusCompRatRat1" (binary-+ #c(0 -1) 22/3311))
    ("BinaryPlusCompRatRat2" (binary-+ #c(8383/2 -1234) 5/12))
    ("BinaryPlusCompRatRat3" (binary-+ #c(8383/2 555) -1/2))
    ;; on complex rational and complex rational:
    ("BinaryPlusCompRatCompRat0" (binary-+ #c(0 22) #c(33 0)))
    ("BinaryPlusCompRatCompRat1" (binary-+ #c(8/3 -22) #c(0 77/2)))
    ("BinaryPlusCompRatCompRat2" (binary-+ #c(9/100 23) #c(-23 1/2)))
    ("BinaryPlusCompRatCompRat3" (binary-+ #c(314/100 100/313) #c(-12 -4)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *<-tests*
  '(;; on integer and integer:
    ("LessThanIntInt0" (< 0 1))
    ("LessThanIntInt1" (< 1 8))
    ("LessThanIntInt2" (< 88888 0))
    ("LessThanIntInt3" (< 749393 11))
    ("LessThanIntInt4" (< -78 78))
    ("LessThanIntInt5" (< 900 -1))
    ("LessThanIntInt6" (< -1234 852983457283478527845827922002022002))
    ;; on integer and ratio:
    ("LessThanIntRat0" (< 5 3/4))
    ("LessThanIntRat1" (< 37373 3883/17))
    ("LessThanIntRat2" (< 0 8/9999))
    ("LessThanIntRat3" (< 1 443/123))
    ("LessThanIntRat4" (< -5 3/4))
    ("LessThanIntRat5" (< 37373 -3883/17))
    ("LessThanIntRat6" (< 0 -8/9999))
    ("LessThanIntRat7" (< -1 -443/123))
    ;; on ratio and integer:
    ("LessThanRatInt0" (< 3/4 5))
    ("LessThanRatInt1" (< 3883/17 37373))
    ("LessThanRatInt2" (< 8/9999 0))
    ("LessThanRatInt3" (< 443/123 1))
    ("LessThanRatInt4" (< 3/4 -5))
    ("LessThanRatInt5" (< -3883/17 37373))
    ("LessThanRatInt6" (< -8/9999 0))
    ("LessThanRatInt7" (< -443/123 -1))
    ;; on ratio and ratio:
    ("LessThanRatRat0" (< 73/4 9/23))
    ("LessThanRatRat1" (< 7387598328575/4 9/23840875240523))
    ("LessThanRatRat2" (< -738/22 8/3))
    ("LessThanRatRat3" (< -7338/222222 -1/2))
    ("LessThanRatRat4" (< 8/15 -1/2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *complex-tests*
  '(;; on integer and integer:
    ("ComplexIntInt0" (complex 0 0))
    ("ComplexIntInt1" (complex 1 2))
    ("ComplexIntInt2" (complex -28282 0))
    ("ComplexIntInt3" (complex 0 116))
    ("ComplexIntInt4" (complex 99 -1001))
    ;; on integer and ratio:
    ("ComplexIntRat0" (complex 0 1/2))
    ("ComplexIntRat1" (complex 889 -262/88880))
    ("ComplexIntRat2" (complex -1 9/13))
    ;; on ratio and integer:
    ("ComplexRatInt0" (complex 1/2 1))
    ("ComplexRatInt1" (complex -262/88880 889))
    ("ComplexRatInt2" (complex 9/13 -1))
    ;; on ratio and ratio:
    ("ComplexRatRat0" (complex 1/2 1/2))
    ("ComplexRatRat1" (complex 2/3 3/4))
    ("ComplexRatRat2" (complex -2/3 -3/4))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *realpart-tests*
  '(;; on integer:
    ("RealPartInt0" (realpart 0))
    ("RealPartInt1" (realpart 1))
    ("RealPartInt2" (realpart 112))
    ("RealPartInt3" (realpart -888))
    ("RealPartInt4" (realpart -1))
    ("RealPartInt5" (realpart 291010292929348100029383465625627181881111111))
    ;; on ratio:
    ("RealPartRat0" (realpart 1/2))
    ("RealPartRat1" (realpart 17171/228282))
    ("RealPartRat2" (realpart -10/7))
    ("RealPartRat3" (realpart 3/4))
    ;; on complex rational:
    ("RealPartCompRat0" (realpart #c(0 1)))
    ("RealPartCompRat1" (realpart #c(0 1001)))
    ("RealPartCompRat2" (realpart #c(0 -992928282)))
    ("RealPartCompRat3" (realpart #c(0 1/22882)))
    ("RealPartCompRat4" (realpart #c(0 -22222/3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *imagpart-tests*
  '(;; on integer:
    ("ImagPartInt0" (imagpart 0))
    ("ImagPartInt1" (imagpart 1))
    ("ImagPartInt2" (imagpart 112))
    ("ImagPartInt3" (imagpart -888))
    ("ImagPartInt4" (imagpart -1))
    ("ImagPartInt5" (imagpart 291010292929348100029383465625627181881111111))
    ;; on ratio:
    ("ImagPartRat0" (imagpart 1/2))
    ("ImagPartRat1" (imagpart 17171/228282))
    ("ImagPartRat2" (imagpart -10/7))
    ("ImagPartRat3" (imagpart 3/4))
    ;; on complex rational:
    ("ImagPartCompRat0" (imagpart #c(0 1)))
    ("ImagPartCompRat1" (imagpart #c(0 1001)))
    ("ImagPartCompRat2" (imagpart #c(0 -992928282)))
    ("ImagPartCompRat3" (imagpart #c(0 1/22882)))
    ("ImagPartCompRat4" (imagpart #c(0 -22222/3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *numerator-tests*
  '(;; on integer:
    ("NumeratorInt0" (numerator 0))
    ("NumeratorInt1" (numerator 1))
    ("NumeratorInt2" (numerator 112))
    ("NumeratorInt3" (numerator -888))
    ("NumeratorInt4" (numerator -1))
    ("NumeratorInt5" (numerator 291010292929348100029383465625627181881111111))
    ;; on ratio:
    ("NumeratorRat0" (numerator 1/2))
    ("NumeratorRat1" (numerator 17171/228282))
    ("NumeratorRat2" (numerator -10/7))
    ("NumeratorRat3" (numerator 3/4))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *denominator-tests*
  '(;; on integer:
    ("DenominatorInt0" (denominator 0))
    ("DenominatorInt1" (denominator 1))
    ("DenominatorInt2" (denominator 112))
    ("DenominatorInt3" (denominator -888))
    ("DenominatorInt4" (denominator -1))
    ("DenominatorInt5" (denominator 2910102929293481000293834681881111111))
    ;; on ratio:
    ("DenominatorRat0" (denominator 1/2))
    ("DenominatorRat1" (denominator 17171/228282))
    ("DenominatorRat2" (denominator -10/7))
    ("DenominatorRat3" (denominator 3/4))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *cons-tests*
  '(("Cons0" (cons 0 0))
    ("Cons1" (cons nil 3/4))
    ("Cons2" (cons "ab" #\-))
    ("Cons3" (cons 1 '(2 3)))
    ("Cons4" (cons 'x '(y z)))
    ("Cons5" (cons 'acl2-numberp 'x))
    ("Cons6" (cons 1 '(2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *car-tests-tests*
  '(("Car0" (car '(0 . 0)))
    ("Car1" (car '(nil . 3/4)))
    ("Car2" (car '("ab" . #\-)))
    ("Car3" (car '(1 2 3)))
    ("Car4" (car '(x y z)))
    ("Car5" (car '(acl2-numberp x)))
    ("Car6" (car '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *cdr-tests-tests*
  '(("Cdr0" (cdr '(0 . 0)))
    ("Cdr1" (cdr '(nil . 3/4)))
    ("Cdr2" (cdr '("ab" . #\-)))
    ("Cdr3" (cdr '(1 2 3)))
    ("Cdr4" (cdr '(x y z)))
    ("Cdr5" (cdr '(acl2-numberp x)))
    ("Cdr6" (cdr '(1 2 3 . "abc")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *equal-tests*
  '(("Equal0" (equal t nil))
    ("Equal1" (equal t "T"))
    ("Equal2" (equal 15 45/3))
    ("Equal3" (equal #\c #\c))
    ("Equal4" (equal '(1 2 3) '(1 . (2 3))))
    ("Equal5" (equal :kwd :diff))
    ("Equal6" (equal :same :same))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *if-tests*
  '(("If0" (if t 1 2))
    ("If1" (if nil 1 2))
    ("If2" (if #\c "abcde" '(1 2 3)))
    ("If3" (if :key :one :other))
    ("If4" (if nil :no :yes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *nonnegative-integer-quotient-tests*
  '(("NonnegIntQuot0" (nonnegative-integer-quotient 0 889))
    ("NonnegIntQuot1" (nonnegative-integer-quotient 3 7))
    ("NonnegIntQuot2" (nonnegative-integer-quotient 363202 783))
    ("NonnegIntQuot3" (nonnegative-integer-quotient 528 22))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *string-append-tests*
  '(("StringAppend0" (string-append "" ""))
    ("StringAppend1" (string-append "abc" ""))
    ("StringAppend2" (string-append "" "xyz"))
    ("StringAppend3" (string-append "string" "append"))
    ("StringAppend4" (string-append "SJSKDN83KD" "KSKSOWOWOZZNCM8D88383"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *len-tests*
  '(("Len0" (len nil))
    ("Len1" (len '(a)))
    ("Len2" (len '(a b)))
    ("Len3" (len '(a b c)))
    ("Len4" (len '(a b c d)))
    ("Len5" (len '(a b c d e f g h i j k l m n o p q r s t u v w x y z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *all-tests*
  (append *characterp-tests*
          *stringp-tests*
          *symbolp-tests*
          *integerp-tests*
          *rationalp-tests*
          *complex-rationalp-tests*
          *acl2-numberp-tests*
          *consp-tests*
          *unary---tests*
          *unary-/-tests*
          *binary-*-tests*
          *binary-+-tests*
          *char-code-tests*
          *code-char-tests*
          *coerce-tests*
          *intern-in-package-of-symbol-tests*
          *symbol-package-name-tests*
          *symbol-name-tests*
          *pkg-imports-tests*
          *pkg-witness-tests*
          *<-tests*
          *complex-tests*
          *realpart-tests*
          *imagpart-tests*
          *numerator-tests*
          *denominator-tests*
          *cons-tests*
          *car-tests-tests*
          *cdr-tests-tests*
          *equal-tests*
          *if-tests*
          *nonnegative-integer-quotient-tests*
          *string-append-tests*
          *len-tests*))
