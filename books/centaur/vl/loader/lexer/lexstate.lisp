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
(include-book "../config")
(include-book "tokens")

(defsection lexstate
  :parents (lexer)
  :short "Low level, internal configuration for the lexer, which allows us to
switch between supported Verilog editions."

  :long "<p>You should typically never create a lexstate directly.  Instead,
see @(see vl-lexstate-init), which creates an appropriate lexstate for a
particular, high-level @(see vl-loadconfig-p).</p>")

(define vl-plaintoken-alistp (x)
  :parents (lexstate)
  :short "Recognize alists binding strings to plaintoken types."
  :long "<p>We use these for configurable operator handling, based on the
particular standard we're implementing.</p>"
  (if (atom x)
      t
    (and (consp (car x))
         (stringp (caar x))
         (not (equal (caar x) ""))
         (vl-plaintokentype-p (cdar x))
         (vl-plaintoken-alistp (cdr x))))
  ///
  (defthm vl-plaintoken-alistp-when-atom
    (implies (atom x)
             (equal (vl-plaintoken-alistp x)
                    t)))
  (defthm vl-plaintoken-alistp-of-cons
    (equal (vl-plaintoken-alistp (cons a x))
           (and (consp a)
                (stringp (car a))
                (not (equal (car a) ""))
                (vl-plaintokentype-p (cdr a))
                (vl-plaintoken-alistp x))))
  (defthm vl-plaintoken-alistp-of-append
    (equal (vl-plaintoken-alistp (append x y))
           (and (vl-plaintoken-alistp x)
                (vl-plaintoken-alistp y))))
  (defthm vl-plaintokentype-p-of-hons-assoc-equal-when-vl-plaintoken-alistp
    (implies (vl-plaintoken-alistp x)
             (equal (vl-plaintokentype-p (cdr (hons-assoc-equal key x)))
                    (if (hons-assoc-equal key x)
                        t
                      nil)))))

(defaggregate vl-lexstate
  :parents (lexstate)
  :short "Internal representation of the lexer's configuration."
  :layout :fulltree
  :tag nil

  ((kwdtable vl-keyword-table-p
             "The set of @(see lex-keywords) that are currently supported; this
              could be, e.g., the Verilog 2005 keywords or the SystemVerilog
              2012 keywords, and might or might not include VL extensions.")

   (bangops   vl-plaintoken-alistp "Operators starting with @('!').")
   (poundops  vl-plaintoken-alistp "Operators starting with @('#').")
   (remops    vl-plaintoken-alistp "Operators starting with @('%').")
   (andops    vl-plaintoken-alistp "Operators starting with @('&').")
   (starops   vl-plaintoken-alistp "Operators starting with @('*').")
   (plusops   vl-plaintoken-alistp "Operators starting with @('+').")
   (dashops   vl-plaintoken-alistp "Operators starting with @('-').")
   (dotops    vl-plaintoken-alistp "Operators starting with @('.').")
   (divops    vl-plaintoken-alistp "Operators starting with @('/').")
   (colonops  vl-plaintoken-alistp "Operators starting with @(':').")
   (lessops   vl-plaintoken-alistp "Operators starting with @('<').")
   (gtops     vl-plaintoken-alistp "Operators starting with @('>').")
   (eqops     vl-plaintoken-alistp "Operators starting with @('=').")
   (xorops    vl-plaintoken-alistp "Operators starting with @('^').")
   (barops    vl-plaintoken-alistp "Operators starting with @('|').")

   (dollarops vl-plaintoken-alistp "Special tokens starting with @('$').")

   (quotesp    booleanp "Enable SystemVerilog 2012 ' tokens?")
   (strextsp   booleanp "Enable SystemVerilog 2012 string literal extensions?")
   (timelitsp  booleanp "Enable SystemVerilog 2012 time literals?")
   (extintsp   booleanp "Enable SystemVerilog 2012 '0/'1/'x/'z integers?")
   (onestepp   booleanp "Enable SystemVerilog 2012 '1step' tokens?")
   ))


(define vl-lexstate->plainalist
  :parents (lexstate)
  :short "Just used for sanity checking."
  ((x vl-lexstate-p))
  :returns (al vl-plaintoken-alistp :hyp :fguard)
  (b* (((vl-lexstate x) x))
    (append-without-guard
     x.bangops x.poundops x.remops x.andops x.starops
     x.plusops x.dashops x.dotops x.divops x.colonops
     x.lessops x.gtops x.eqops x.xorops x.barops
     x.dollarops))
  :prepwork ((local (in-theory (disable (:t acl2::true-listp-append)
                                        (:t binary-append))))))


(defval *vl-2005-strict-lexstate*
  :parents (lexstate)
  :short "Configuration for strict Verilog-2005 mode."
  (make-vl-lexstate
   :kwdtable *vl-2005-keyword-table-strict*
   :bangops  '(("!==" . :vl-cne)        ;; Longest tokens first in each alist!
               ("!="  . :vl-neq)
               ("!"   . :vl-lognot))
   :poundops '(("#"   . :vl-pound))
   :remops   '(("%"   . :vl-rem))
   :andops   '(("&&&" . :vl-andandand)
               ("&&"  . :vl-logand)
               ("&"   . :vl-bitand))
   :starops  '(("**"  . :vl-power)
               ("*)"  . :vl-endattr)
               ("*"   . :vl-times))
   :plusops  '(("+:"  . :vl-pluscolon)
               ("+"   . :vl-plus))
   :dashops  '(("->"  . :vl-arrow)
               ("-:"  . :vl-minuscolon)
               ("-"   . :vl-minus))
   :dotops   '(("."   . :vl-dot))
   :divops   '(("/"   . :vl-div))
   :colonops '((":"   . :vl-colon))
   :lessops  '(("<<<" . :vl-ashl)
               ("<<"  . :vl-shl)
               ("<="  . :vl-lte)
               ("<"   . :vl-lt))
   :gtops    '((">>>"  . :vl-ashr)
               (">>"   . :vl-shr)
               (">="   . :vl-gte)
               (">"    . :vl-gt))
   :eqops    '(("===" . :vl-ceq)
               ("=="  . :vl-eq)
               ("="   . :vl-equalsign))
   :xorops   '(("^~" . :vl-xnor)
               ("^"  . :vl-xor))
   :barops   '(("||"   . :vl-logor)
               ("|"    . :vl-bitor))
   :dollarops  nil
   :quotesp    nil
   :strextsp   nil
   :timelitsp  nil
   :extintsp   nil
   :onestepp   nil
   )
  ///
  (assert!
   ;; Basic sanity check, everything should be unique and valid.
   (let ((al (vl-lexstate->plainalist *vl-2005-strict-lexstate*)))
     (and (subsetp-equal (alist-vals al) *vl-2005-plain-nonkeywords*)
          (uniquep (alist-keys al))
          (uniquep (alist-vals al)))))
  (assert!
   (not (vl-lexstate->quotesp *vl-2005-strict-lexstate*))))

(defval *vl-2005-lexstate*
  :parents (lexstate)
  :short "Configuration for extended (non-strict) Verilog-2005 mode."
  (change-vl-lexstate *vl-2005-strict-lexstate*
                      :kwdtable *vl-2005-keyword-table*))

(defval *vl-2012-strict-lexstate*
  :parents (lexstate)
  :short "Configuration for strict SystemVerilog-2012 mode."

  (make-vl-lexstate
   :kwdtable *vl-2012-keyword-table-strict*
   :bangops  '(("!=="  . :vl-cne)         ;; Longest tokens first in each alist!
               ("!=?"  . :vl-wildneq)
               ("!="   . :vl-neq)
               ("!"    . :vl-lognot))
   :poundops '(("#-#"  . :vl-pounddash)
               ("#=#"  . :vl-poundequal)
               ("##"   . :vl-poundpound)
               ("#"    . :vl-pound))
   :remops   '(("%="   . :vl-remeq)
               ("%"    . :vl-rem))
   :andops   '(("&&&"  . :vl-andandand)
               ("&="   . :vl-andeq)
               ("&&"   . :vl-logand)
               ("&"    . :vl-bitand))
   :starops  '(("**"   . :vl-power)
               ("*)"   . :vl-endattr)
               ("*="   . :vl-timeseq)
               ("*>"   . :vl-stararrow)
               ("*"    . :vl-times))
   :plusops  '(("+:"   . :vl-pluscolon)
               ("+="   . :vl-pluseq)
               ("++"   . :vl-plusplus)
               ("+"    . :vl-plus))
   :dashops  '(("->>"  . :vl-arrowgt)
               ("->"   . :vl-arrow)
               ("-="   . :vl-minuseq)
               ("--"   . :vl-minusminus)
               ("-:"   . :vl-minuscolon)
               ("-"    . :vl-minus))
   :dotops   '((".*"   . :vl-dotstar)
               ("."    . :vl-dot))
   :divops   '(("/="   . :vl-diveq)
               ("/"    . :vl-div))
   :colonops '((":="   . :vl-coloneq)
               (":/"   . :vl-colonslash)
               ("::"   . :vl-scope)
               (":"    . :vl-colon))
   :lessops  '(("<<<=" . :vl-ashleq)
               ("<<<"  . :vl-ashl)
               ("<<="  . :vl-shleq)
               ("<->"  . :vl-equiv)
               ("<<"   . :vl-shl)
               ("<="   . :vl-lte)
               ("<"    . :vl-lt))
   :gtops    '((">>>=" . :vl-ashreq)
               (">>>"  . :vl-ashr)
               (">>="  . :vl-shreq)
               (">>"   . :vl-shr)
               (">="   . :vl-gte)
               (">"    . :vl-gt))
   :eqops    '(("==="  . :vl-ceq)
               ("==?"  . :vl-wildeq)
               ("=="   . :vl-eq)
               ("=>"   . :vl-eqarrow)
               ("="    . :vl-equalsign))
   :xorops   '(("^~"   . :vl-xnor)
               ("^="   . :vl-xoreq)
               ("^"    . :vl-xor))
   :barops   '(("|->"  . :vl-bararrow)
               ("|=>"  . :vl-bareqarrow)
               ("|="   . :vl-oreq)
               ("||"   . :vl-logor)
               ("|"    . :vl-bitor))
   :dollarops '(("$root" . :vl-$root)
                ("$unit" . :vl-$unit)
                ("$"     . :vl-$))
   :quotesp    t
   :strextsp   t
   :timelitsp  t
   :extintsp   t
   :onestepp   t)
  ///
  (assert!
   ;; Basic sanity check, everything should be unique and valid.
   (let ((al (vl-lexstate->plainalist *vl-2012-strict-lexstate*)))
     (and (subsetp-equal (alist-vals al) *vl-2012-plain-nonkeywords*)
          (uniquep (alist-keys al))
          (uniquep (alist-vals al)))))
  (assert!
   ;; Make sure all new SystemVerilog keywords are accounted for.
   (b* ((al-2005  (vl-lexstate->plainalist *vl-2005-strict-lexstate*))
        (al-2012  (vl-lexstate->plainalist *vl-2012-strict-lexstate*))
        (kwds-2005 (alist-vals al-2005))
        (kwds-2012 (alist-vals al-2012))
        (new-used  (set-difference-equal kwds-2012 kwds-2005))
        (new-spec
         ;; SystemVerilog adds these keywords
         (set-difference-equal *vl-2012-plain-nonkeywords*
                               *vl-2005-plain-nonkeywords*)))
     (cw "New-used not in new-spec: ~x0.~%"
         (difference (mergesort new-used)
                     (mergesort new-spec)))
     (cw "New-spec not in new-used: ~x0.~%"
         (difference (mergesort new-spec)
                     (mergesort new-used)))
     (equal (mergesort new-used)
            (difference (mergesort new-spec)
                        ;; These are special because they're not just
                        ;; handled as simple plaintoken-alists.
                        (mergesort '(:vl-1step :vl-quote)))))))

(defval *vl-2012-lexstate*
  :parents (lexstate)
  :short "Configuration for extended (non-strict) SystemVerilog-2012 mode."
  (change-vl-lexstate *vl-2012-strict-lexstate*
                      :kwdtable *vl-2012-keyword-table*))

(define vl-lexstate-init
  :parents (lexstate)
  :short "User-level constructor for internal lexer states."
  ((config vl-loadconfig-p))
  :returns (st vl-lexstate-p)
  (b* (((vl-loadconfig config) config))
    (case config.edition
      (:verilog-2005 (if config.strictp
                         *vl-2005-strict-lexstate*
                       *vl-2005-lexstate*))
      (:system-verilog-2012 (if config.strictp
                                *vl-2012-strict-lexstate*
                              *vl-2012-lexstate*))
      (otherwise
       ;; Logically default to a good lexstate, for an unconditional return
       ;; value theorem.
       (progn$ (impossible)
               *vl-2012-lexstate*)))))
