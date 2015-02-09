; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "preprocessor")
(include-book "print-defines")
(local (include-book "../../util/arithmetic"))

;; This will get run any time the book is included.
(make-event (prog2$ (cw "preprocessor-tests.lisp is being included.  You ~
                         almost certainly do not want to do this.~%")
                    (value '(value-triple :invisible)))
            :check-expansion t)

(define vl-pps-defines ((x vl-defines-p))
  (with-local-ps (vl-pp-defines x)))

(define vl-pps-define-formals ((x vl-define-formallist-p))
  (with-local-ps (vl-pp-define-formals x)))


(define simple-test-defines
  ;; Turn a simple alist like (("foo" . "1") ("bar" . "2")) into a proper
  ;; vl-defines-p structure as if we'd just read:
  ;;
  ;;   `define foo 1
  ;;   `define bar 2
  ((al (and (alistp al)
            (string-listp (alist-keys al))
            (string-listp (alist-vals al)))))
  :returns (defs vl-defines-p)
  (b* (((when (atom al))
        nil)
       ((cons name val) (car al)))
    (cons (make-vl-define :name name
                          :body val
                          :formals nil
                          :loc *vl-fakeloc*)
          (simple-test-defines (cdr al)))))

(program)

(defmacro preprocessor-must-ignore (input &key defines)
  `(make-event
    (b* ((echars (vl-echarlist-from-str ,input))
         ((mv successp ?defs ?filemap output state)
          (vl-preprocess echars
                         :defines ,defines
                         :config (make-vl-loadconfig
                                  :include-dirs (list "."))))
         (- (or (debuggable-and successp
                                (equal echars output))
                (er hard? 'preprocessor-must-ignore "failed!"))))
      (value '(value-triple :success)))))

;; (preprocessor-must-ignore "`foo") ;; causes an error, good.

(preprocessor-must-ignore "foo")
(preprocessor-must-ignore "0.0 + 10'h4 * 10")
(preprocessor-must-ignore "// oneline comment")
(preprocessor-must-ignore "/* block comment */")
(preprocessor-must-ignore "10'h4")
(preprocessor-must-ignore "module")
(preprocessor-must-ignore "\\module")
(preprocessor-must-ignore "// comment with `define in it")
(preprocessor-must-ignore "\\escaped-identifier-with-`define-in-it")
(preprocessor-must-ignore "\"string with `define in it\"")



(defmacro preprocessor-basic-test (&key input defines output)
  `(make-event
    (b* ((echars (vl-echarlist-from-str ,input))
         ((mv successp ?defs ?filemap output state)
          (vl-preprocess echars
                         :defines ,defines
                         :config (make-vl-loadconfig
                                  :include-dirs (list "."))))
         (- (cw! "Successp:~x0~%Input:~%~s1~%Output:~%|~s2|~%"
                 successp ,input (vl-echarlist->string output)))
         (- (or (debuggable-and successp
                                (equal (vl-echarlist->string output) ,output))
                (er hard? 'preprocessor-basic-test "failed!"))))
      (value '(value-triple :success)))))


(preprocessor-basic-test
 :input "`ifdef foo
           random text
           // comments with hidden `endif
           \"string with hidden `endif\"
           \\escaped-identifier-with-`endif
           more random text
         `endif"
 :output ""
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 3 "
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 1 "
 :defines (simple-test-defines
           '(("foo" . "value of foo"))))

(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 1 "
 :defines (simple-test-defines
           '(("foo" . "value of foo")
             ("bar" . "value of bar"))))

(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 2 "
 :defines (simple-test-defines
           '(("bar" . "value of bar"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  1  "
 :defines (simple-test-defines
           '(("outer" . "1")
             ("foo"   . "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  1  "
 :defines (simple-test-defines
           '(("outer" . "1")
             ("foo" . "1")
             ("bar" . "1")
             ("baz" . "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  2  "
 :defines (simple-test-defines
           '(("outer" . "1")
             ("bar"   . "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  3  "
 :defines (simple-test-defines
           '(("outer" . "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output " 4 "
 :defines (simple-test-defines
           '(("baz" . "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output " 5 "
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "`define foo 3
`ifdef foo 1 `endif"
 :output "
 1 "
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`define foo 3
`undef foo
`ifdef foo 1 `endif"
 :output "

"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`define foo
`ifdef foo 1 `endif"
 :output "
 1 "
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "`define foo 3
`define bar `foo
`define foo 4
`bar"
 :output "


  4"
 :defines (simple-test-defines nil))




(preprocessor-basic-test
 :input "`timescale 1 ns / 10 ps"
 :output ""
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`timescale 1ms/10fs"
 :output ""
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`timescale 1 s /100us"
 :output ""
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`timescale 1 s /

      1

              s"
 :output ""
 :defines (simple-test-defines nil))



(preprocessor-basic-test
 :input "this is some `resetall text"
 :output "this is some  text"
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "this is `celldefine some more `endcelldefine and some more"
 :output "this is  some more  and some more"
 :defines (simple-test-defines nil))





;; This should cause an infinite loop.
;; (preprocessor-basic-test
;;  :input "`define foo 3
;; `define bar `foo
;; `define foo `bar
;; `bar"
;;  :defines nil)



(preprocessor-basic-test
 :input "//+VL test of special vl comments
"
 :output " test of special vl comments
"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "/*+VL test 2 of special vl comments */"
 :output " test 2 of special vl comments "
 :defines (simple-test-defines nil))



(preprocessor-basic-test
 :input "//+VL test of special vl comments
"
 :output " test of special vl comments
"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "/*@VL foo */"
 :output "(* foo *)"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "/*@VL foo, bar */"
 :output "(* foo, bar *)"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "//@VL foo, bar"
 :output "(* foo, bar*)"
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "//@VL foo, bar  // wow, a comment"
 :output "(* foo, bar  *)// wow, a comment"
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "//@VL foo, bar  /* a multiline one
too */"
 :output "(* foo, bar  *)/* a multiline one
too */"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "//@VL foo, bar  // wow, a comment
blah blah"
 :output "(* foo, bar  *)// wow, a comment
blah blah"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "//@VL foo // wow, a comment
blah blah"
 :output "(* foo *)// wow, a comment
blah blah"
 :defines (simple-test-defines nil))



(preprocessor-basic-test
 :input "`include \"test.txt\""
 :output "// this is used in preprocessor-tests.lisp
// do not delete it
"
 :defines (simple-test-defines nil))



; Well, the spacing here is kind of awful.  Make sure we can put preprocessor
; stuff into //+VL and //@VL stuff.

(preprocessor-basic-test
 :input "`define foo 1

//+VL assign w = `foo" ;
 :output "

 assign w =  1"
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "`define foo 1

/*+VL
assign w = `foo ;
*/"
 :output "


assign w =  1 ;
"
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "`define foo 1

/*@VL FOO = `foo */ assign bar = 2;"
 :output "

(* FOO =  1 *) assign bar = 2;"
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input "`define foo 1

//@VL FOO = `foo
assign bar = 2;"
 :output "

(* FOO =  1*)
assign bar = 2;"
 :defines (simple-test-defines nil))


#||
(trace$ (vl-expand-define
         :entry
         (list 'vl-expand-define
               name
               :defines (vl-pps-defines defines)
               :echars (vl-echarlist->string echars))
         :exit
         (let ((values acl2::values))
           (list 'vl-expand-define :okp (first values)
                 :new-echars (vl-echarlist->string (second values))))))

(trace$ vl-find-define)

(trace$ (vl-substitute-into-macro-text
        :entry
        (list 'vl-substitute-into-macro-text
              name
              :body body
              :subst subst
              :acc (reverse (vl-echarlist->string acc)))
        :exit
        (let ((values acl2::values))
          (list 'vl-substitute-into-macro-text
                name
                :okp (first values)
                :acc (reverse (vl-echarlist->string acc))))))


(trace$ (vl-line-up-define-formals-and-actuals
         :entry
         (list 'vl-line-up-define-formals-and-actuals
               name
               :formals (vl-pps-define-formals formals)
               :actuals actuals)
         :exit
         (let ((values acl2::values))
           (list 'vl-line-up-define-formals-and-actuals
                 :okp (first values)
                 :subst (second values)))))
||#

(preprocessor-basic-test
 :input "`define foo(a) a
assign b = `foo(c);"
 :output "
assign b =  c;"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`define foo(a) a+b
assign b = `foo(c);"
 :output "
assign b =  c+b;"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`define foo(a) a /* la, la */ +b // la, la
assign b = `foo(c /* blah, la, la */
// more comments, la, la
);"
 :output "
assign b =  c /* la, la */ +b ;"
 :defines (simple-test-defines nil))


