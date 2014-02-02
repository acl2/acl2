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
(include-book "preprocessor")
(local (include-book "../../util/arithmetic"))

(program)

;; This will get run any time the book is included.
(make-event (prog2$ (cw "preprocessor-tests.lisp is being included.  You ~
                         almost certainly do not want to do this.~%")
                    (value '(value-triple :invisible)))
            :check-expansion t)



(defmacro preprocessor-must-ignore (input &key defines)
  `(make-event
    (b* ((echars                     (vl-echarlist-from-str ,input))
         ((mv successp ?defs output state)
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
    (b* ((echars                           (vl-echarlist-from-str ,input))
         ((mv successp ?defs output state)
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
 :defines nil)




(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 3 "
 :defines nil)

(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 1 "
 :defines (list (cons "foo" (vl-echarlist-from-str "value of foo"))))

(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 1 "
 :defines (list (cons "foo" (vl-echarlist-from-str "value of foo"))
                (cons "bar" (vl-echarlist-from-str "value of bar"))))

(preprocessor-basic-test
 :input "`ifdef foo 1 `elsif bar 2 `else 3 `endif"
 :output " 2 "
 :defines (list (cons "bar" (vl-echarlist-from-str "value of bar"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  1  "
 :defines (list (cons "outer" (vl-echarlist-from-str "1"))
                (cons "foo"   (vl-echarlist-from-str "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  1  "
 :defines (list (cons "outer" (vl-echarlist-from-str "1"))
                (cons "foo"   (vl-echarlist-from-str "1"))
                (cons "bar"   (vl-echarlist-from-str "1"))
                (cons "baz"   (vl-echarlist-from-str "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  2  "
 :defines (list (cons "outer" (vl-echarlist-from-str "1"))
                (cons "bar"   (vl-echarlist-from-str "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output "  3  "
 :defines (list (cons "outer" (vl-echarlist-from-str "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output " 4 "
 :defines (list (cons "baz" (vl-echarlist-from-str "1"))))

(preprocessor-basic-test
 :input (cat "`ifdef outer "
             "`ifdef foo 1 `elsif bar 2 `else 3 `endif "
             "`elsif baz 4 "
             "`else 5 "
             "`endif")
 :output " 5 ")







(preprocessor-basic-test
 :input "`define foo 3
`ifdef foo 1 `endif"
 :output "
 1 "
 :defines nil)

(preprocessor-basic-test
 :input "`define foo 3
`undef foo
`ifdef foo 1 `endif"
 :output "

"
 :defines nil)

(preprocessor-basic-test
 :input "`define foo
`ifdef foo 1 `endif"
 :output "
 1 "
 :defines nil)




(preprocessor-basic-test
 :input "`define foo 3
`define bar `foo
`define foo 4
`bar"
 :output "


  4"
 :defines nil)




(preprocessor-basic-test
 :input "`timescale 1 ns / 10 ps"
 :output "")

(preprocessor-basic-test
 :input "`timescale 1ms/10fs"
 :output "")

(preprocessor-basic-test
 :input "`timescale 1 s /100us"
 :output "")

(preprocessor-basic-test
 :input "`timescale 1 s /

      1

              s"
 :output "")



(preprocessor-basic-test
 :input "this is some `resetall text"
 :output "this is some  text")


(preprocessor-basic-test
 :input "this is `celldefine some more `endcelldefine and some more"
 :output "this is  some more  and some more")





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
")

(preprocessor-basic-test
 :input "/*+VL test 2 of special vl comments */"
 :output " test 2 of special vl comments ")



(preprocessor-basic-test
 :input "//+VL test of special vl comments
"
 :output " test of special vl comments
")

(preprocessor-basic-test
 :input "/*@VL foo */"
 :output "(* foo *)")

(preprocessor-basic-test
 :input "/*@VL foo, bar */"
 :output "(* foo, bar *)")

(preprocessor-basic-test
 :input "//@VL foo, bar"
 :output "(* foo, bar*)")


(preprocessor-basic-test
 :input "//@VL foo, bar  // wow, a comment"
 :output "(* foo, bar  *)// wow, a comment")


(preprocessor-basic-test
 :input "//@VL foo, bar  /* a multiline one
too */"
 :output "(* foo, bar  *)/* a multiline one
too */")

(preprocessor-basic-test
 :input "//@VL foo, bar  // wow, a comment
blah blah"
 :output "(* foo, bar  *)// wow, a comment
blah blah")

(preprocessor-basic-test
 :input "//@VL foo // wow, a comment
blah blah"
 :output "(* foo *)// wow, a comment
blah blah")



(preprocessor-basic-test
 :input "`include \"test.txt\""
 :output "// this is used in preprocessor-tests.lisp
// do not delete it
")



; Well, the spacing here is kind of awful.  Make sure we can put preprocessor
; stuff into //+VL and //@VL stuff.

(preprocessor-basic-test
 :input "`define foo 1

//+VL assign w = `foo" ;
 :output "

 assign w =  1")


(preprocessor-basic-test
 :input "`define foo 1

/*+VL
assign w = `foo ;
*/"
 :output "


assign w =  1 ;
")


(preprocessor-basic-test
 :input "`define foo 1

/*@VL FOO = `foo */ assign bar = 2;"
 :output "

(* FOO =  1 *) assign bar = 2;")


(preprocessor-basic-test
 :input "`define foo 1

//@VL FOO = `foo
assign bar = 2;"
 :output "

(* FOO =  1*)
assign bar = 2;")

