; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "print-defines")
(include-book "../../mlib/print-warnings")
(include-book "oslib/ls" :dir :system)
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
    (b* ((__function__ 'preprocessor-must-ignore)
         (echars (vl-echarlist-from-str ,input))
         (include-dirs (list "."))
         (warnings nil)
         ((mv idcache ?warnings state)
          (vl-make-dirlist-cache include-dirs warnings state))
         ((mv successp ?defs ?filemap ?iskips ?ifdefmap ?defmap ?bytes warnings output state)
          (vl-preprocess echars
                         :defines ,defines
                         :config (make-vl-loadconfig :include-dirs include-dirs)
                         :idcache idcache
                         :warnings warnings
                         :bytes 0))
         (- (vl-free-dirlist-cache idcache))
         (- (or (debuggable-and successp
                                (equal echars output))
                (raise "expected ~s0, got ~s1"
                       (vl-echarlist->string echars)
                       (vl-echarlist->string output))))
         (- (or (not warnings)
                (raise "unexpected warnings: ~s0~%" (vl-warnings-to-string warnings)))))
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



(defmacro preprocessor-basic-test (&key input defines output warnings-expectedp must-failp)
  `(make-event
    (b* ((__function__ 'preprocessor-basic-test)
         (echars (vl-echarlist-from-str ,input :filename "test.v"))
         (include-dirs (list "."))
         (warnings nil)
         ((mv idcache warnings state)
          (vl-make-dirlist-cache include-dirs warnings state))
         ((mv successp ?defs ?filemap ?iskips ?ifdefmap ?defmap ?bytes warnings output state)
          (vl-preprocess echars
                         :defines ,defines
                         :config (make-vl-loadconfig :include-dirs include-dirs)
                         :idcache idcache
                         :warnings warnings
                         :bytes 0))
         (- (vl-free-dirlist-cache idcache))
         (- (cw! "Successp:~x0~%Input:~%~s1~%Output:~%|~s2|~%Expected:~%|~s3|~%"
                 successp
                 ,input
                 (vl-echarlist->string output)
                 ,output))
         ((when ',must-failp)
          (or (not successp)
              (raise "Failed to fail!"))
          (value '(value-triple :success)))
         (- (or (debuggable-and successp
                                (equal (vl-echarlist->string output) ,output))
                (raise "failed!")))
         (- (if (and warnings (not ,warnings-expectedp))
                (raise "unexpected warnings: ~s0~%" (vl-warnings-to-string warnings))
              t))
         (- (if (and ,warnings-expectedp (not warnings))
                (raise "expected warnings but got none!")
              t)))
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
 :defines (simple-test-defines nil)
 :warnings-expectedp t ;; because we're redefining foo
 )




(preprocessor-basic-test
 :input "`timescale 1 ns / 10 ps"
 :output "`timescale 1 ns / 10 ps"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`timescale 1ms/10fs"
 :output "`timescale 1ms/10fs"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`timescale 1 s /100us"
 :output "`timescale 1 s /100us"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`timescale 1 s /

      1

              s"
 :output "`timescale 1 s /

      1

              s"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`timescale `foo"
 :output "`timescale 1ns / 10 ps"
 :defines (simple-test-defines '(("foo" . "1ns / 10 ps"))))

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
 :defines (simple-test-defines nil)
 ;; since there isn't an include guard
 :warnings-expectedp t)



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

(preprocessor-basic-test
 :input "`define foo(a,b=bar) a + b
assign b = `foo(c);"
 :output "
assign b =  c + bar;"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`define foo(a,b=bar) a + b
assign b = `foo(c,d);"
 :output "
assign b =  c + d;"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`define foo(a,b=\\foo,bar ) a + b
assign b = `foo(c);"
 :output "
assign b =  c + \\foo,bar ;"
 :defines (simple-test-defines nil))

(preprocessor-basic-test
 :input "`define foo(a,b=) a b
assign b = `foo(c);"
 :output "
assign b =  c ;"
 :defines (simple-test-defines nil))




;; Some tests of the new fancy define escape sequences for string/id construction

(preprocessor-basic-test
 :input #{"""
`define test1 "hello"
wire [800:0] found1 = `test1;
"""}


 :output #{"""

wire [800:0] found1 =  "hello";
"""}
 :defines (simple-test-defines nil))



(preprocessor-basic-test
 :input #{"""
`define test2(world) "hello world"
wire [800:0] found2 = `test2(moon);
"""}
;; It appears that VCS does not correctly handle this case.  It does the
;; substitution, producing hello moon.  However, NCV properly avoids
;; substituting into the string literal.

 :output #{"""

wire [800:0] found2 =  "hello world";
"""}
 :defines (simple-test-defines nil))




(preprocessor-basic-test
 :input #{"""
`define test3(world) `"hello world`"
wire [800:0] found3 = `test3(moon);
"""}
 :output #{"""

wire [800:0] found3 =  "hello moon";
"""}
 :defines (simple-test-defines nil))

;; (trace$ (vl-read-until-end-of-define
;;          :entry (list 'vl-read-until-end-of-define (vl-echarlist->string echars))
;;          :exit (b* (((list successp prefix remainder) acl2::values))
;;                  (list 'vl-read-until-end-of-define successp
;;                        :prefix (vl-echarlist->string prefix)
;;                        :remainder (vl-echarlist->string remainder)))))

;; (trace$ (vl-expand-define
;;          :entry (list 'vl-expand-define name
;;                       :echars (vl-echarlist->string echars))
;;          :exit (b* (((list successp new-echars) acl2::values))
;;                  (list 'vl-expand-define 
;;                        successp (vl-echarlist->string new-echars)))))

(preprocessor-basic-test
 :input #{"""
`define FOO `"FOO`"
 wire [24:0] foo = `FOO;
"""}
 :output #{"""

 wire [24:0] foo =  "FOO";
"""})

(preprocessor-basic-test
 :input #{"""
`define test4(world) `"hello``world`"
wire [800:0] found4 = `test4(moon);
"""}
 :output #{"""

wire [800:0] found4 =  "hellomoon";
"""}
 :defines (simple-test-defines nil))


(preprocessor-basic-test
 :input #{"""
`define test5(world) `"hello`\`"world`"
wire [800:0] found5 = `test5(moon);
"""}

 :output #{"""

wire [800:0] found5 =  "hello\"moon";
"""}
 :defines (simple-test-defines nil))

;; extra quote to help emacs colorize this "


;; Fancy interactions between `include and the rest of the preprocessor

(preprocessor-basic-test
 :input #{"""
`define addtxt(arg) `"arg.txt`"
`include `addtxt(test)
"""}
 :output #{"""

// this is used in preprocessor-tests.lisp
// do not delete it

"""}
 :defines (simple-test-defines nil)
 ;; since there's no include-guard
 :warnings-expectedp t)



(preprocessor-basic-test
 :input #{"""
`define foo
`include `ifdef foo "test.txt" `else "do-not-include-this.txt" `endif
hello
"""}
 :output #{"""

// this is used in preprocessor-tests.lisp
// do not delete it
 
hello
"""}
 :defines (simple-test-defines nil)
 ;; since there's no include guard
 :warnings-expectedp t)



;; Nasty corner cases for the interaction of escaped identifiers and `` stuff.

(preprocessor-basic-test   ;; Corner1: NCV/VCS agree
 :input #{"""
`define mac(name) wire mac``name = 1;
`mac(blah)
"""}
 :output #{"""

 wire macblah = 1;
"""})


(preprocessor-basic-test   ;; Corner2: NCV/VCS agree
 :input #{"""
`define mac(name) wire name``_mac = 1;
`mac(blah)
"""}
 :output #{"""

 wire blah_mac = 1;
"""})


(preprocessor-basic-test  ;; Corner3: NVC/VCS agree
 :input #{"""
`define mac(name) wire \mac_``name = 1;
`mac(blah)
"""}
 :output #{"""

 wire \mac_blah = 1;
"""})



(preprocessor-basic-test   ;; Corner4: NCV/VCS agree
 :input #{"""
`define mac(arg) wire \foo`arg = 1;
`mac(blah)
"""}
 :output #{"""

 wire \foo`blah = 1;
"""})


(preprocessor-basic-test   ;; Corner5: NCV/VCS agree
 :input #{"""
`define mac(arg) wire \arg = 1;
`mac(blah)
"""}
 :output #{"""

 wire \blah = 1;
"""})


(preprocessor-basic-test   ;; Corner6: NCV segfaults (seriously), VCS acts as below
 :input #{"""
`define mac(arg) wire \`arg = 1;
`mac(blah)
"""}
 :output #{"""

 wire \`blah = 1;
"""})


(preprocessor-basic-test   ;; Corner7: NCV/VCS agree
 :input #{"""
`define blah mywire
`define mac(arg) wire `arg = 1;
`mac(blah)
"""}
;; not sure why I get an extra space between wire and mywire...
 :output #{"""


 wire  mywire = 1;
"""})


(preprocessor-basic-test   ;; Corner8: NCV/VCS disagree

 ;; We (arbitrarily) behave like VCS in this case.

 ;; In contrast, NCVerilog does not perform the variable substitution
 ;; and instead creates a wire named \arg+1.

 :input #{"""
`define mac(arg) wire \arg+1 = 1;
`mac(blah)
"""}

 :output #{"""

 wire \blah+1 = 1;
"""})


(preprocessor-basic-test   ;; Corner9: NCV/VCS disagree
 :input #{"""
`define mac(name) wire \``name``_mac = 1;
`mac(blah)
"""}
 :output #{"""

 wire \blah_mac = 1;
"""})

(preprocessor-basic-test
 :input #{"""
The file is `__FILE__
"""}
 :output #{"""
The file is "test.v"
"""})

(preprocessor-basic-test
 :input #{"""
The line is `__LINE__
"""}
 :output #{"""
The line is 2
"""})



; Tests of weird `" behavior in macro arguments

(preprocessor-basic-test
 :input #{"""
`define foo(x) x
assign w = `foo("bar");
"""}
 :output #{"""

assign w =  "bar";
"""})

(preprocessor-basic-test
 :input #{"""
`define foo(x) x
assign w = `foo(`"bar`");
"""}
 :output #{"""

assign w =  "bar";
"""})

(preprocessor-basic-test
 :input #{"""
`define foo(x,y) x
`define xx 123
assign w = `foo(`"bar`", `xx);
"""}
 :output #{"""


assign w =  "bar";
"""})

(preprocessor-basic-test
 :input #{"""
`define foo(x) x
assign w = `foo(`"\101bc`");
"""}
 :output #{"""

assign w =  "\101bc";
"""})

(preprocessor-basic-test
 :input #{"""
`define foo(x) x
assign w = `foo(`"bar");
"""}
 :must-failp t)

(preprocessor-basic-test
 :input #{"""
`define foo(x) x
assign w = `foo(`");
"""}
 :must-failp t)

;; Extra closing quote to make emacs highlight better "

(preprocessor-basic-test
 :input #{"""
`define foo(x) x
assign w = `foo(`"bar);
"""}
 :must-failp t)

;; Extra closing quote to make emacs highlight better "

(preprocessor-basic-test
 :input #{"""
`define foo(x) x`"
assign w = `foo(`"bar);
"""}
 :must-failp t)

(preprocessor-basic-test
 :input #{"""
`define foo(x,y) x
assign w = `foo(`"bar`", baz);
"""}
 :output #{"""

assign w =  "bar";
"""})


(preprocessor-basic-test
 :input
 #{"""
`define FOO_BAZ 5
`define FOO_BAR(bar, tasty, flavor, sausage)\
    FOO_FN((bar), (tasty), (flavor), `__FILE__, `__LINE__, (sausage))
`define FOO_TOP(tasty, flavor, sausage)\
    `FOO_BAR(null, (tasty), (flavor), (sausage))
`FOO_TOP(`"oink`", `FOO_BAZ, $psprintf("lalala %x %y", xxx, yyy));
"""}

 :output
 #{"""




    
    FOO_FN((null), (("oink")), (( 5)), "test.v", 7, (($psprintf("lalala %x %y", xxx, yyy))));
"""})


