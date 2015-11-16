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
(include-book "base")
(include-book "../imports")

(define vl-pretty-import ((x vl-import-p))
  (list 'import
        (vl-import->pkg x)
        (vl-import->part x)
        (vl-pretty-atts (vl-import->atts x))))

(defprojection vl-pretty-imports ((x vl-importlist-p))
  (vl-pretty-import x))

(encapsulate nil
  (local (in-theory (enable vl-is-token?
                            vl-lookahead-is-token?
                            )))
  (defparser-top vl-parse-package-import-declaration
    :guard (and (vl-lookahead-is-token? :vl-kwd-import tokens)
                (vl-lookahead-is-token? :vl-idtoken (cdr tokens))
                (vl-atts-p atts))))

(defmacro test-import (&key input expect (successp 't) atts)
  `(assert! (b* ((tokens (make-test-tokens ,input))
                 (pstate (make-vl-parsestate :warnings nil))
                 (config *vl-default-loadconfig*)
                 ((mv erp val ?tokens (vl-parsestate pstate))
                  (vl-parse-package-import-declaration-top ,atts))
                 ((when erp)
                  (cw "ERP is ~x0.~%" erp)
                  (not ,successp)))
              (cw "VAL is ~x0.~%" val)
              (debuggable-and ,successp
                              (equal (vl-pretty-imports val) ,expect)
                              (not pstate.warnings)))))

(test-import :input "import foo::*;"
             :expect '((import "foo" :vl-import* nil)))

(test-import :input "import foo :: bar;"
             :expect '((import "foo" "bar" nil)))

(test-import :input "import foo::baz;"
             :expect '((import "foo" "baz" nil)))

(test-import :input "import \\foo-bar ::baz;"
             :expect '((import "foo-bar" "baz" nil)))

(test-import :input "import \\foo-bar ::\\baz-beep ;"
             :expect '((import "foo-bar" "baz-beep" nil)))

(test-import :input "import foo::*, foo::bar;"
             :expect '((import "foo" :vl-import* nil)
                       (import "foo" "bar" nil)))

(test-import :input "import foo::bar, foo::baz;"
             :expect '((import "foo" "bar" nil)
                       (import "foo" "baz" nil)))

(test-import :input "import foo::*, foo::bar;"
             :atts (list (cons "myatt" (vl-idexpr "myval")))
             :expect '((import "foo" :vl-import* (("myatt" <- (id "myval"))))
                       (import "foo" "bar"       (("myatt" <- (id "myval"))))))


;; These are now ruled out by our guard due to adding DPI stuff.

;; (test-import :input "import"  ;; sanity check early eof
;;              :successp nil)

;; (test-import :input "import ;"  ;; need at least one item
;;              :successp nil)

(test-import :input "import foo::*" ;; missing semicolon
             :successp nil)

(test-import :input "import foo, bar;"  ;; missing :: stuff
             :successp nil)

(test-import :input "import \\foo-bar ::\\baz-beep; " ;; missing space after baz-beep
             :successp nil)

(test-import :input "import foo::*, foo::bar" ;; no semicolon
             :successp nil)

(test-import :input "import foo::*, foo::bar, " ;; no item
             :successp nil)

(test-import :input "import foo::*, foo::bar, foo:: ;" ;; no name
             :successp nil)

(test-import :input "import foo::*, foo::bar, foo ;" ;; no name
             :successp nil)

(test-import :input "import foo::*, foo::bar, foo"
             :successp nil)



