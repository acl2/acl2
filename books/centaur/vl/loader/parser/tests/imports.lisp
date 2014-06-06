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
(include-book "base")
(include-book "../imports")

(define vl-pretty-import ((x vl-import-p))
  (list 'import
        (vl-import->pkg x)
        (vl-import->part x)
        (vl-pretty-atts (vl-import->atts x))))

(defprojection vl-pretty-imports ((x vl-importlist-p))
  (vl-pretty-import x))

(defmacro test-import (&key input expect (successp 't) atts)
  `(assert! (let ((tokens (make-test-tokens ,input))
                  (warnings nil)
                  (config *vl-default-loadconfig*))
              (mv-let (erp val tokens warnings)
                (vl-parse-package-import-declaration ,atts)
                (declare (ignore tokens))
                (if erp
                    (prog2$
                     (cw "ERP is ~x0.~%" erp)
                     (not ,successp))
                  (prog2$
                   (cw "VAL is ~x0.~%" val)
                   (debuggable-and ,successp
                                   (equal (vl-pretty-imports val) ,expect)
                                   (not warnings))))))))


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
             :atts (list (cons "myatt" (vl-idexpr "myval" nil nil)))
             :expect '((import "foo" :vl-import* (("myatt" <- (id "myval"))))
                       (import "foo" "bar"       (("myatt" <- (id "myval"))))))



(test-import :input "import"  ;; sanity check early eof
             :successp nil)

(test-import :input "import ;"  ;; need at least one item
             :successp nil)

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



