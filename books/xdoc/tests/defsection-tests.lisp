; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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

(in-package "XDOC")
(include-book "../top")
(include-book "std/util/bstar" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

(defxdoc test :short "Test of defsection")

(defsection foo1
  :parents (test)
  :autodoc nil
  (defun foo1 (x) x))

(defsection foo2
  :parents (test)
  (defun foo2 (x) x))

(defsection foo3
  :parents (test)
  :short "Section for foo3"
  :long "<p>Foo3 is wonderful.</p>"

  (defund foo3 (x) (+ 1 x))

  (local (in-theory (enable foo3)))

  (defthm natp-of-foo3
    (implies (natp x)
             (natp (foo3 x))))

  (local (defthm foo3-lemma
           (implies (equal x 3)
                    (equal (foo3 x) 4))))

  (defmacro foo3-alias (x)
    `(foo3 ,x))

  (defsection bar
    :parents (test)
    :short "Section for bar"
    :long "<p>Bar is wonderful.</p>"
    (defund bar (x) (+ 2 x))))

;; BOZO the theorems in the nested section are leaking out into the superior
;; section... ugh.


(defsection foo3-advanced
  :extension foo3

  (local (in-theory (enable foo3)))

  (defthm posp-of-foo3
    (implies (natp x)
             (posp (foo3 x))))

  (defthm oddp-of-foo3
    (implies (evenp x)
             (oddp (foo3 x)))))


(defsection foo3-advanced-more
  :extension foo3
  :long "<h3>Even more theorems!</h3>"

  (local (in-theory (enable foo3)))

  (defthm integerp-of-foo3
    (implies (integerp x)
             (integerp (foo3 x)))))




(defxdoc short-eval-test
  :short (concatenate 'string "Test of evaluation of " ":short strings."))

(defxdoc long-eval-test
  :long (concatenate 'string "Test of evaluation of " ":long strings."))

(assert! (stringp (cdr (assoc :short (find-topic 'short-eval-test (get-xdoc-table (w state)))))))
(assert! (stringp (cdr (assoc :long (find-topic 'long-eval-test (get-xdoc-table (w state)))))))

(defsection short-eval-test-2
  :short (concatenate 'string "Test of evaluation of " ":short strings, for defsection."))

(defsection long-eval-test-2
  :long (concatenate 'string "Test of evaluation of " ":long strings, for defsection."))

(assert! (stringp (cdr (assoc :short (find-topic 'short-eval-test-2 (get-xdoc-table (w state)))))))
(assert! (stringp (cdr (assoc :long (find-topic 'long-eval-test-2 (get-xdoc-table (w state)))))))

(defsection ext-test
  :extension long-eval-test
  :long (concatenate 'string "Test of evaluation of " "extension strings"))

(xdoc-extend short-eval-test
             (concatenate 'string "test of evaluation of " "xdoc-extend strings"))

(assert! (stringp (cdr (assoc :short (find-topic 'short-eval-test (get-xdoc-table (w state)))))))

(xdoc-prepend short-eval-test
             (concatenate 'string "test of evaluation of " "xdoc-prepend strings"))

(assert! (stringp (cdr (assoc :short (find-topic 'short-eval-test (get-xdoc-table (w state)))))))



(defsection ext-test-2
  :extension (long-eval-test)
  :long "Test of new :extension (foo) feature.")



(xdoc::set-default-parents nil)

(defsection double-extension-test
  :short "Test of double extensions"
  :long "<p>Blah1</p>"
  (defun det-f1 (x) x))

(defthm det-f1-identity (equal (det-f1 x) x))

(defsection det-extension-1
  :extension (double-extension-test)
  :long "<p>Blah2</p>"
  (defun det-f2 (x) x))

(defthm det-f2-identity (equal (det-f2 x) x))

(defsection det-extension-1
  :extension (double-extension-test)
  :long "<p>Blah3</p>"
  (defun det-f3 (x) x))

(defthm det-f3-identity (equal (det-f3 x) x))

(assert!
 (b* ((topic (find-topic 'double-extension-test (get-xdoc-table (w state))))
      (long  (cdr (assoc :long topic))))
   (and (str::substrp "@(def |XDOC|::|DET-F1|)" long)
        (str::substrp "@(def |XDOC|::|DET-F2|)" long)
        (str::substrp "@(def |XDOC|::|DET-F3|)" long)
        (str::substrp "Blah1" long)
        (str::substrp "Blah2" long)
        (str::substrp "Blah3" long)
        (not (str::substrp "@(def |XDOC|::|DET-F1-IDENTITY|)" long))
        (not (str::substrp "@(def |XDOC|::|DET-F2-IDENTITY|)" long))
        (not (str::substrp "@(def |XDOC|::|DET-F3-IDENTITY|)" long)))))






(xdoc::set-default-parents whatever)

(defsection double-extension-test2
  :short "Test of double extensions"
  :long "<p>Blooop1</p>"
  (defun det2-f1 (x) x))

(defthm det2-f1-identity (equal (det2-f1 x) x))

(defsection det2-extension-1
  :extension (double-extension-test2)
  :long "<p>Blooop2</p>"
  (defun det2-f2 (x) x))

(defthm det2-f2-identity (equal (det2-f2 x) x))

(defsection det2-extension-2
  :extension (double-extension-test2)
  :long "<p>Blooop3</p>"
  (defun det2-f3 (x) x))

(defthm det2-f3-identity (equal (det2-f3 x) x))

(assert!
 (b* ((topic (find-topic 'double-extension-test2 (get-xdoc-table (w state))))
      (long  (cdr (assoc :long topic))))
   (and (str::substrp "@(def |XDOC|::|DET2-F1|)" long)
        (str::substrp "@(def |XDOC|::|DET2-F2|)" long)
        (str::substrp "@(def |XDOC|::|DET2-F3|)" long)
        (str::substrp "Blooop1" long)
        (str::substrp "Blooop2" long)
        (str::substrp "Blooop3" long)
        (not (str::substrp "@(def |XDOC|::|DET2-F1-IDENTITY|)" long))
        (not (str::substrp "@(def |XDOC|::|DET2-F2-IDENTITY|)" long))
        (not (str::substrp "@(def |XDOC|::|DET2-F3-IDENTITY|)" long)))))


#||

; Error Reporting Tests.
;
; These are meant to be run interactively because the goal is to test out how
; defsection output looks when various errors occur.

;; --- These should report an error at the top level with macro-expansion. ---

;; [Great] no noise:
(defsection)

;; [Ugly] extra nonsense about TOP-LEVEL and macroexpansion failing.
(defsection nil)
(defsection "error with name")
(defsection "error with name" (defun oops (x) x))


;; --- These should report an error with the xdoc form. ---

;; [Great] no noise:
(defsection oops :short 17 :autodoc nil)
(defsection oops :long 17 :autodoc nil)
(defsection oops :parents 17 :autodoc nil (defun blah))
(defsection oops :short 17 :autodoc nil (defun blah))
(defsection oops :long 17 :autodoc nil (defun blah))
(defsection oops :parents 17 :autodoc nil)
(defsection oops :parents 17)
(defsection oops :short 17)
(defsection oops :long 17)

;; [Ugly] big pile of "encapsulate" messages after the error.
(defsection oops :parents 17 (defun blah))
(defsection oops :short 17 (defun blah))
(defsection oops :long 17 (defun blah))

;; --- Extension not allowed with other xdoc args ---

;; [Ugly] extra nonsense about TOP-LEVEL and macroexpansion failing
(defsection oops :extension (append) :short "Hello")
(defsection oops :extension (append) :short "Hello" :autodoc nil)
(defsection oops :extension (append) :short "Hello" (defun blah))
(defsection oops :extension (append) :short "Hello" :autodoc nil (defun blah))
(defsection oops :extension (append) :autodoc nil)
(defsection oops :extension (append) :autodoc nil (defun blah))

;; --- Extending topic that doesn't exist ---

;; [Ugly] Error in (table xdoc) nonsense
(defsection oops :extension (this-should-never-exist))

;; [Ugly] big pile of "encapsulate" messages, as above
(defsection oops :extension (this-should-never-exist) (defun blah))

;; [Ugly] error in TOP-LEVEL nonsense about macroexpansion
(defsection oops :extension (this-should-never-exist) :autodoc nil)
(defsection oops :extension (this-should-never-exist) :autodoc nil (defun blah))

;; --- Errors in internal forms ---

;; [Ugly] big pile of "encapsulate" messages and ugly encapsulate summary
(defsection oops (defun blah))
(defsection oops :autodoc nil (defun blah))


||#
