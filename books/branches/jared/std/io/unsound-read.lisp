; Serializing ACL2 Objects
; Copyright (C) 2009-2012 Centaur Technology
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

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)
; (depends-on "unsound-read-raw.lsp")

(defxdoc unsound-read
  :parents (std/io serialize)
  :short "A faster alternative to @(see serialize-read), which is unsound in
general, but may be fine in many common cases."

  :long "<p>The @('unsound-read') is like @(see serialize-read) except that it
does not take @(see state).  This means it works even in ordinary @(see
defconst) events, which avoids the performance penalty of using @(see
make-event) to read files, as described in @(see serialize-in-books).</p>

<p>As its name suggests, @('unsound-read') is unsound and it can easily be used
to prove @('nil'); see below.  Because of this, unlike the other @(see
serialize) routines, it is not build it into ACL2; instead, to use it you must
first include its book, which requires a <see topic='@(url defttag)'>trust
tag</see>:</p>

@({
 (include-book \"std/io/unsound-read\" :dir :system :ttags (:unsound-read))
})

<p>General form:</p>

@({
  (unsound-read filename
                [:hons-mode {:always, :never, :smart}]
                [:verbose   {t, nil}])
    -->
  obj
})

<p>The arguments are as in @(see serialize-read).</p>


<h3>Explanation of Unsoundness</h3>

<p>The logical problem with @('unsound-read') is that, like any other function,
it is expected to satisfy the functional equality axiom schema, namely,</p>

@({
  (equal (unsound-read-fn filename hons-mode verbosep)
         (unsound-read-fn filename hons-mode verbosep))
})

<p>But we can easily violate this property by modifying the file system between
calls of @('unsound-read').  For instance, here is a proof of @('nil') that is
carried out in @('std/io/serialize-tests.lisp'):</p>

@({
  (local
   (encapsulate
    ()
    ;; Write NIL to test.sao
    (make-event
     (let ((state (serialize-write \"test.sao\" nil)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains NIL.
    (defthm lemma-1
      (equal (unsound-read \"test.sao\") nil)
      :rule-classes nil)

    ;; Write T to test.sao
    (make-event
     (let ((state (serialize-write \"test.sao\" t)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains T.
    (defthm lemma-2
      (equal (unsound-read \"test.sao\") t)
      :rule-classes nil)

    ;; Arrive at our contradiction.
    (defthm qed
      nil
      :rule-classes nil
      :hints((\"Goal\"
              :use ((:instance lemma-1)
                    (:instance lemma-2))
              :in-theory (disable (unsound-read-fn)))))))
})

<h3>Avoiding Unsoundness</h3>

<p>If you want to safely use @('unsound-read') to read some file, @('foo.sao'),
then you should not change @('foo.sao') after reading it.</p>

<p>A common scenario is that you have some book, @('foo.lisp'), that uses
@('unsound-read') to load @('foo.sao'), using a @(see defconst) event.  In this
case, simply adding a @('depends-on') line such as:</p>

@({
    ; (depends-on \"foo.sao\")
    (defconst *contents* (unsound-read \"foo.sao\"))
})

<p>May, at least for users of @('cert.pl'), offer some minimal
protection. (This @('depends-on') line tells cert.pl to rebuild @('foo.cert')
any time that @('foo.sao') changes.)</p>")

(defttag :unsound-read)

; We use this stub in the logical definition, so that you can't
; directly reason about the value of unsound-read.

(defstub unsound-read-fn-logical-def (filename honsp verbosep)
  t)

(defun unsound-read-fn (filename hons-mode verbosep)
  (declare (xargs :guard (and (stringp filename)
                              (member-eq hons-mode '(:always :never :smart))
                              (booleanp verbosep))))
  (prog2$
   (er hard? 'unsound-read-fn "Raw-lisp definition not installed??")
   (unsound-read-fn-logical-def filename hons-mode verbosep)))

(defmacro unsound-read (filename &key
                                 (hons-mode ':smart)
                                 verbosep)
  `(unsound-read-fn ,filename ,hons-mode ,verbosep))

(include-raw "unsound-read-raw.lsp")
