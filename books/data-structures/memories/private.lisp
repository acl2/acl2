;
; Memories: Array-like Records for ACL2
; Copyright (C) 2005-2006 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>
;



; private.lisp
;
; This file provides the "private" macro, which is used in memory.lisp to
; provide auxilliary/implementation functions that a user should not be allowed
; to work with directly.  The macro is generic and may be of use to the authors
; of other libraries.

(in-package "MEM")
(include-book "xdoc/top" :dir :system)

(defxdoc private
  :parents (memory)
  :short "Redundantly define, then serverely restrict the usage of some function."
  :long "<p>Example:</p>

@({
     (private foo (x y)
        (if (atom x)
            ...))
})

<p>@('private') is a macro which may be useful for authors of libraries, or to
users who want to enforce severe discipline upon themselves.</p>

<p>The macro is similar to @(see defund) in that it first introduces a defun
and then immediately disables its definition.  However, @('private') goes
further: it also disables the resulting type-prescription rule and sets up
@(see theory-invariant)s that prohibit the user from ever enabling the
definition or the type prescription.</p>

<p>Why would we want such a thing?  A nice way to develop libraries is to use
@(see acl2::redundant-events) in an interface file, so that users never even
see the local lemmas and so forth that you used to get the proofs to go
through.  This gives you the freedom to change and remove those definitions at
will.</p>

<p>Unfortunately, you cannot do the same for functions, because ACL2 needs the
functions available in the interface book if they are ever used.  With
@('private'), you can identify functions that you want to keep control over and
that the user should either (1) not be using at all, or (2) only be reasoning
about using the theorems your have provided.</p>

<p>To use private, simply copy your @('(defun foo ...)') form into your
interface file, then replace @('defun') with @('private').</p>")

(defmacro private (&rest def)
  (declare (xargs :guard (and (true-listp def)
                              (symbolp (car def))
                              (symbol-listp (cadr def)))))
  `(progn

     ;; First introduce the function itself
     (defun ,@def)

     ;; Now disable the :definition and :type-prescription rules
     (with-output :off summary
                  (in-theory (disable (:definition ,(car def))
                                      (:type-prescription ,(car def)))))

     ;; Now create a theory invariant named foo-is-private, which will cause an
     ;; error if the user ever tries to enable these rules
     (with-output :off summary
                  (theory-invariant
                   (and (not (active-runep '(:definition ,(car def))))
                        (not (active-runep '(:type-prescription ,(car def)))))
                   :key ,(intern-in-package-of-symbol
                          (concatenate 'string (symbol-name (car def))
                                       "-IS-PRIVATE")
                          (car def))))

     ;; And finally just use the name of the function as our return value
     (ACL2::value-triple ',(car def))))
