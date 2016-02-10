; Standard Utilities Library
; Copyright (C) 2008-2016 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "STD")
(include-book "tools/include-raw" :dir :system)
;; (depends-on "cons-raw.lsp")

(defxdoc cons-with-hint
  :parents (cons)
  :short "Alternative to @(see cons) that tries to avoid consing when a
 suitable @('cons') structure is provided as a hint."

  :long "<p>This is a special purpose function that is intended to help with
 reducing the memory usage of functions that modify existing cons tree
 structures.</p>

 <p>Logically @('(cons x y hint)') is just @('(cons x y)').  That is, the
 @('hint') is completely irrelevant and ignored.  We generally expect that
 @('cons-with-hint') will just be left @(see enable)d, so you should never have
 to reason about it.</p>

 <p>But @('cons-with-hint') has a special raw Common Lisp definition that tries
 to avoid consing by using your @('hint').  In particular, if @('hint') happens
 to already be a cons of the form @('(x . y)'), then we simply return @('hint')
 instead of creating a new cons.  This @('hint') checking is done with @(see
 eql), which makes it a fast but not thorough check.</p>

 <p>What good is this?  A fairly common operation in ACL2 is to ``change'' an
 existing data structure by consing together a new structure that is similar to
 it, but perhaps with some subtrees replaced.  In many cases, some portion of
 the structure does not need to change.</p>

 <p>For instance, consider a function like @(see remove-equal), which updates a
 list by removing all copies of some element from it.  The definition of
 @('remove-equal') is as follows:</p>

 @(def remove-equal)

 <p>You can see that if @('l') doesn't have any copies of @('x'), this function
 will essentially make a fresh copy of the whole list @('x').  That could waste
 a lot of memory when @('x') is long.  It is easy to write a new version of
 @('remove-equal') that uses @('cons-with-hint'):</p>

 @({
     (defun remove-equal-with-hint (x l)
       (declare (xargs :guard (true-listp l)))
       (mbe :logic (remove-equal x l)
            :exec (cond ((endp l) nil)
                        ((equal x (car l))
                         (remove-equal-with-hint x (cdr l)))
                        (t
                         (cons-with-hint (car l)
                                         (remove-equal-with-hint x (cdr l))
                                         l)))))
 })

 <p>This new version avoids consing in the case that we are not dropping an
 element and the @('cdr') has not been changed.  For example, at the time of
 this writing, we found the following memory usages on our copy of CCL:</p>

 @({
      ;; 16 MB of memory allocated
      (let ((list (make-list 1000 :initial-element 0)))
        (time (loop for i from 1 to 1000 do (remove-equal i list))))

      ;; 0 MB of memory allocated
      (let ((list (make-list 1000 :initial-element 0)))
        (time (loop for i from 1 to 1000 do (remove-equal-with-hint i list))))
 })")

(defun cons-with-hint (x y hint)
  (declare (xargs :guard t)
           (ignorable hint))
  (cons x y))

(defttag :cons-with-hint)

(acl2::include-raw "cons-raw.lsp")
