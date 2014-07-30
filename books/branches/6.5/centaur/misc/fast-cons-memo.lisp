; Centaur Miscellaneous Books
; Copyright (C) 2012 Centaur Technology
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
; fast cons memoization utility -- acl2 book wrapper
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(defttag fast-cons-memo)

;; Warning!  Not compatible with parallelism.

;; Credit/blame to Bob Boyer for showing me this type of optimization.

;; This book provides some utilities to make it slightly less error-prone to do
;; a horrible trick: Say you want to do some computation on a cons tree, and
;; memoize intermediate results for some internal nodes.  You can do this using
;; a hash table, which is relatively safe, or you can use the following trick:
;; Whenever you're ready to store a result, push a record containing the
;; current cons node and its car and cdr onto a recovery stack.  Then, clobber
;; the car and cdr of the node: set the cdr to a particular value recognized as
;; meaning "i'm done here", and the car to the result.  Whenever you descend to
;; a cons node with the special cdr value, just return the car value, since
;; that's its memoized result.  When you finish the computation, restore all
;; the conses by going through the recovery stack and undoing all your
;; destructive operations.

;; Care must be taken to recover correctly if such a function is interrupted.
;; The with-fast-cons-memo macro takes care of this using unwind-protect.

;; Of course, if you have some other thread looking at the same conses that
;; this thread is destructively updating, you'll get into a lot of trouble. :-)

;; (depends-on "fast-cons-memo-raw.lsp")
(include-raw "fast-cons-memo-raw.lsp")
