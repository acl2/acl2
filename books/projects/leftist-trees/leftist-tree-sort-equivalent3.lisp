#|
   Leftist Trees, Version 0.1
   Copyright (C) 2012 by Ben Selfridge <benself@cs.utexas.edu>

   License: (An MIT/X11-style license)

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to
   deal in the Software without restriction, including without limitation the
   rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
   sell copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
   IN THE SOFTWARE.
|#

; (certify-book "sorts-equivalent3")

(in-package "ACL2")

(include-book "sorting/equisort3" :dir :system)
(include-book "sorting/isort" :dir :system)

(include-book "leftist-tree-sort")

(defthm ltree-sort-is-isort
  (implies (true-listp x)
           (equal (ltree-sort x) (isort x)))
  :hints (("Goal" :in-theory (e/d (equisort) (ltree-sort isort)))))

