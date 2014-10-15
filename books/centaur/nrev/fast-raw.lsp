; NREV - A "safe" implementation of something like nreverse
; Copyright (C) 2014 Centaur Technology
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

(in-package "NREV")

; Basic implementation:
;
;  ACC is NIL == We have the empty list.
;
;  ACC is (CONS HEAD TAIL) otherwise, where:
;
;     HEAD points at the list which has been constructed IN ORDER and hence
;          does not need to be reversed
;
;     TAIL points at its tail, so we can rplacd things in as needed.

(defun nrev$c-copy (nrev$c)
  (let* ((acc  (nrev$c-acc nrev$c))
         (head (car acc)))
    ;; We must make a deep copy of the elements, because otherwise our next
    ;; PUSH would extend a list that someone else has gotten hold of.
    (loop for e in head collect e)))

(defun nrev$c-finish (nrev$c)
  (let* ((acc    (nrev$c-acc nrev$c))
         (head   (car acc))
         (nrev$c (update-nrev$c-acc nil nrev$c)))
    ;; No need to deep copy; nobody else has a handle to our conses.
    (mv head nrev$c)))

(defun nrev$c-push (a nrev$c)
  (let* ((acc      (nrev$c-acc nrev$c))
         (new-cons (cons a nil)))
    (if (atom acc)
        (update-nrev$c-acc (cons new-cons new-cons) nrev$c)
      (let* ((tail (cdr acc)))
        #+hons (acl2::memoize-flush nrev$c)
        (rplacd tail new-cons)
        (rplacd acc new-cons)
        nrev$c))))
