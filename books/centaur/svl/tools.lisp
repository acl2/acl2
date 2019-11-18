; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")


(encapsulate
  nil
  

  (local
   (defthm lemma1
     (implies (and (consp x)
                   (consp (cdr x)))
              (< (len (evens x))
                 (len x)))))

  (local
   (defthm lemma2
     (implies (and (consp x)
                   )
              (< (len (evens x))
                 (1+ (len x))))))

  (local
   (defthm lemma3
     (IMPLIES (AND (CONSP (CDR L)) (CONSP L))
         (< (LEN (EVENS L)) (+ 1 (LEN (CDR L)))))))
  
  (defun merge-comperator (l1 l2 acc comperator)
    (declare (xargs :guard (and (true-listp l1)
                                (true-listp l2)
                                (true-listp acc)
                                (symbolp comperator ))
                    :measure (+ (len l1) (len l2))))
    (cond
     ((endp l1)
      (revappend acc l2))
     ((endp l2)
      (revappend acc l1))
     ((apply$ comperator (list (car l1) (car l2)))
      (merge-comperator  (cdr l1)
                         l2
                         (cons (car l1) acc)
                         comperator))
     (t (merge-comperator  l1 (cdr l2)
                           (cons (car l2) acc) comperator))))

  (defun merge-comperator-sort (l comperator)
    (declare (xargs :guard (and (true-listp l)
                                (symbolp comperator))
                    :measure (len l)
                    :verify-guards nil))
    (cond ((endp (cdr l)) l)
          (t (merge-comperator
              (merge-comperator-sort (evens l) comperator)
              (merge-comperator-sort (odds l) comperator)
              nil
              comperator))))

  (defthm true-listp-of-merge-comprerator
    (implies (and (true-listp l1)
                  (true-listp l2)
                  (true-listp acc))
             (true-listp (merge-comperator l1 l2 acc comperator))))
  
  (defthm true-listp-of-merge-sort
    (implies (true-listp l)
             (true-listp (merge-comperator-sort l comperator))))

  (verify-guards merge-comperator-sort))



