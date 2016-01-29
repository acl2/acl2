; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

#+hons
(progn

  (defparameter *count-branches-to-memo-table*
    (hl-mht))

  (defun count-branches-to (x n)
    (labels
        ((count-branches-to1
          (x)
          (let* ((max (* 2 n))
                 (ar (make-array max))
                 (avrc (cons nil nil))
                 (cnt 0))
            (declare (type (simple-array t (*)) ar)
                     (dynamic-extent ar))
            (labels
                ((outer (x)
                        (labels
                            ((fn (x)
                                 (cond
                                  ((atom x) nil)
                                  ((eq (car x) avrc) nil)
                                  ((eq (car x) (cdr x))
                                   (fn (cdr x)))
                                  (t (setf (aref ar cnt) x)
                                     (setf
                                      (aref ar
                                            (the fixnum (+ 1 cnt)))
                                      (car x))
                                     (setq cnt (the fixnum (+ 2 cnt)))
                                     (if (>= cnt max)
                                         (return-from outer nil))
                                     (fn (car x))
                                     (fn (cdr x))
                                     (rplaca (the cons x) avrc)))))
                          (fn x))))
              (unwind-protect
                  (progn
                    (outer x)
                    (values (if (>= cnt max)
                                nil
                              (floor cnt 2))))
                (loop for i fixnum below cnt by 2 do
                      (rplaca (the cons (aref ar i))
                              (aref ar (the fixnum (+ i 1)))))))))
         (lookup
          (x)
          (when (not *count-branches-to-memo-table*)
            (setq *count-branches-to-memo-table* (hl-mht)))
          (b* (((mv ans present)
                (gethash x *count-branches-to-memo-table*)))
            (if present
                (if (car ans)
                    (if (<= (cdr ans) n)
                        (mv (cdr ans) t)
                      (mv nil t))
                  (if (>= (cdr ans) n)
                      (mv nil t)
                    (mv nil nil)))
              (mv nil nil))))
         (descend
          (x)
          (cond ((atom x) x)
                ((eq (car x) (cdr x))
                 (descend (car x)))
                (t x))))
      (b* ((x (hons-copy x))
           ((mv ans ok)
            (lookup x)))
        (if ok
            ans
          (b* ((dx (descend x))
               ((mv ans ok)
                (lookup dx)))
            (if ok
                ans
              (let* ((ans
                      (count-branches-to1 dx))
                     (mem (if ans (cons t ans) (cons nil n))))
                (setf (gethash x *count-branches-to-memo-table*) mem)
                (setf (gethash dx *count-branches-to-memo-table*) mem)
                ans)))))))

  ;; BOZO really profile this?

  (mf-note-arity 'count-branches-to 2 1)

  (profile-fn 'count-branches-to)

  #+Clozure
  ;; Dirty hack so as to clear the count-branches-to memoize table whenever
  ;; clearing the other memoize tables.  BOZO is this something we need to do?
  (setf (gethash 'count-branches-to *memoize-info-ht*)
        (change memoize-info-ht-entry
                (gethash 'count-branches-to *memoize-info-ht*)
                :tablename '*count-branches-to-memo-table*))
  )
