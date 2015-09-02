; Oracle Timing
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License: (An MIT license):
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

(defvar *oracle-time-stack*
  ;; Holds (elapsed-time . total-alloc) pairs for computations.
  nil)

(defun fudge-heap-bytes-allocated ()
  ;; BOZO copied and pasted in oracle-timelimit-raw.lsp
  #+(or ccl sbcl)
  (heap-bytes-allocated)
  #-(or ccl sbcl) ;; BOZO why doesn't ACL2 do it this way?
  0)

(defmacro oracle-time-exec-raw (ignored-arg1 form)
  (declare (ignorable ignored-arg1))
  (let ((start-time  (gensym))
        (start-alloc (gensym))
        (ans         (gensym))
        (end-time    (gensym))
        (end-alloc   (gensym)))
    `(let ((,start-alloc (fudge-heap-bytes-allocated))
           (,start-time  (get-internal-real-time))
           (,ans         (multiple-value-list ,form))
           (,end-time    (get-internal-real-time))
           (,end-alloc   (fudge-heap-bytes-allocated)))
       ;; Record these times so we can extract them later.
       (push (cons (/ (coerce (- ,end-time ,start-time) 'rational)
                      internal-time-units-per-second)
                   (- ,end-alloc ,start-alloc))
             *oracle-time-stack*)
       ;; Return the answer from the computation.
       (values-list ,ans))))

(defun oracle-time-extract (state)
  (unless (live-state-p state)
    (er hard? 'oracle-time "A live state is required!"))

  (unless (consp *oracle-time-stack*)
    (er hard? 'oracle-time
        "Trying to extract timing info, but the *oracle-time-stack* is empty! ~
         Jared thinks this should never happen."))

  (let ((val (pop *oracle-time-stack*)))

    (unless (and (consp val)
                 (rationalp (car val))
                 (natp (cdr val)))
      (er hard? 'oracle-time
          "*oracle-time-stack* had corrupt value ~x0.  Jared thinks this ~
           should never happen." val))

    (mv (car val) (cdr val) state)))
