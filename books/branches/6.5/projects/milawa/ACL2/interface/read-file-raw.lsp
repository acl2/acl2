; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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

(in-package "CL-USER")

(defmacro report-time (message form)
  `(let* ((start-time (get-internal-real-time))
          (value      ,form)
          (stop-time  (get-internal-real-time))
          (elapsed    (/ (coerce (- stop-time start-time) 'float)
                         internal-time-units-per-second)))
     (format t ";; ~A took ~$ seconds~%" ,message elapsed)
     value))

(defvar *milawa-readtable* (copy-readtable *readtable*))
(declaim (readtable *milawa-readtable*))

(defvar *milawa-abbreviations-hash-table*)
(declaim (type hash-table *milawa-abbreviations-hash-table*))

(defun milawa-sharp-equal-reader (stream subchar arg)
  (declare (ignore subchar))
  (multiple-value-bind
   (value presentp)
   (gethash arg *milawa-abbreviations-hash-table*)
   (declare (ignore value))
   (when presentp
     (error "#~A= is already defined." arg))
   (let ((object (read stream)))
     (setf (gethash arg *milawa-abbreviations-hash-table*) object))))

(defun milawa-sharp-sharp-reader (stream subchar arg)
  (declare (ignore stream subchar))
  (or (gethash arg *milawa-abbreviations-hash-table*)
      (error "#~A# used but not defined." arg)))

(let ((*readtable* *milawa-readtable*))
  (set-dispatch-macro-character #\# #\# #'milawa-sharp-sharp-reader)
  (set-dispatch-macro-character #\# #\= #'milawa-sharp-equal-reader))

(defconstant unique-cons-for-eof (cons 'unique-cons 'for-eof))

(defun milawa-read-file-aux (stream)
   (let ((obj (read stream nil unique-cons-for-eof)))
     (cond ((eq obj unique-cons-for-eof)
            nil)
           (t
            (cons obj (milawa-read-file-aux stream))))))

(defun MILAWA::milawa-read-file (filename)
  (format t ";; Reading from ~A~%" filename)
  (report-time "Reading the file"
    (let* ((*milawa-abbreviations-hash-table* (make-hash-table
                                               :size 10000
                                               :rehash-size 100000
                                               :test 'eql))
           (*readtable* *milawa-readtable*)
           (*package*   (find-package "MILAWA"))
           (stream (open filename
                         :direction :input
                         :if-does-not-exist :error))
           (contents (milawa-read-file-aux stream)))
      (close stream)
      ;; the actual version of this for the proof checker includes
      ;; an acceptable-objectp check, but in this case we don't
      ;; really care.
      contents)))




