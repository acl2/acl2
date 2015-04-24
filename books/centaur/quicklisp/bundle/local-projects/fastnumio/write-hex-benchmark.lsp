; Fastnumio - Efficient hex string I/O ops for Common Lisp streams
; Copyright (C) 2015 Centaur Technology
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

(ql:quickload :fastnumio)
(ql:quickload :trivial-garbage)
(in-package "FASTNUMIO")

(defun get-bytes ()
  #+ccl
  (ccl::total-bytes-allocated)
  #+sbcl
  (sb-ext::get-bytes-consed)
  #+(and (not sbcl) (not ccl))
  0)

;; write-hex performance testing

(defun test-builtin (ntimes nums stream)
  (declare (type fixnum ntimes))
  (format t "Testing FORMAT.~%")
  (loop for i fixnum from 1 to ntimes do
        (loop for num in nums do
              (format stream "~x" num))))

(defun test-safe (ntimes nums stream)
  (declare (type fixnum ntimes))
  (format t "Testing WRITE-HEX.~%")
  (loop for i fixnum from 1 to ntimes do
        (loop for num in nums do
              (write-hex num stream))))

(defun test-unsafe (ntimes nums stream)
  (declare (type fixnum ntimes))
  (format t "Testing SCARY-UNSAFE-WRITE-HEX.~%")
  (loop for i fixnum from 1 to ntimes do
        (loop for num in nums do
              (scary-unsafe-write-hex num stream))))

(defun gc ()
  (tg::gc :full t :verbose nil))

(defmacro my-time (form)
  ;; Returns (cons seconds bytes)
  `(let ((start-bytes (get-bytes))
         (start-time  (get-internal-real-time))
         (blah        (time ,form))
         (end-time    (get-internal-real-time))
         (end-bytes   (get-bytes)))
     (declare (ignore blah))
     (cons (/ (coerce (- end-time start-time) 'float)
              internal-time-units-per-second)
           (- end-bytes start-bytes))))

(defun nice-bytes (x)
  (cond ((< x (expt 2 10))
         (format nil "~5DB" x))
        ((< x (expt 2 20))
         (format nil "~5,1FK" (/ (coerce x 'float) (expt 2 10))))
        ((< x (expt 2 30))
         (format nil "~5,1FM" (/ (coerce x 'float) (expt 2 20))))
        (t
         (format nil "~5,1FG" (/ (coerce x 'float) (expt 2 30))))))

(defparameter *times*
  (loop for x in '((32  . 1000000) ;; 2^N . NTIMES
                   (60  . 1000000)
                   (64  . 800000)
                   (80  . 600000)
                   (128 . 500000)
                   (256 . 300000)
                   (512 . 150000))
        collect
        (let* ((n      (car x))
               (ntimes (cdr x))
               (limit  (expt 2 n))
               (nums   (loop for i from 1 to 10 collect (random limit))))
          (format t "~%  --- Testing hex writing of numbers up to 2^~d --- ~%" n)
          (with-open-file (stream "/dev/null"
                                  :direction :output
                                  :if-exists :append)
            (let* ((unsafe-time  (progn (gc) (my-time (test-unsafe ntimes nums stream))))
                   (safe-time  (progn (gc) (my-time (test-safe ntimes nums stream))))
                   (fmt-time (progn (gc) (my-time (test-builtin ntimes nums stream)))))
              (list n fmt-time safe-time unsafe-time))))))



(progn
  (format t "~%")
  (format t "         N         FMT       SAFE/Speedup     UNSAFE/Speedup~%")
  (format t "---------------------------------------------------------------~%~%")
  (loop for elem in *times* do
        ;; Times
        (let* ((n        (first elem))
               (fmt      (car (second elem)))
               (safe     (car (third elem)))
               (unsafe   (car (fourth elem)))
               (sspeedup (if (< fmt safe)   (- (/ safe fmt))   (/ fmt safe)))
               (uspeedup (if (< fmt unsafe) (- (/ unsafe fmt)) (/ fmt unsafe))))
          (format t "~10D  ~10,2Fs ~10,2Fs/~3,2Fx ~10,2Fs/~3,2Fx~%"
                  n fmt safe sspeedup unsafe uspeedup))
        ;; Bytes
        (let* ((builtin  (cdr (second elem)))
               (safe     (cdr (third elem)))
               (unsafe   (cdr (fourth elem)))
               (sspeedup (if (eql builtin 0)
                             "???"
                           (* 100 (/ (coerce safe 'float) builtin))))
               (uspeedup (if (eql builtin 0)
                             "???"
                           (* 100 (/ (coerce unsafe 'float) builtin)))))
          (format t "~10a       ~7a    ~7a ~3,1F%      ~7a ~3,1F%~%"
                  ""
                  (nice-bytes builtin)
                  (nice-bytes safe) sspeedup
                  (nice-bytes unsafe) uspeedup))
        (format t "~%"))
  (format t "----------------------------------------------------------------~%")
  (format t "~%"))



