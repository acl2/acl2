; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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


(in-package "ACL2")

;; For when you want the convenience of "nth" without the annoying
;; guard overhead.

(defun ith (n list)
  (declare (type t n list))
  (if (consp list)
      (if (zp (nfix n))
	  (car list)
	(ith (1- n) (cdr list)))
    nil))

(defthm open-ith-not-zp
  (implies
   (not (zp n))
   (equal (ith n list)
	  (ith (1- n) (cdr list)))))

(defthm open-ith-consp
  (implies
   (consp list)
   (equal (ith n list)
	  (if (zp n) (car list)
	    (ith (1- n) (cdr list))))))

(defthm ith-non-increasing
  (<= (acl2-count (ith n list)) (acl2-count list))
  :rule-classes (:linear))

;; If you need other rules about ith, you might want to switch over to nth

(defthmd ith-to-nth
  (equal (ith n list)
	 (nth n list)))