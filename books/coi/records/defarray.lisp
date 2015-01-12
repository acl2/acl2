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

(include-book "records")
(include-book "../symbol-fns/symbol-fns")

(defmacro defarray (&key (name 'nil) (type 'nil) (size 'nil))

  (declare (ignore size type))

  (let ((name-p   (symbol-fns::suffix name '-p))
	(get-name (symbol-fns::prefix 'get- name))
	(set-name (symbol-fns::prefix 'set- name))
	(new-name (symbol-fns::prefix 'new- name)))

    `(encapsulate
      ()

      (defun ,name-p (x)
	(wfr x))

      (defun ,get-name (a x)
	(g a x))

      (defun ,set-name (a v x)
	(s a v x))

      (defun ,new-name ()
	nil)

      )

    ))

;; Additional vfaat support

(defmacro integer-list-p (x)
  `(integer-listp ,x))

(defun index_list_rec (base off size)
  (if (zp size) nil
    (cons (ifix (+ base off))
	  (index_list_rec base (1+ off) (1- size)))))

(defthm integer-list-p-index_list_rec
  (integer-list-p (index_list_rec base off size))
  :hints (("goal" :in-theory (enable integer-listp))))

(defun index_list (base size)
  (index_list_rec base 0 size))

(defthm integer-list-p-index_list
  (integer-list-p (index_list base size)))

(defun default-integer-list-list () nil)

(defun integer-list-list-p (list)
  (declare (type t list))
  (if (consp list)
      (and (integer-listp (car list))
	   (integer-list-list-p (cdr list)))
    (null list)))

(in-theory (disable index_list))