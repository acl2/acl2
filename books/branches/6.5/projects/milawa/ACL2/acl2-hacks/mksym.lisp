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

(in-package "ACL2")

(defun concatenate-symbols (x)
  (declare (xargs :guard (symbol-listp x) :mode :program))
  (if (consp x)
      (concatenate 'string
                   (symbol-name (car x))
                   (concatenate-symbols (cdr x)))
    ""))

(defun has-namespace1 (char-list)
  (declare (xargs :mode :program))
  (if (consp char-list)
      (or (equal (car char-list) #\.)
          (has-namespace1 (cdr char-list)))
    nil))

(defun has-namespace (symbol)
  (declare (xargs :mode :program))
  (has-namespace1 (coerce (symbol-name symbol) 'list)))

(defun extract-namespace1 (char-list)
  (declare (xargs :mode :program))
  (if (consp char-list)
      (if (equal (car char-list) #\.)
          nil
        (cons (car char-list)
              (extract-namespace1 (cdr char-list))))
    nil))

(defun extract-namespace (symbol)
  (declare (xargs :mode :program))
  (let* ((char-list (coerce (symbol-name symbol) 'list))
         (namespace (coerce (extract-namespace1 char-list) 'string)))
    (intern-in-package-of-symbol namespace 'MILAWA::foo)))

(defun extract-nonnamespace1 (char-list)
  (declare (xargs :mode :program))
  (if (consp char-list)
      (if (equal (car char-list) #\.)
          (cdr char-list)
        (extract-nonnamespace1 (cdr char-list)))
    nil))

(defun extract-nonnamespace (symbol)
  (declare (xargs :mode :program))
  (let* ((char-list    (coerce (symbol-name symbol) 'list))
         (nonnamespace (coerce (extract-nonnamespace1 char-list) 'string)))
    (intern-in-package-of-symbol nonnamespace 'MILAWA::foo)))

(defmacro mksym (&rest args)
  `(intern-in-package-of-symbol (concatenate-symbols (list ,@args)) 'MILAWA::foo))