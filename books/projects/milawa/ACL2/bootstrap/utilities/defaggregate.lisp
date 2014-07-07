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

(in-package "MILAWA")


(defun %make-accessors (name fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons `(%autoadmit ,(accessor-name name (car fields)))
            (%make-accessors name (cdr fields)))
    nil))

(defun %make-accessor-of-constructor (name field)
  (declare (xargs :mode :program))
  `(%autoprove ,(ACL2::mksym (accessor-name name field) '-of- (constructor-name name))
               (%enable default
                        ,(accessor-name name field)
                        ,(constructor-name name))))

(defun %make-accessors-of-constructor-aux (name fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (%make-accessor-of-constructor name (car fields))
            (%make-accessors-of-constructor-aux name (cdr fields)))
    nil))

(defun %make-accessors-of-constructor (name fields)
  (declare (xargs :mode :program))
  (%make-accessors-of-constructor-aux name fields))

(defun %make-requirement-of-recognizer (name require accnames)
  (declare (xargs :mode :program))
  `(%autoprove ,(ACL2::mksym 'forcing- (first require))
               (%enable default
                        ,(recognizer-name name)
                        ,@accnames)))

(defun %make-requirements-of-recognizer-aux (name require accnames)
  (declare (xargs :mode :program))
  (if (consp require)
      (cons (%make-requirement-of-recognizer name (car require) accnames)
            (%make-requirements-of-recognizer-aux name (cdr require) accnames))
    nil))

(defun %make-requirements-of-recognizer (name require fields)
  (declare (xargs :mode :program))
  (%make-requirements-of-recognizer-aux name require (accessor-names name fields)))


(defmacro %defaggregate (name fields &key require)
  ;; BOZO change defaggregate so it stores its name, fields, and requirements
  ;; in a table; then we can change the defaggregate in one place and
  ;; %defaggregate can consult these tables instead of needing to be a whole
  ;; copy of them big form.
  (declare (ACL2::ignorable name fields require))
  (let ((foop (recognizer-name name))
        (make-foo (constructor-name name)))
    (declare (ACL2::ignorable foop make-foo))
    `(encapsulate
      ()
      (%autoadmit ,(recognizer-name name))
      (%autoadmit ,(constructor-name name))

      ,@(%make-accessors name fields)

      (%autoprove ,(ACL2::mksym make-foo '-under-iff)
                  (%enable default ,make-foo))

      (%autoprove ,(ACL2::mksym 'booleanp-of- foop)
                  (%enable default ,foop))

      ,(if (consp require)
           `(%autoprove ,(ACL2::mksym 'forcing- foop '-of- make-foo)
                        (%enable default ,foop ,make-foo))
         `(%autoprove ,(ACL2::mksym foop '-of- make-foo)
                      (%enable default ,foop ,make-foo)))

      ,@(%make-accessors-of-constructor name fields)
      ,@(%make-requirements-of-recognizer name require fields)

      )))
