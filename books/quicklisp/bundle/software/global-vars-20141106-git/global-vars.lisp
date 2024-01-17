;;; Copyright (c) 2014 James M. Lawrence
;;; 
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;; 
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;; 
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

(defpackage #:global-vars
  (:export #:define-global-var
           #:define-global-var*
           #:define-global-parameter
           #:define-global-parameter*)
  (:use :cl))

(in-package #:global-vars)

(setf (documentation 'define-global-var 'function)
"Define a global variable with a compile-time value.

Subsequent redefinitions will not change the value (like `defvar').

The `value' argument is evaluated at compile-time. On SBCL, this
permits optimizations based upon the invariant that `name' is always
bound.")

(setf (documentation 'define-global-var* 'function)
"Same as `define-global-var` except `value` is evaluated at load time,
not compile time.")

(setf (documentation 'define-global-parameter 'function)
"Same as `define-global-var` except subsequent redefinitions will
update the value (like `defparameter`).")

(setf (documentation 'define-global-parameter* 'function)
"Same as `define-global-parameter` except `value` is evaluated at load
time, not compile time.")

;;; To ensure that a value form is evaluated only once, we store the
;;; result in the symbol plist of the variable being defined. Another
;;; reason for this is to preserve the toplevelness of essential
;;; forms.

(defmacro store-in-symbol-plist (name value key)
  `(progn
     (eval-when (:compile-toplevel)
       (setf (get ',name ',key) ,value))
     (unless (get ',name ',key)
       (setf (get ',name ',key) ,value))))

(defconstant +value-key+ '.value-key.)

#+sbcl
(progn
  (defmacro define-global-var (&whole whole
                               name value &optional documentation)
    (declare (ignore name value documentation))
    `(sb-ext:defglobal ,@(rest whole)))
  
  (defmacro define-global-var* (&whole whole
                                name value &optional documentation)
    (declare (ignore name value documentation))
    `(sb-ext:define-load-time-global ,@(rest whole)))

  (defmacro define-global-parameter (name value &optional documentation)
    `(progn
       (store-in-symbol-plist ,name ,value ,+value-key+)
       (sb-ext:defglobal ,name (get ',name +value-key+)
         ,@(when documentation (list documentation)))
       (eval-when (:compile-toplevel :load-toplevel :execute)
         (setf ,name (get ',name +value-key+)))
       (remprop ',name +value-key+)
       ',name))

  (defmacro define-global-parameter* (name value &optional documentation)
    `(progn
       (setf (get ',name +value-key+) ,value)
       (sb-ext:define-load-time-global ,name (get ',name +value-key+)
         ,@(when documentation (list documentation)))
       (setf ,name (get ',name +value-key+))
       (remprop ',name +value-key+)
       ',name)))

#+(or ccl lispworks)
(progn
  (defmacro define-global-var* (&whole whole
                                name value &optional documentation)
    (declare (ignore #+lispworks name value documentation))
    ;; defstaticvar doesn't return the var name; likely a ccl bug
    #+ccl `(progn (ccl:defstaticvar ,@(rest whole)) ',name)
    #+lispworks `(hcl:defglobal-variable ,@(rest whole)))

  (defmacro define-global-parameter* (&whole whole
                                      name value &optional documentation)
    (declare (ignore name value documentation))
    #+ccl `(ccl:defstatic ,@(rest whole))
    #+lispworks `(hcl:defglobal-parameter ,@(rest whole)))

  (defmacro define-global-var (&whole whole
                               name value &optional documentation)
    (declare (ignore name value documentation))
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (define-global-var* ,@(rest whole))))

  (defmacro define-global-parameter (name value &optional documentation)
    `(progn
       (store-in-symbol-plist ,name ,value ,+value-key+)
       (eval-when (:compile-toplevel :load-toplevel :execute)
         (define-global-parameter* ,name (get ',name +value-key+)
           ,@(when documentation (list documentation))))
       (remprop ',name +value-key+)
       ',name)))

#-(or sbcl ccl lispworks)
(progn
  (defmacro define-global-parameter* (name value &optional documentation)
    `(progn
       (setf (symbol-value ',name) ,value)
       (define-symbol-macro ,name (symbol-value ',name))
       ,@(when documentation
           `((setf (documentation ',name 'variable) ,documentation)))
       ',name))

  (defmacro define-global-var* (&whole whole
                                  name value &optional documentation)
    (declare (ignore value documentation))
    `(progn
       ;; The symbol macro must be present in any case so compilers
       ;; don't complain about undeclared variable references.
       (define-symbol-macro ,name (symbol-value ',name))
       (unless (boundp ',name)
         (define-global-parameter* ,@(rest whole)))
       ',name))

  (defmacro define-global-parameter (name value &optional documentation)
    `(progn
       (store-in-symbol-plist ,name ,value ,+value-key+)
       (eval-when (:compile-toplevel :load-toplevel :execute)
         (define-global-parameter* ,name (get ',name +value-key+)
           ,@(when documentation (list documentation))))
       (remprop ',name +value-key+)
       ',name))

  (defmacro define-global-var (&whole whole
                                 name value &optional documentation)
    (declare (ignore name value documentation))
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (define-global-var* ,@(rest whole)))))
