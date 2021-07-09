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

(include-book "defdoc")

(include-book "xdoc/top" :dir :system)

(defun map-values-to-fmt-list (values)
  (make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9) values))

;; ===================================================================
;;
;; coi-debug::fail
;;
;; ===================================================================

(defund coi-debug::fail-fn (value message parameters)
  (declare (type t value message parameters))
  (prog2$
   (hard-error 'coi-debug::fail message parameters)
   value))

(defthm coi-debug::fail-fn-value
  (equal (coi-debug::fail-fn value message parameters)
	 value)
  :hints (("Goal" :in-theory (enable coi-debug::fail-fn))))

(defmacro coi-debug::fail (&key (value 'nil)
			    (message '"Failure")
			    (parameters 'nil))
  `(coi-debug::fail-fn ,value ,message ,(map-values-to-fmt-list parameters)))

;; -------------------------------------------------------------------
;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc coi-debug::fail
;
;   :one-liner "A macro to assist in signalling runtime errors"
;
;   :details (docstring
; "
;
;   The coi-debug::fail macro allows the user to signal runtime errors
; in ACL2 code.  The return value of coi-debug::fail can be set by
; specifying a :value parameter.  The failure message can be configured
; via the :message keyword.  Additional parameters can be passed in as
; a list via :parameters.
;
;   Typical usage pattern:
;
;   (if (consp x) (car x)
;     (coi-debug::fail :value nil
;                  :message \"~~x0 is not a consp\"
;                  :parameters (x)))
;
;   It is sometimes convenient when debugging to induce a common-lisp
; break on a failure.  The following code will do just that.
;
;   FOO !> (acl2::progn
;            (acl2::defttag t)
;            (acl2::progn!
;              (acl2::set-raw-mode t)
;              (defun coi-debug::fail-fn (value message parameters)
;                (acl2::prog2$
;                  (acl2::fmt-to-comment-window message parameters 0 nil nil)
;                  (acl2::break)))))
;
; "))

(defxdoc coi-debug::fail
  :parents (acl2::miscellaneous)
  :short "A macro to assist in signalling runtime errors"
  :long "<p>The coi-debug::fail macro allows the user to signal runtime errors
 in ACL2 code.  The return value of coi-debug::fail can be set by specifying
 a :value parameter.  The failure message can be configured via the :message
 keyword.  Additional parameters can be passed in as a list
 via :parameters.</p>

 <p>Typical usage pattern:</p>

 <p>(if (consp x) (car x) (coi-debug::fail :value nil :message \"~x0 is not a
     consp\" :parameters (x)))</p>

 <p>It is sometimes convenient when debugging to induce a common-lisp break on
 a failure.  The following code will do just that.</p>

 <p>FOO !&gt; (acl2::progn (acl2::defttag t) (acl2::progn!  (acl2::set-raw-mode
            t) (defun coi-debug::fail-fn (value message parameters)
            (acl2::prog2$ (acl2::fmt-to-comment-window message parameters 0
            nil nil) (acl2::break)))))</p>")
;; -------------------------------------------------------------------


;; ===================================================================
;;
;; coi-debug::assert
;;
;; ===================================================================

(defun coi-debug::assert-fn (test true false message parms)
  (declare (type t test))
  (if (not test) (coi-debug::fail-fn false message parms)
    true))

(defmacro coi-debug::assert (test &key (value 'nil) (message 'nil) (parameters 'nil))
  (let ((parameters (cons test parameters)))
    (let ((message (or message "Failed Assertion: ~x0")))
      `(coi-debug::assert-fn ,test ,(or value *t*)
			 ,value ,message ,(map-values-to-fmt-list parameters)))))

;; -------------------------------------------------------------------
;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc coi-debug::assert
;
;   :one-liner "A macro to assist in detecting runtime errors"
;
;   :details (docstring
; "
;
;   The coi-debug::assert macro allows the user to identify runtime errors
; in ACL2 code.  The return value of coi-debug::assert can be set by
; specifying a :value parameter.  The failure message can be configured
; via the :message keyword.  Note that the first argument (~~x0) is the
; syntactic form of the test, but that additional parameters can be
; passed in as a list via :parameters.
;
;   Example usage pattern:
;
;   (let ((y (coi-debug::assert (test y)
;                           :value y
;                           :message \"Y failed ~~x0 in ~~x1\"
;                           :parameters (z))))
;     ..)
;
; "))

(defxdoc coi-debug::assert
  :parents (acl2::miscellaneous)
  :short "A macro to assist in detecting runtime errors"
  :long "<p>The coi-debug::assert macro allows the user to identify runtime
 errors in ACL2 code.  The return value of coi-debug::assert can be set by
 specifying a
 :value parameter.  The failure message can be configured via the :message
 keyword.  Note that the first argument (~x0) is the syntactic form of the
 test, but that additional parameters can be passed in as a list via
 :parameters.</p>

 <p>Example usage pattern:</p>

 <p>(let ((y (coi-debug::assert (test y) :value y :message \"Y failed ~x0 in
                           ~x1\" :parameters (z)))) ..)</p>")

;; -------------------------------------------------------------------

