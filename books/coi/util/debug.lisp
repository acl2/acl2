(in-package "ACL2")

(include-book "defdoc")

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
(def::doc coi-debug::fail

  :one-liner "A macro to assist in signalling runtime errors"

  :details (docstring
"

  The coi-debug::fail macro allows the user to signal runtime errors
in ACL2 code.  The return value of coi-debug::fail can be set by
specifying a :value parameter.  The failure message can be configured
via the :message keyword.  Additional parameters can be passed in as 
a list via :parameters.

  Typical usage pattern:

  (if (consp x) (car x)
    (coi-debug::fail :value nil
                 :message \"~x0 is not a consp\"
                 :parameters (x)))

  It is sometimes convenient when debugging to induce a common-lisp
break on a failure.  The following code will do just that.

  FOO !> (acl2::progn
           (acl2::defttag t)
           (acl2::progn!
             (acl2::set-raw-mode t)
             (defun coi-debug::fail-fn (value message parameters)
               (acl2::prog2$
                 (acl2::fmt-to-comment-window message parameters 0 nil)
                 (acl2::break)))))

"))
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

(def::doc coi-debug::assert

  :one-liner "A macro to assist in detecting runtime errors"

  :details (docstring
"

  The coi-debug::assert macro allows the user to identify runtime errors
in ACL2 code.  The return value of coi-debug::assert can be set by
specifying a :value parameter.  The failure message can be configured
via the :message keyword.  Note that the first argument (~x0) is the
syntactic form of the test, but that additional parameters can be
passed in as a list via :parameters.

  Example usage pattern:

  (let ((y (coi-debug::assert (test y)
                          :value y
                          :message \"Y failed ~x0 in ~x1\"
                          :parameters (z))))
    ..)

"))

;; -------------------------------------------------------------------

