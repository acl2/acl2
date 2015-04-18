;;;; $Id: package.lisp 660 2011-05-11 13:08:19Z ctian $
;;;; $URL: svn://common-lisp.net/project/usocket/svn/usocket/tags/0.6.1/test/package.lisp $

;;;; See the LICENSE file for licensing information.

(in-package :cl-user)

(defpackage :usocket-test
  (:use :common-lisp
	:usocket
	:regression-test)
  (:export #:do-tests
	   #:run-usocket-tests))
