;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (11th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "datatypes")

(local (in-theory (enable string-or-symbol-p paragraph-p word-p)))

(define translate-variable ((sym symbolp))
  :returns (translated paragraph-p)
  (str::downcase-string (lisp-to-python-names sym)))
