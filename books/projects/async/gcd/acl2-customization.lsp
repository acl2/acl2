;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(ld "package.lsp")
(in-package "ADE")

(defmacro b16 ()
  `(set-print-base-radix 16 state))

(defmacro b10 ()
  `(set-print-base-radix 10 state))

(defmacro b2 ()
  `(set-print-base-radix 2 state))
