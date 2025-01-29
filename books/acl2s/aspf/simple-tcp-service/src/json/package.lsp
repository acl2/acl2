;; SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT

#-ACL2 (error "This file must be loaded inside of an ACL2s image.")

(defpackage :acl2s-json
  (:use :cl :trivia)
  (:import-from :acl2 :rationalp)
  (:export #:encode-value #:encode-to-string
           #:decode-from-string #:decode-from-stream
           #:encode-counterexample #:encode-counterexamples))
