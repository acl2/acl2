;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package "ACL2S")
(include-book "tools/include-raw" :dir :system)
(defttag :z3)
(acl2::subsume-ttags-since-defttag)

;; useful for debugging...
;; (set-debugger-enable t)

;; Some stuff has to be include-raw'ed because it uses packages not known to ACL2.
;; (depends-on "z3_raw_code.lsp")
(acl2::include-raw "z3_raw_code.lsp" :host-readtable t)

(acl2::defun-bridge z3-get-solver-stats ()
  :program nil
  :raw (write-to-string (z3-get-solver-stats-fn)))

(acl2::defun-bridge z3-set-solver-from-tactic (name)
  :program nil
  :raw (progn (z3-set-solver (z3-make-solver-from-tactic-name name)) nil))

(acl2::defun-bridge z3-register-tuple-sort-bridge (name fields)
  :program nil
  :raw (progn (z3-register-tuple-sort-fn name fields (z3-default-context)) nil))

(defmacro z3-register-tuple-sort (name fields)
  `(z3-register-tuple-sort-bridge ',name ',fields))

(acl2::defun-bridge z3-register-enum-sort-bridge (name elements)
  :program nil
  :raw (progn (z3-register-enum-sort-fn name elements (z3-default-context)) nil))

(defmacro z3-register-enum-sort (name elements)
  `(z3-register-enum-sort-bridge ',name ',elements))

(acl2::defun-bridge z3-query-bridge (query types)
  :program nil
  :raw
  (progn (z3-solver-init-fn)
         (z3-assert-fn query types)
         (let ((res (z3-check-sat-fn)))
           (if (equal res :sat)
               (z3-get-model-as-assignment-fn)
             res))))

(defmacro z3-query (query types)
  `(z3-query-bridge ',query ',types))

(acl2::defun-bridge z3-init ()
  :program nil
  :raw (progn (z3-solver-init-fn) nil))

(acl2::defun-bridge check-sat ()
  :program nil
  :raw (z3-check-sat-fn))

(acl2::defun-bridge get-model-as-assignment ()
  :program nil
  :raw (z3-get-model-as-assignment-fn))

(acl2::defun-bridge z3-push ()
  :program nil
  :raw (z3-solver-push-fn))

(acl2::defun-bridge z3-pop ()
  :program nil
  :raw (z3-solver-pop-fn))

(acl2::defun-bridge z3-assert-bridge (query types)
  :program nil
  :raw (z3-assert-fn query types))

(defmacro z3-assert (query &optional types)
  `(z3-assert-bridge ',query ',types))
