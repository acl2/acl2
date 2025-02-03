;; SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(make-event `(add-include-book-dir :acl2s-modes (:system . "acl2s/")))
(ld "acl2s-mode.lsp" :dir :acl2s-modes)
(acl2s-defaults :set verbosity-level 1)
(set-inhibit-warnings! "Invariant-risk" "theory")
(reset-prehistory t)

(in-package "ACL2S")
;; Some data definitions, for use in examples below.
(defdata student
    (record (name . string)
            (age . nat)
            (grade . nat)))

(defdata lo-student
    (listof student))

(defdata classroom
    (enum '(1 2 3 4 5 6)))

(defdata classroom-assignment
    (alistof classroom lo-student))

:q

(load "try-load-quicklisp.lsp")

(in-package "ACL2S")

(pushnew (truename "../../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :simple-tcp-service/json)

;; Integers are turned into strings, to allow larger integers than
;; JSON libraries typically accept in an interoperable fashion.
(acl2s-json::encode-value 4)

;; Rationals are expressed as a numerator and denominator
(acl2s-json::encode-value (/ 3 4))

;; Symbols are translated into a data structure that also contains
;; package information.
(acl2s-json::encode-value 'a)

;; Strings are translated directly, no wrapping object.
(acl2s-json::encode-value "Hello, World!")

;; Nil is treated as a symbol
(acl2s-json::encode-value nil)

;; Lists are turned into arrays, with each element recursively being
;; encoded
(acl2s-json::encode-value '(1 2 3))

;; Certain kinds of alists are treated specially. In particular, if it
;; is a nonempty list where the first element is a cons and the cdr of
;; that cons is not itself a list, it will be encoded as an alist.
(acl2s-json::encode-value '((1 . "a") (2 . "b") (4 . "d")))

;; Note that conses are encoded as lists in a way that makes them
;; indistinguishable from true lists, e.g. the following two produce
;; the same encoding.
(acl2s-json::encode-value '(1 . "a"))
(acl2s-json::encode-value '(1 "a"))

;; The above alist behavior can be disabled via the
;; *encode-alists-as-plain-lists* setting.
(setf acl2s-json::*encode-alists-as-plain-lists* t)
;; In that case, alists will just be translated into arrays of arrays.
(acl2s-json::encode-value '((1 . "a") (2 . "b") (4 . "d")))

;; Resetting to the default value
(setf acl2s-json::*encode-alists-as-plain-lists* nil)

;; Defdata records are treated specially, and are translated into
;; objects.
(acl2s-json::encode-value (nth-classroom-assignment/acc 2 9))
