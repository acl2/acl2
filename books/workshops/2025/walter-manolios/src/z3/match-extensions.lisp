;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

;; This pattern allows one to match against a symbol by name only, ignoring symbol packages.
;; For example, the pattern (sym-name foo) would match against any symbol X such that (symbol-name 'foo) = (symbol-name X)
(trivia:defpattern sym-name (val)
                   (let ((val-to-match
                          (if (symbolp val) (symbol-name val) val))
                         (it (gensym)))
                     `(trivia:guard1 (,it :type symbol) (symbolp ,it) (symbol-name ,it) ,val-to-match)))


#|
(assert (trivia:match 'cl-user::foo
                      ((sym-name foo) t)
                      ((sym-name "baz") t)
                      (otherwise nil)))

(assert (trivia:match :foo
                      ((sym-name foo) t)
                      ((sym-name "baz") t)
                      (otherwise nil)))

;; note case-sensitivity
(assert (not (trivia:match :baz
                           ((sym-name foo) t)
                           ((sym-name "baz") t)
                           (otherwise nil))))

(assert (trivia:match :|baz|
                      ((sym-name foo) t)
                      ((sym-name "baz") t)
                      (otherwise nil)))

(assert (trivia:match :baz
                      ((sym-name foo) t)
                      ((sym-name "BAZ") t)
                      (otherwise nil)))

;; don't quote the value to match against.
(assert (not (trivia:match :foo
                           ((sym-name 'foo) t)
                           ((sym-name "baz") t)
                           (otherwise nil))))
|#
