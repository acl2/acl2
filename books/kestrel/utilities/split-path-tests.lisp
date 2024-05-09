; Tests of split-path.lisp
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "split-path")

;; Simple test
(assert-event
 (mv-let (dir filename)
   (split-path "bar/foo.lisp")
   (and (equal dir "bar")
        (equal filename "foo.lisp"))))

;; Test with no dir
(assert-event
 (mv-let (dir filename)
   (split-path "foo.lisp")
   (and (equal dir ".")
        (equal filename "foo.lisp"))))

;; Test with an absolute path
(assert-event
 (mv-let (dir filename)
   (split-path "/users/smith/foo.lisp")
   (and (equal dir "/users/smith")
        (equal filename "foo.lisp"))))

;; Test with a ..
(assert-event
 (mv-let (dir filename)
   (split-path "../bar/foo.lisp")
   (and (equal dir "../bar")
        (equal filename "foo.lisp"))))

;; Test with multiple dots in the filename
(assert-event
 (mv-let (dir filename)
   (split-path "bar/foo.2.lisp")
   (and (equal dir "bar")
        (equal filename "foo.2.lisp"))))
