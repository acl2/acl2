; Standard Basic Library
;
; Copyright (C) 2026 Kestrel Institute (https://www.kestrel.edu)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define yyyjoin (fn rev-args)
  :parents (std/basic)
  :short "Spread a binary function over two or more arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to the builtin @('xxxjoin'),
     but it associates left instead of right,
     and arguments are passed reversed."))
  :mode :program
  (if (cdr (cdr rev-args))
      (list fn (yyyjoin fn (cdr rev-args)) (car rev-args))
    (list fn (second rev-args) (first rev-args))))
