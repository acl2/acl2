; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Documentation for file-io.lisp.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc write-list
  :parents (io)
  :short "Write a list to a file"
  :long "@({
 Example Forms:

 (write-list '(a b c) \"foo\" 'top-level state)
 (write-list '(a b c) \"foo\" 'top-level state :quiet t)

 General Form:

 (write-list list x ctx state &key :quiet val)
 })

 <p>where all arguments are evaluated and @('state') must literally be the ACL2
 @(see state), @('STATE').  @('List') is a true-list; @('x') is a filename or a
 list of length 1 containing a filename; and @('ctx') is a context (see @(see
 ctx)).  By default or if :quiet is nil, a message of the form @('\"Writing
 file [x]\"') is printed to @(see standard-co); otherwise, no such message is
 printed.</p>

 <p>Also see @(see print-object$) and @(see print-object$+).</p>")
