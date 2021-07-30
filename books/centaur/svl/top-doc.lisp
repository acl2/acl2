; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann (this file only)
; License: See "License" in top.lisp

(in-package "ACL2")

(include-book "xdoc/archive-matching-topics" :dir :system)
(local (include-book "top")) ; no_port
(xdoc::archive-matching-topics
 (str::strprefixp "[books]/centaur/svl/" (cdr (assoc :from x))))
