; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann (this file only)

;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "ACL2")

(include-book "xdoc/archive-matching-topics" :dir :system)
(local (include-book "top")) ; no_port
(xdoc::archive-matching-topics
 (str::strprefixp "[books]/projects/smtlink/" (cdr (assoc :from x))))
