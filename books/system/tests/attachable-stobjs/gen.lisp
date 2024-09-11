; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See gen-support.lisp for comments.

(in-package "ACL2")

(include-book "gen-support")

(defabsstobj st
  :exports ((lookup :exec mem$ci)
            (update :exec update-mem$ci)
            (misc :exec misc$c+)
            update-misc)
  :attachable t)
