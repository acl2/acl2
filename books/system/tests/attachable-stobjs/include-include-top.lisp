; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book tests attaching an implementation to an attachable stobj when there
; are nested include-book events.

(in-package "ACL2")

(include-book "impl")
(include-book "include-include-mid")

(defun f-top (st)
  (declare (xargs :stobjs st))
  (misc st))

; This easily passes.
(value-triple (f-top st))

; The following two fail if world global ext-gen-barriers is only updated when
; not inside include-book.  That restriction should only be applied to
; declaiming ext-gen-barriers functions notinline in expansion files, not to
; extending ext-gen-barriers.

(value-triple (f-sub st))

(value-triple (f-mid st))
