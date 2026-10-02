; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "tools/remove-hyps" :dir :system)
(include-book "../base")

(defmacro remove-hypz (form)
  (declare (xargs :guard (and (consp form)
                              (member-eq (car form)
                                         '(thmz defthmz defthmdz)))))
  (let* ((expansion (thmz-fn form))
         (form (case-match expansion
                 (('progn & form) form)
                 (& (er hard 'remove-hypz
                        "Bad expansion: ~x0"
                        expansion)))))
    `(acl2::remove-hyps ,form)))
