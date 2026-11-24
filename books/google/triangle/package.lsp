;; Copyright 2026 Google LLC
;; Use of this source code is governed by a BSD-style license that can be
;; found in the LICENSE file.

(in-package "ACL2")

;; The following comment line tells the build system that if *acl2-exports*
;; changes, then every book that uses this file should be recertified:
;; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "TRIANGLE"
  (union-eq '(a b c x y z)
            (union-eq *acl2-exports*
                      *common-lisp-symbols-from-main-lisp-package*)))
