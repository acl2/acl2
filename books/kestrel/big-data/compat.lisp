; Ensure cherry-picked packages stay in sync with their original versions

; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Brings in, via packages.acl2, various packages that can't easily be brought
;; in by themselves (those packages have been copied into packages.acl2).
;; TODO: Untangle those packages from their contexts so they can be brought in separately.
(include-book "packages")

;; Brings in the original packages, to check that everything is in sync:
(include-book "workshops/2006/cowles-gamboa-euclid/Euclid/ed4db" :dir :system)
(include-book "workshops/2006/cowles-gamboa-euclid/Euclid/prime-fac" :dir :system)
(include-book "projects/paco/utilities" :dir :system)
(include-book "projects/taspi/proofs/sets" :dir :system)
(include-book "workshops/2006/cowles-gamboa-euclid/Euclid/ed5aa" :dir :system)
(include-book "workshops/2006/cowles-gamboa-euclid/Euclid/ed4ba" :dir :system)
(include-book "misc/pigeonhole" :dir :system)
(include-book "workshops/2000/ruiz/multiset/examples/newman/local-confluence" :dir :system)
