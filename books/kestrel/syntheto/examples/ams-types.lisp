; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


#||
;; Extracted the type declarations from MIDAS/example.ams/spec-v0.lisp
;; as of 2020-09-17

(fty::defprod acid
  ((id pos))
  :pred acidp)

(fty::deftagsum actype
  (:a ())
  (:b ())
  (:c ())
  :pred actypep)

(fty::defprod aircraft
  ((id acid)
   (type actype))
  :pred aircraftp)

(fty::defoption maybe-aircraft
  aircraft
  :pred maybe-aircraftp)

(fty::defset acroster
  :elt-type aircraft
  :elementp-of-nil nil
  :pred acrosterp)

(fty::defprod mission
  ((required actype))
  :pred missionp)

(fty::deflist mission-list
  :elt-type mission
  :true-listp t
  :elementp-of-nil nil
  :pred mission-listp)

(fty::deflist assignment
  :elt-type acid
  :true-listp t
  :elementp-of-nil nil
  :pred assignmentp)

(fty::deftagsum result
  (:solution ((get assignment)))
  (:nosolution ())
  :pred resultp)

||#
