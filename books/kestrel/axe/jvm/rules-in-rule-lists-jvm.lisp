; Rules mentioned in rule-lists-jvm.lisp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../rules-in-rule-lists") ;todo: remove some list stuff from this?

(include-book "kestrel/jvm/jvm-facts" :dir :system)
(include-book "kestrel/jvm/jvm-rules" :dir :system)
(include-book "kestrel/jvm/set-classes" :dir :system)
(include-book "kestrel/jvm/do-inst-rules" :dir :system)
(include-book "kestrel/jvm/arrays-2d" :dir :system)
(include-book "kestrel/arrays-2d/arrays-2d" :dir :system)
(include-book "jvm-rules-axe")
(include-book "kestrel/arithmetic-light/mod" :dir :system)

(include-book "rule-lists-jvm")

(ensure-rules-known (first-loop-top-rules))
(ensure-rules-known (phase-1-rules))
