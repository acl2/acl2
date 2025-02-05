; An axe-bind-free-evaluator that knows about the JVM model
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

(include-book "axe-syntax-functions-jvm") ; for get-stack-height-and-pc-to-step-from-myif-nest
(include-book "axe-syntax-functions-jvm2") ; for choose-state-to-step
(include-book "../axe-syntax-functions-bv")
(include-book "../make-axe-bind-free-evaluator")

(make-axe-bind-free-evaluator 'jvm '(bind-bv-size-axe
                                     bind-bv-array-length-axe
                                     bind-bv-array-element-size-axe
                                     get-stack-height-and-pc-to-step-from-myif-nest ;jvm-specific
                                     choose-state-to-step ;jvm-specific
                                     bind-low-zero-count-in-bvcat-nest
                                     )
                              :enables '(bind-bv-array-length-axe
                                         bind-bv-array-element-size-axe
                                         bind-bv-size-axe
                                         get-stack-height-and-pc-to-step-from-myif-nest
                                         choose-state-to-step
                                         symbol-alistp-of-bind-low-zero-count-in-bvcat-nest))
