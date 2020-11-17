; A basic axe-bind-free-evaluator
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

(include-book "axe-syntax-functions-bv")
(include-book "make-axe-bind-free-evaluator")

(make-axe-bind-free-evaluator 'basic '(bind-bv-size-axe
                                       bind-bv-array-length-axe
                                       bind-bv-array-element-size-axe)
                              :enables '(bind-bv-array-length-axe
                                         bind-bv-array-element-size-axe
                                         bind-bv-size-axe))
