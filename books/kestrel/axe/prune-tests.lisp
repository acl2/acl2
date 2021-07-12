; Tests of the prune machinery
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

(include-book "prune")
(include-book "kestrel/utilities/assert-with-stobjs" :dir :system)

(assert-equal-with-stobjs2 (prune-term-with-rule-alist '(myif (equal x y) (myif (equal x y) v w) z)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(myif (equal x y) v z)
                           :stobjs (state))

;; TODO: Simplify the (booland 't ...) below
(assert-equal-with-stobjs2 (prune-term-with-rule-alist '(myif (equal x y) (booland (equal x y) z) w)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(myif (equal x y) (booland 't z) w)
                           :stobjs (state))

(assert-equal-with-stobjs2 (prune-term-with-rule-alist '(boolif 't x y)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(bool-fix x)
                           :stobjs (state))

(assert-equal-with-stobjs2 (prune-term-with-rule-alist '(boolif 'nil x y)
                                                       nil
                                                       nil
                                                       nil
                                                       nil
                                                       state)
                           '(bool-fix y)
                           :stobjs (state))

;; todo:
;; (assert-equal-with-stobjs2 (prune-term-with-rule-alist '(boolif '3 x y)
;;                                                        nil
;;                                                        nil
;;                                                        nil
;;                                                        nil
;;                                                        state)
;;                            '(bool-fix x)
;;                            :stobjs (state))
