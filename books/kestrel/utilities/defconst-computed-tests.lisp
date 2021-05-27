; Tests of defconst-computed
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

(include-book "defconst-computed")
(include-book "std/testing/must-be-redundant" :dir :system)

;; a stobj other than state:
(defstobj result-array-stobj
  (thearray :type (array t (10)) :resizable t)
  ;(default-array-value :type t :initially nil)
  )

;;;
;;; tests of defconst-computed-simple
;;;

;; Test that the form given can mention stobjs:
(defconst-computed-simple *thearray-length* (thearray-length result-array-stobj))
;; expected result:
(must-be-redundant (defconst *thearray-length* '10))

;; Test that the form given can mention state:
(defconst-computed-simple *world-length* (len (w state)))

;; Test that the form given can mention state and another stobj:
(defconst-computed-simple *thearray-length-and-world-length*
  (list (thearray-length result-array-stobj)
        (len (w state))))
(thm (equal (len *thearray-length-and-world-length*) 2))

;;;
;;; tests of defconst-computed
;;;

;; The FORM mentions STATE and returns a value and state:
(defconst-computed *two* (mv '2 state))

;; The FORM can mention other stobjs (but still must return just a value and state):
(defconst-computed *foo* (mv (list (thearray-length result-array-stobj) (len (w state)))
                             state))

;;;
;;; tests of defconst-computed3
;;;

(defconst-computed3 *world-length2* (mv nil (len (w state)) state))

;;;
;;; tests of defconst-computed-erp-and-val
;;;

(defconst-computed-erp-and-val *world-length3* (mv nil (len (w state))))
