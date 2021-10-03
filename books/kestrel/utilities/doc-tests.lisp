; Tests of defmacrodoc
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "doc")

(defxdoc-for-macro foo (bar) (myparent) "Short" (bar "the arg") (concatenate 'string "Description " "Description2"))

;; A simple test. We define a macro called FOO and add xdoc to it, including
;; describing its inputs.
(defmacrodoc foo (&whole
                  whole
                  req1
                  req2
                  &key
                  key1 ;todo: is the default nil?
                  (key2 'nil)
                  )
  ;; the body (can be preceded by declares):
  `(foo-fn ,req1 ,req2 ,key1 ,key2 ,whole)
  ;; xdoc args:
  :parents (top)
  :short "Short text goes here."
  ;; TODO: Make an version of :description that puts in the P tags for you:
  ;; This test makes sure that the :description can be computed:
  :description (concatenate 'string
                            "<p>The description of the macro goes here.  This text comes after the General Form and Inputs sections.</p>"
                            "<p>Second paragraph of the description.</p>")
  ;; now an alternating list of param names and strings (or lists of strings):
  :inputs (req1
           "This is the first required param."
           req2
           "Second required param."
           :key1
           "First paragraph of text about key1."
           "Second paragraph of text about key1."
           :key2
           "Blah Blah."))
