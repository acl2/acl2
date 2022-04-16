; Tests of defmacrodoc
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmacrodoc")

(defxdoc-for-macro bar
  (bar &optional o1 &key (key1 'nil) (key2 ':auto))
  (myparent)
  "Short desc"
  ((bar "the arg")
   (o1 "the optional arg")
   (key1 "the first keyword arg")
   (key2 (concatenate 'string "the second" " keyword arg")))
  (concatenate 'string "Description " "Description2"))

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
  ;; This test makes sure that the :description can be computed:
  :description (concatenate 'string
                            "The description of the macro goes here.  This text comes after the General Form and Inputs sections."
                            "Second sentence of the description, showing that the description can be computed.")
  ;; now an alternating list of param names and strings (or lists of strings):
  :args ((req1 "This is the first required param.")
         (req2 "Second required param.")
         (key1 "First paragraph of text about key1."
                "Second paragraph of text about key1.")
         (key2 "Blah Blah.")))

;; Test where the description has multiple forms, each of which is made into a paragraph.
(defmacrodoc foo2 (&whole
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
  :description ("The description of the macro goes here.  This text comes after the General Form and Inputs sections."
                "Second paragraph of the description.")
  ;; now an alternating list of param names and strings (or lists of strings):
  :args ((req1 "This is the first required param.")
         (req2 "Second required param.")
         (key1 "First paragraph of text about key1."
                "Second paragraph of text about key1.")
         (key2 "Blah Blah.")))
