; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "deftutorial")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftutorial my-tutorial "My tutorial")

(def-my-tutorial-top
  (parent1 parent2)
  (xdoc::p "one")
  (xdoc::p "two"))

(def-my-tutorial-page first
  "The first thing."
  (xdoc::p "A")
  (xdoc::p "B")
  (xdoc::p "C"))

(def-my-tutorial-page second
  "The second thing."
  (xdoc::p "para1")
  (xdoc::p "para2")
  (xdoc::p "para3"))

(def-my-tutorial-page third
  "The third thing."
  (xdoc::p "text"))

(def-my-tutorial-topics)
