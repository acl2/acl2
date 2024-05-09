; FTY Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/alter" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pos-list
  :parents (fty::fty-extensions fty::specific-types pos-listp)
  :short "Fixtype of lists of positive integers."

  ;; We put the DEFLIST in a DEFSECTION,
  ;; surrounded by XDOC::WITHOUT-XDOC,
  ;; to avoid generating a topic for POS-LISTP,
  ;; which would shadow the built-in one.
  ;; But we want a topic for POS-LIST,
  ;; which we create via DEFSECTION.

  (xdoc::without-xdoc
   (fty::deflist pos-list
     :elt-type pos
     :true-listp t
     :elementp-of-nil nil
     :pred pos-listp)))
