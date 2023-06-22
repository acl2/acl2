; Xdoc for some utilities in this directory
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "gen-xdoc-for-file")

(gen-xdoc-for-file "setenv-dollar-event.lisp"
                   ((setenv$-event "A version of setenv$ that is an event."))
                   (setenv$))
