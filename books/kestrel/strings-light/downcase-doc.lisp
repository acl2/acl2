; Xdoc for downcase utilities
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)

(gen-xdoc-for-file "downcase.lisp"
                   ((char-downcase-gen  "Downcase any character (even a non-standard one).")
                    (chars-downcase-gen  "Downcase any list of characters (even non-standard ones)."))
                   (characters))

(gen-xdoc-for-file "downcase.lisp"
                   ((string-downcase-gen  "Downcase any string (even ones with non-standard characters)."))
                   (strings))
