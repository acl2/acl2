; Getting all the world triples for a symbol
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns a list of all the triples in WRLD whose symbol is SYM.
(defund world-triples-for (sym wrld acc)
  (declare (xargs :guard (and (symbolp sym)
                              (plist-worldp wrld)
                              (true-listp acc))))
  (if (endp wrld)
      acc
    (let* ((triple (first wrld)))
      (if (eq (car triple) sym)
          (world-triples-for sym (rest wrld) (cons triple acc))
        (world-triples-for sym (rest wrld) acc)))))
