; A recognizer for world triples
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Recognizes a triple of the form (symb prop . val).
;; TODO: Does something like this already exist?
(defund world-triplep (trip)
  (declare (xargs :guard t))
  (and (consp trip)
       (symbolp (car trip))
       (consp (cdr trip))
       (symbolp (cadr trip))))
