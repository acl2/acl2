; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Stephen Westfold (westfold@kestrel.edu)


(in-package "ACL2")

(include-book "propagate-iso-test-1")
(include-book "std/util/defaggregate" :dir :system)

(std::defaggregate test-int10-pair
  ((name "Symbol" symbolp) 
   (int10-val "Must be int10" int10))
  :tag :test-int10-pair
  :layout :list)

(define inc-int10-val ((pr test-int10-pair-p))
  (change-test-int10-pair pr :int10-val (add-int10 1 (test-int10-pair->int10-val pr))))

;; (apt::lift-iso test-int10-pair-p int10-iso-int20)

(apt::propagate-iso (int10-iso-int20 int10-list-p-iso-int20-list-p)
  ((add-int10 add-int20 add-int10-->add-int20 add-int20-->add-int10
              (int10 int10) => int10))
  :first-event add-int10-comm
  :last-event return-type-of-test-int10-pair->int10-val ;inc-int10-val
  :hints-map ((test-int10-pair-is-iso-test-int20-pair (enable test-int10-pair))
              (honsed-test-int10-pair-is-iso-honsed-test-int20-pair (("Goal")))
              (test-int20-pair->int20-val$inline-is-iso-test-int10-pair->int10-val$inline
                (("Goal" :in-theory (enable int10-to-int20 test-int10-pair->int10-val$inline int20-to-int10 test-int20-pair-p))))))
