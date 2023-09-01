; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file type-set-b.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun active-useless-runes (state)
  (let ((useless-runes (f-get-global 'useless-runes state)))
    (let ((my-augmented-disabled-runes                        ;patch;
           (f-get-global 'my-augmented-disabled-runes state)) ;patch;
          (old                                                ;patch;
           (and useless-runes
                (and (eq (access useless-runes useless-runes :tag) 'THEORY)
                     (access useless-runes useless-runes :data)))))
      (if my-augmented-disabled-runes ;patch;

; I was tempted here to use union-augmented-theories-fn1, but it returns an
; unaugmented theory.  The comment there points out that augmented runic
; theories are "descendingly ordered lists of pairs mapping numes to runes".
; So we use merge-car-> to get the new runes into appropriate positions.

          (merge-car-> my-augmented-disabled-runes old) ;patch;
        old))) ;patch;
  )
