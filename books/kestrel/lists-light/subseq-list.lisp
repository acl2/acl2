; A lightweight book about the built-in function SUBSEQ-LIST
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also subrange.lisp

(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(in-theory (disable subseq-list))

;; Not sure I like the posp in the conclusion
(defthm consp-of-subseq-list
  (equal (consp (subseq-list x start end)) ; x here should be LST, but we match the rule in STD
         (posp (- end start)))
  :hints (("Goal" :in-theory (enable subseq-list))))

(defthm character-listp-of-subseq-list
  (implies (and (character-listp lst)
                (integerp end)
                (natp start))
           (equal (character-listp (subseq-list lst start end))
                  (or (<= end start) ; result will be empty
                      (<= end (len lst)))))
  :hints (("Goal" :in-theory (enable subseq-list))))
