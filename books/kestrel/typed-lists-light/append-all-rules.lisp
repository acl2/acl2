; Rules that mix append-all and other functions
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "append-all")
(include-book "character-list-listp")

(defthm character-listp-of-append-all
  (implies (character-list-listp x)
           (character-listp (append-all x)))
  :hints (("Goal" :in-theory (enable character-list-listp
                                     append-all))))

(defthm character-listp-of-append-all-2
  (implies (true-list-listp x)
           (equal (character-listp (append-all x))
                  (character-list-listp x)))
  :hints (("Goal" :in-theory (enable character-list-listp
                                     append-all))))

;; TODO: Consider this:

;; (defun map-true-list-fix (x)
;;   (if (endp x)
;;       nil
;;     (cons (true-list-fix (first x))
;;           (map-true-list-fix (rest x)))))

;; (defthm character-listp-of-append-all-2
;;   (equal (character-listp (append-all x))
;;          (character-list-listp (map-true-list-fix x)))
;;   :hints (("Goal" :in-theory (enable character-list-listp
;;                                      append-all))))
