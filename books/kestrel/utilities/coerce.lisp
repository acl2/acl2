; A lightweight book about the built-in function coerce
;
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/len" :dir :system))

(defthm consp-of-coerce-of-list
  (equal (consp (coerce x 'list))
         (and (stringp x)
              (not (equal x ""))))
  :hints (("Goal" :use (:instance coerce-inverse-2)
           :cases ((coerce x 'list)))))

(defthm coerce-of-list-iff
  (iff (coerce x 'list)
       (and (stringp x)
            (not (equal x ""))))
  :hints (("Goal" :use (:instance consp-of-coerce-of-list)
           :in-theory (disable consp-of-coerce-of-list))))

(defthm equal-of-len-of-coerce-of-list-and-0
  (equal (equal (len (coerce str 'list)) 0)
         (or (not (stringp str))
             (equal str ""))))

(defthm equal-of-coerce-of-string-when-quotep
  (implies (and (syntaxp (quotep str))
                (character-listp x))
           (equal (equal (coerce x 'string) str)
                  (and (stringp str)
                       ;; the call to coerce here gets computed:
                       (equal x (coerce str 'list))))))

(defthm equal-of-coerce-of-list-when-quotep
  (implies (and (syntaxp (quotep chars))
                (stringp x))
           (equal (equal (coerce x 'list) chars)
                  (and (character-listp chars)
                       ;; the call to coerce here gets computed:
                       (equal x (coerce chars 'string))))))

(defthm equal-of-coerce-and-coerce-string-case
  (implies (and (character-listp x)
                (character-listp y))
           (equal (equal (coerce x 'string)
                         (coerce y 'string))
                  (equal x y)))
  :hints (("Goal" :use ((:instance coerce-inverse-1 (x x))
                        (:instance coerce-inverse-1 (x y)))
           :in-theory (disable coerce-inverse-1))))

(defthm equal-of-coerce-and-coerce-list-case
  (implies (and (stringp x)
                (stringp y))
           (equal (equal (coerce x 'list)
                         (coerce y 'list))
                  (equal x y)))
  :hints (("Goal" :use ((:instance coerce-inverse-2 (x x))
                        (:instance coerce-inverse-2 (x y)))
           :in-theory (disable coerce-inverse-2))))

;improve name?
(defthm coerce-injective
  (implies (and (equal (coerce x 'list) (coerce y 'list))
                (stringp x)
                (stringp y))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable COERCE-INVERSE-2)
           :use ((:instance coerce-inverse-2 (x x))
                 (:instance coerce-inverse-2 (x y))))))

;drop?
(DEFthmd COERCE-INVERSE-1-forced
  (IMPLIES (force (CHARACTER-LISTP X))
           (EQUAL (COERCE (COERCE X 'STRING) 'LIST)
                  X)))
