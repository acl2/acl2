; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;  insert-list.lisp                                    Mihir Mehta

(local (include-book "file-system-lemmas"))

(defund
  insert-text (oldtext start text)
  (declare (xargs :guard (and (character-listp oldtext)
                              (natp start)
                              (stringp text))))
  (let*
      ((end (+ start (length text)))
       (newtext (append (make-character-list (take start oldtext))
                        (coerce text 'list)
                        (nthcdr end oldtext))))
    newtext))

(defthm
  insert-text-correctness-1
  (implies (and (character-listp oldtext)
                (natp start)
                (stringp text))
           (character-listp (insert-text oldtext start text)))
  :hints (("goal" :in-theory (enable insert-text))))

(defthm
  insert-text-correctness-2
  (implies
   (and (character-listp oldtext)
        (natp start)
        (stringp text))
   (equal
    (take (+ start (- start)
             (len (coerce text 'list)))
          (nthcdr start (insert-text oldtext start text)))
    (coerce text 'list)))
  :hints (("goal" :in-theory (enable insert-text)
           :use (:theorem (equal (+ start (- start)
                                    (len (coerce text 'list)))
                                 (len (coerce text 'list)))))))

(defthm insert-text-correctness-3
  (implies (and (character-listp oldtext)
                (stringp text)
                (natp start))
           (<= (+ start (len (coerce text 'list)))
               (len (insert-text oldtext start text))))
  :hints (("goal" :in-theory (enable insert-text)))
  :rule-classes :linear)

(defthmd
  len-of-insert-text
  (implies (and (character-listp oldtext)
                (stringp text)
                (natp start))
           (equal (len (insert-text oldtext start text))
                  (max (+ start (len (coerce text 'list)))
                       (len oldtext))))
  :hints (("goal" :do-not-induct t
           :expand (insert-text oldtext start text))))

(defthm
  insert-text-correctness-4
  (implies (and (character-listp oldtext)
                (stringp text)
                (natp start))
           (iff (consp (insert-text oldtext start text))
                (or (> start 0)
                    (> (len (coerce text 'list)) 0)
                    (consp oldtext))))
  :hints
  (("goal" :use len-of-insert-text)
   ("subgoal 4'''" :expand (len (insert-text nil 0 text)))
   ("subgoal 1'4'" :expand (len oldtext))))
