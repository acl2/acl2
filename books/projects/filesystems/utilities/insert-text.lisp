(in-package "ACL2")

;  insert-text.lisp                                    Mihir Mehta

(local (include-book "../file-system-lemmas"))

(defund
  insert-text (oldtext start text)
  (declare (xargs :guard (and (character-listp oldtext)
                              (natp start)
                              (stringp text))))
  (let*
      ((start (mbe :exec start :logic (nfix start)))
       (oldtext (mbe :exec oldtext :logic (make-character-list oldtext)))
       (end (+ start (length text))))
    (append (make-character-list (take start oldtext))
            (coerce text 'list)
            (nthcdr end oldtext))))

(defthm insert-text-correctness-1
  (character-listp (insert-text oldtext start text))
  :hints (("goal" :in-theory (enable insert-text))))

(defthm insert-text-correctness-2
  (equal (take (+ start (- start)
                  (len (coerce text 'list)))
               (nthcdr start (insert-text oldtext start text)))
         (coerce text 'list))
  :hints (("goal" :in-theory (enable insert-text)
           :use (:theorem (equal (+ start (- start)
                                    (len (coerce text 'list)))
                                 (len (coerce text 'list)))))))

(defthm
  insert-text-correctness-3
  (<= (+ (nfix start)
         (len (coerce text 'list)))
      (len (insert-text oldtext start text)))
  :hints (("goal" :in-theory (enable insert-text)))
  :rule-classes
  (:linear
   (:linear
    :corollary (implies (natp start)
                        (<= (+ start (len (coerce text 'list)))
                            (len (insert-text oldtext start text)))))))

(defthmd len-of-insert-text
  (implies (stringp text)
           (equal (len (insert-text oldtext start text))
                  (max (+ (nfix start)
                          (len (coerce text 'list)))
                       (len oldtext))))
  :hints (("goal" :do-not-induct t
           :expand (insert-text oldtext start text))))

(encapsulate
  ()

  ;; Borrowed from books/std/lists/append.lisp.
  (local
   (defthm consp-of-append
     (equal (consp (append x y))
            (or (consp x)
                (consp y)))))

  (defthm insert-text-correctness-4
    (implies (stringp text)
             (iff (consp (insert-text oldtext start text))
                  (or (not (zp start))
                      (> (len (coerce text 'list)) 0)
                      (consp oldtext))))
    :hints (("goal" :do-not-induct t
             :use len-of-insert-text
             :in-theory (e/d (insert-text len-when-consp)
                             (len-of-insert-text))))))

(defthm true-listp-of-insert-text
  (implies (true-listp oldtext)
           (true-listp (insert-text oldtext start text)))
  :hints (("goal" :in-theory (enable insert-text)))
  :rule-classes :type-prescription)
