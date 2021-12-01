; A lightweight book about the built-in function character-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm character-listp-of-cdr
  (implies (character-listp x)
           (character-listp (cdr x)))
  :hints (("Goal" :in-theory (enable character-listp))))

(defthm character-listp-of-append-2 ;avoid name clash with std?
  (equal (character-listp (append x y))
         (and (character-listp (true-list-fix x))
              (character-listp y)))
  :hints (("Goal" :in-theory (enable character-listp))))

(defthm character-listp-of-revappend
  (equal (character-listp (revappend x y))
         (and (character-listp (true-list-fix x))
              (character-listp y))))

(defthm character-listp-of-reverse
  (implies (true-listp x)
           (equal (character-listp (reverse x))
                  (character-listp x))))

(defthm character-listp-of-true-list-fix
  (implies (character-listp lst)
           (character-listp (true-list-fix lst)))
  :hints (("Goal" :in-theory (enable character-listp))))

(defthm character-listp-of-first-n-ac
  (implies (and (character-listp l)
                (true-listp ac)
                (<= i (len l)))
           (equal (character-listp (first-n-ac i l ac))
                  (character-listp ac)))
  :hints (("Goal" :in-theory (enable character-listp take true-listp))))

(defthm character-listp-of-take
  ;; [Jared] changed for compatibility with std/typed-lists/character-listp.
  (implies (character-listp (double-rewrite x))
           (iff (character-listp (take n x))
                (or (characterp nil) ;; gross
                    (<= (nfix n) (len x))))))

(defthm character-listp-of-nthcdr
  ;; [Jared] changed for compatibility with std/typed-lists/character-listp
  (implies (character-listp (double-rewrite x))
           (character-listp (nthcdr n x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;simpler-take
                            nthcdr character-listp) ()))))

;dup in std/typed-lists/character-listp.lisp
(defthm character-listp-of-cons
  (equal (character-listp (cons a x))
         (and (characterp a)
              (character-listp x)))
  :rule-classes ((:rewrite))
  :hints (("Goal" :in-theory (enable character-listp))))

(defthm character-listp-of-substitute-ac
  (implies (and (characterp new)
                (characterp old)
                (character-listp seq)
                (character-listp acc))
           (character-listp (substitute-ac new old seq acc))))

;; There is a :compound-recognizer rule in std called
;; true-listp-when-character-listp.  There is also a rewrite rule.
(defthmd true-listp-when-character-listp2
  (implies (character-listp x)
           (true-listp x)))
