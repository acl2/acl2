; Finite Set Theory for ACL2
; Copyright (C) 2000  University of Texas at Austin
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by: J Strother Moore
; email:      Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; The original kernel of this book was created with support from
; Compaq Systems Research Center, Palo Alto, CA.

(in-package "ACL2")

; We define a total ordering on ordinary ACL2 objects composed of
; numbers, characters, strings, symbols, and conses of these things.

; We export
; (ordinaryp x)                       the notion of "ordinary objects"
; (<< x y)                 disabled   the total ordering on such objects

; <<-irreflexivity                    the four obvious theorems about
; <<-trichotomy            disabled   total orders
; <<-mutual-exclusion      disabled
; <<-transitivity          disabled

; We provide ``fast'' versions of the slow rules, named

; fast-<<-trichotomy       enabled
; fast-<<-mutual-exclusion enabled
; fast-<<-transitivity     enabled

; We also provide two theory macros for fiddling with the status of
; these rules.

; Options:
; :in-theory (fast-<<-rules)      ; the default setting above
; :in-theory (fast-<<-rules <<)   ; default plus << enabled
; :in-theory (slow-<<-rules)      ; slow rules enabled but << disabled
; :in-theory (slow-<<-rules <<)   ; slow rules and << enabled

; These macros never enable BOTH the fast and slow rules.  Sometimes
; you need << and sometimes you don't.  The optional << always has the
; same effect whether you're using fast- or slow-<<-rules.  Including
; the << arg ENABLES <<.

(defun ordinaryp (x)
  (cond ((atom x)
         (or (acl2-numberp x)
             (characterp x)
             (stringp x)
             (symbolp x)))
        (t (and (consp x)
                (ordinaryp (car x))
                (ordinaryp (cdr x))))))

; This is used only for admitting the ordering relation.

(defun vcount (x)
  (cond ((atom x)
         (cond ((acl2-numberp x) 0)
               ((characterp x) 0)
               ((stringp x) (+ 1 (length x)))
               ((symbolp x)
                (cond ((equal x nil) 0)
                      (t (+ 3
                            (length (symbol-package-name x))
                            (length (symbol-name x))))))
               (t 0)))
        (t (+ 1 (vcount (car x)) (vcount (cdr x))))))

(local
 (defthm vcount-character-listp
   (implies (character-listp x)
            (equal (vcount x) (len x)))))

; The temptation below is to order all symbols by comparing their
; symbol-package-names and their symbol-names, lexicographically.  But
; how does NIL compare to things?  Since NIL occurs in its
; symbol-package-name, such recursion would not terminate.  So we put
; NIL before all other symbols.

(defun << (x y)
  (declare (xargs :measure (vcount x)))
  (cond
   ((atom x)
    (cond ((atom y)
           (cond ((acl2-numberp x)
                  (cond ((acl2-numberp y) (< x y))
                        (t t)))
                 ((characterp x)
                  (cond ((acl2-numberp y) nil)
                        ((characterp y) (< (char-code x) (char-code y)))
                        (t t)))
                 ((stringp x)
                  (cond ((acl2-numberp y) nil)
                        ((characterp y) nil)
                        ((stringp y)
                         (<< (coerce x 'list)
                             (coerce y 'list)))
                        (t t)))
                 ((symbolp x)
                  (cond ((acl2-numberp y) nil)
                        ((characterp y) nil)
                        ((stringp y) nil)
                        ((symbolp y)
                         (cond ((equal x nil)
                                (cond ((equal y nil) nil)
                                      (t t)))
                               ((equal y nil) nil)
                               (t
                                (or (<< (symbol-package-name x)
                                        (symbol-package-name y))
                                    (and (equal (symbol-package-name x)
                                                (symbol-package-name y))
                                         (<< (symbol-name x)
                                             (symbol-name y)))))))
                        (t t)))
                 (t nil)))
          (t t)))
   ((atom y) nil)
   (t (or (<< (car x) (car y))
          (and (equal (car x) (car y))
               (<< (cdr x) (cdr y)))))))

; Now we prove that << is a total ordering on ACL2 objects.

(defthm <<-irreflexivity
  (not (<< x x)))

(local
 (defthm character-listp-implies-ordinaryp
   (implies (character-listp x)
            (ordinaryp x))))

; The next three were pulled straight out of axioms.lisp, where they
; were proved locally.

(local
 (defthm symbol-equality-rewrite
   (implies (and (symbolp s1)
                 (symbolp s2)
                 (equal (symbol-name s1)
                        (symbol-name s2))
                 (equal (symbol-package-name s1)
                        (symbol-package-name s2)))
            (equal (equal s1 s2) t))
   :hints (("Goal" :use symbol-equality))))

(local
 (defthm equal-coerce
   (implies (and (stringp x)
                 (stringp y))
            (equal (equal (coerce x 'list)
                          (coerce y 'list))
                   (equal x y)))
   :hints (("Goal" :use
            ((:instance coerce-inverse-2 (x x))
             (:instance coerce-inverse-2 (x y)))
            :in-theory (disable coerce-inverse-2)))))

(local
 (defthm equal-char-code-rewrite
   (implies (and (characterp x)
                 (characterp y))
            (implies (equal (char-code x) (char-code y))
                     (equal (equal x y) t)))
   :hints (("Goal" :use equal-char-code))))

(defthm <<-trichotomy
  (implies (and (ordinaryp x)
                (ordinaryp y))
           (or (<< x y)
               (equal x y)
               (<< y x)))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (ordinaryp x)
                           (ordinaryp y)
                           (not (<< x y))
                           (not (equal x y)))
                      (<< y x)))))

(defthm <<-mutual-exclusion
  (implies (<< x y)
           (and (not (equal x y))
                (not (<< y x))))
  :rule-classes
  ((:rewrite :corollary
             (implies (<< x y)
                      (and (not (equal x y))
                           (not (<< y x)))))))

(defthm <<-transitivity
  (implies (and (<< x y) (<< y z)) (<< x z)))

(defthm fast-<<-trichotomy
  (and (implies (and (not (<< xxx y))
                     (equal xxx x)
                     (ordinaryp x)
                     (ordinaryp y)
                     (not (equal x y)))
                (<< y x))
       (implies (and (not (<< x yyy))
                     (equal yyy y)
                     (ordinaryp x)
                     (ordinaryp y)
                     (not (equal x y)))
                (<< y x))))

(defthm fast-<<-mutual-exclusion
  (and (implies (and (<< xxx y)
                     (equal xxx x))
                (and (not (equal x y))
                     (not (<< y x))))
       (implies (and (<< x yyy)
                     (equal yyy y))
                (and (not (equal x y))
                     (not (<< y x))))))

(defthm fast-<<-transitivity
  (implies (and (<< x y)
                (<< yyy z)
                (equal yyy x))
           (<< x z)))

(defmacro fast-<<-rules (&optional <<)

; If << is non-nil, then enable <<, else, don't.

  `(set-difference-theories (enable ,@(if << '((:DEFINITION <<)) nil)
                                    fast-<<-trichotomy
                                    fast-<<-mutual-exclusion
                                    fast-<<-transitivity)
                            '(,@(if << nil '((:DEFINITION <<)))
                              <<-trichotomy
                              <<-mutual-exclusion
                              <<-transitivity)))

(defmacro slow-<<-rules (&optional <<)

; If << is non-nil, then enable <<, else, don't.

  `(set-difference-theories (enable ,@(if << '((:DEFINITION <<)) nil)
                                    <<-trichotomy
                                    <<-mutual-exclusion
                                    <<-transitivity)
                            '(,@(if << nil '((:DEFINITION <<)))
                              fast-<<-trichotomy
                              fast-<<-mutual-exclusion
                              fast-<<-transitivity)))

(in-theory (fast-<<-rules))

