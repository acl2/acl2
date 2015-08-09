#|$ACL2s-Preamble$;
; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2's lexicographic-ordering book.~%This indicates that either your ACL2 installation is missing the standard books are they are not properly certified.") (value :invisible))
(include-book "ordinals/lexicographic-ordering" :dir :system)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book
 "ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file :comp)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book
 "custom" :dir :acl2s-modes :uncertified-okp nil :load-compiled-file :comp)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))
; Other events:
(set-well-founded-relation l<)

; Non-events:
(set-guard-checking :none)

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;;Amr HELMY
;; this file is similar to the one in the ACL2 book library the
;; differences are
;; some extra theorems at the end.
;; and the main difference is the change in the permutation function
;; to use member-equal instead of the function in used in the books.
;; But apart from that it is the same as the one in the ACL2 distribution
;; own-perm.lisp
;; 13th March 2008
(begin-book t :TTAGS ((:CCG)));$ACL2s-Preamble$|#

(in-package "ACL2")#|ACL2s-ToDo-Line|#


(defun del (a x)
  (cond ((atom x) nil)
        ((equal a (car x)) (cdr x))
        (t (cons (car x) (del a (cdr x))))))

(defun is-perm (x y)
  (cond ((atom x) (and (equal x y) (atom y)))
        (t (and (member-equal (car x) y)
                (is-perm (cdr x) (del (car x) y))))))

(local (defthm is-perm-reflexive
         (is-perm x x)))

(local
 (encapsulate
  ()

  (local
   (defthm is-perm-del
     (implies (member-equal a y)
              (equal (is-perm (del a y) x)
                     (is-perm y (cons a x))))
     :hints (("Goal" :induct (is-perm y x)))))

  (defthm is-perm-symmetric
    (implies (is-perm x y) (is-perm y x)))))


(defthm member-del-member-normal
  (implies (member-equal x1 (del (car y) z))
           (member-equal x1 z)))


(local (defthm is-perm-implies-same-in
         (implies (and (not (member-equal x1 z))
                       (member-equal x1 y))
                  (not (is-perm y z)))))
(local (defthm del-del
         (equal (del a (del b x))
                (del b (del a x)))))

(defthm member-not-equal-member-equal
  (implies (and (member-equal a z) (not (equal a b)))
           (member-equal a (del b z))))

(local (defthm is-perm-del-del
         (implies (and (member-equal a y)
                       (member-equal a z))
                  (equal (is-perm y z)
                         (is-perm (del a y) (del a z))))))

(local (defthm is-perm-transitive
         (implies (and (is-perm x y) (is-perm y z))
                  (is-perm x z)) ))

(defequiv is-perm)


;;this is the new addition to the file
;; the next theorem proves that if a is not a member of Z then it
;; won't be a member if we remove another member of Z
(defthm not-member-z-not-member-del
  (implies (not (member-equal a z))
           (not (member-equal a (del b z)))))
;; If a is a member of Z and Z contains no duplications
;; then a is not member of (Z-a)
(defthm member-no-duplicatesp-not-member-del
  (implies (and (member-equal a z) (no-duplicatesp-equal z))
           (not (member-equal a (del a z)))))
;; If y has no duplication removing an element from it keeps it
;; without duplications
(defthm no-duplicatesp-delete
  (implies (no-duplicatesp-equal y)
           (no-duplicatesp-equal (del a y))))

;; if x is a permutation of Z, and a is not a member of Z then A is
;; not a member of the tail of X
(defthm not-member-is-perm-no-member
  (implies (and (not (member-equal a z)) (is-perm x z))
           (not (member-equal a (cdr x)))))
;; X is a permutation of Y, No duplications is Y then there is none in
;; X, and the first element of X is not member of its tail, needed of
;; the induction in the next theorem
(defthm is-perm-no-memberp
  (implies (and (is-perm x y) (no-duplicatesp-equal y))
           (not (member-equal (car x) (cdr x))))
  :hints (("Subgoal *1/3.1"
           :use (:instance  not-member-is-perm-no-member
                            (a (car x)) (x (cdr x))  (z  (DEL (CAR X) Y))))))

;;   a list x is a permutation of Y, and no duplication in y
;; then x contains no duplications
(defthm is-perm-no-duplicatesp
  (implies (and (is-perm x y) (no-duplicatesp-equal y))
           (no-duplicatesp-equal x))
  :hints (("subgoal *1/5''"
           :use (:instance is-perm-no-memberp))
          ("subgoal *1/4"
           :use (:instance no-duplicatesp-delete (a (car x))))))




