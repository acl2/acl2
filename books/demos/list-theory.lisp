; Written by David Rager with help from Shilpi Goel and Jared Davis.

; Note that much of this information is probably available in book
; "std/util/deflist", but we have this simpler demo for more novice users.

; This book intends to introduce users into the typical lemmas needed when
; reasoning about functions whose arguments are true-listp's, but have some
; special property, like each element is a foo-p, as below.

(in-package "ACL2")

(local (in-theory (disable natp)))

(defn foo-p (e)

; The below call of natp could be anything -- it just depends on what makes up
; your type.

  (natp e))

(defn foo-list-p (lst)
  (cond ((atom lst)
         (null lst))
        (t (and (foo-p (car lst))
                (foo-list-p (cdr lst))))))

(defthm foo-list-p-implies-true-list-p
  (implies (foo-list-p lst)
           (true-listp lst))
  :rule-classes :compound-recognizer)

; We could submit the following three lemmas, which would allow many of our
; subsequent proof obligations to succeed.

;; (defthm foo-list-p-of-cons
;;   (implies (and (foo-list-p lst)
;;                 (foo-p e))
;;            (foo-list-p (cons e lst))))

;; (defthm foo-list-p-cdr-case
;;   (implies (foo-list-p (cons e lst))
;;            (foo-list-p lst)))

;; (defthm foo-list-p-car-case
;;   (implies (foo-list-p (cons e lst))
;;            (foo-p e)))

; However, we instead use an equals rule, which will also allow those
; subsequent proof obligations to succeed.

(defthm foo-list-p-constructors
  (equal (foo-list-p (cons e lst))
         (and (foo-p e)
              (foo-list-p lst))))

(defthmd foo-list-p-and-member-imply-foo-p

; Here is a lemma that _may_ be useful when reasoning about lists using member
; and remove, but we haven't tried it yet.  Thus, we leave it disabled for now.

  (implies (and (member e lst)
                (foo-list-p lst))
           (foo-p e)))

(defthmd foo-list-p-implies-foo-list-p-of-remove

; Here is a lemma that _may_ be useful when reasoning about lists using member
; and delete, but we haven't tried it yet.  Thus, we leave it disabled for now.

  (implies (foo-list-p lst)
           (foo-list-p (remove e lst))))

(in-theory (disable foo-p foo-list-p))
