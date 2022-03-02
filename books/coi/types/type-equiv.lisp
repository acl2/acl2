;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")
(include-book "type-fty")
(include-book "kwargs")

(defun def-type-equiv (type-name type-p type-fix type-equiv guarded equality in-theory reduce-equiv equal-fix-rule-class)
  (let* ((type-p     (default-name type-p     type-name '-p     type-name))
         (type-fix   (default-name type-fix   type-name '-fix   type-p))
         (type-equiv (default-name type-equiv type-name '-equiv type-p))
         (equality   (or equality 'equal))
         (type-equiv-reduction
          (safe-packn-pos (list type-equiv '-reduction) type-p))
         (equal-type-fix-to-type-equiv-rewrite
          (safe-packn-pos (list 'equal- type-fix '-to- type-equiv '-rewrite) type-p))
         (equal-type-fix-to-type-equiv-forward
          (safe-packn-pos (list 'equal- type-fix '-to- type-equiv '-forward) type-p))
         (equiv-of-fix
          (safe-packn-pos (list type-equiv '-of- type-fix) type-p))
         )
    `(encapsulate
         ()
       
       ,@(and in-theory `((in-theory ,in-theory)))
       
       (defun ,type-equiv (x y)
         ,(if guarded `(declare (xargs :guard (and (,type-p x) (,type-p y)))) 
            `(declare (type t x y)))
         ,(if guarded `(mbe :logic (equal (,type-fix x) (,type-fix y))
                            :exec  (,equality x y))
            `(,equality (,type-fix x) (,type-fix y))))
       
       (defthmd ,type-equiv-reduction
         (implies
          (and
           (syntaxp (and (not (equal (car x) ',type-fix))
                         (not (equal (car y) ',type-fix))))
           (and (,type-p x) (,type-p y)))
          (iff (,type-equiv x y)
               (equal x y)))
         :rule-classes ((:rewrite :backchain-limit-lst 1)))
       
       (defequiv ,type-equiv)
       
       (defcong ,type-equiv equal (,type-fix x) 1)
       
       (defthm ,equiv-of-fix
         (,type-equiv (,type-fix x) x))
       
       (local
        (defthm equal-type-implies-type
          (implies
           (and
            (equal x y)
            (or (,type-p x) (,type-p y)))
           (and
            (,type-p y)
            (,type-p x)))))
       
       (defthmd ,equal-type-fix-to-type-equiv-rewrite
         (and (iff (equal (,type-fix x) y)
                   (and (,type-p y)
                        (,type-equiv x y)))
              (iff (equal x (,type-fix y))
                   (and (,type-p x)
                        (,type-equiv x y)))))
       
       (defthmd ,equal-type-fix-to-type-equiv-forward
         (implies
          (equal (,type-fix x) y)
          (,type-equiv x y))
         :rule-classes (:forward-chaining
                        (:forward-chaining
                         :corollary (implies
                                     (equal y (,type-fix x))
                                     (,type-equiv y x)))))
       
       (in-theory (disable ,type-equiv))
       
       (theory-invariant (incompatible (:definition ,type-equiv)
                                       (:rewrite ,equal-type-fix-to-type-equiv-rewrite)))
       
       (in-theory (enable
                   ,@(and reduce-equiv  `(,type-equiv-reduction))
                   ,@(and (member equal-fix-rule-class '(:all :rewrite))
                          `(,equal-type-fix-to-type-equiv-rewrite))
                   ,@(and (member equal-fix-rule-class '(:all :forward-chaining))
                          `(,equal-type-fix-to-type-equiv-forward))
                   ))
       
       )
    ))

(defmacro def::type-equiv (type-name &rest xvlist)
  (b* ((kwargs (kwargs (def-type-equiv-keywords) xvlist))
       ((&key type-p fix equiv guarded equality reduce-equiv equal-fix-rule-class equiv-in-theory) kwargs))
    (def-type-equiv type-name type-p fix equiv guarded equality equiv-in-theory reduce-equiv equal-fix-rule-class)))

(local
 (encapsulate
     ()
   (def::type-equiv natural
     :type-p natp
     :fix  nfix
     :guarded t
     )
   ))

#+joe
(def::type-equiv type-name
  :type-p  type-p
  :fix     type-fix
  :equiv   type-equiv
  :guarded t
  :equality 'equal
  :in-theory nil
  :reduce-equiv t/nil
  :equal-fix-rule-class :all
  )
