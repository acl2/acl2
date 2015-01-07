#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "defdata/top" :ttags :all)
(include-book "cgen/top" :ttags :all)
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

; I (Pete) went through the built-in functions and added
; signature rules where appropriate. This list is not complete
; for two reasons. First, there are some cases in which we fail
; due to the algorithm not being as general as it can be. See the
; acl2s-issues file. Second, I made one pass through the
; documentation of ACL2-built-ins. I should check again and I
; should check functions defined in the books we load 

(sig append ((listof :a) (listof :a)) => (listof :a))
(sig acl2::rev ((listof :a)) => (listof :a))
(sig nth (nat (listof :a)) => :a 
     :satisfies (< x1 (len x2)))
(sig acl2::fix-true-list ((listof :a)) => (listof :a))
(sig last ((listof :a)) => (listof :a))
(sig acl2::repeat (nat :a) => (listof :a)) ;renamed from replicate-fn
(sig make-list-ac (nat :a (listof :a)) => (listof :a))
(sig nthcdr (nat (listof :a)) => (listof :a))
(sig remove (all (listof :a)) => (listof :a))
(sig remove1-equal (all (listof :a)) => (listof :a))
(sig remove-duplicates ((listof :a)) => (listof :a))
(sig cdr ((listof :a)) => (listof :a))
(sig revappend ((listof :a) (listof :a)) => (listof :a))
(sig reverse ((listof :a)) => (listof :a))
(sig set-difference$ ((listof :a) (listof :a)) => (listof :a))
(sig first-n-ac (nat (listof :a) (listof :a)) => (listof :a)
     :satisfies (< x1 (len x2)))
(sig take (nat (listof :a)) => (listof :a)
     :satisfies (<= x1 (len x2))
     :hints (("Goal" :cases ((equal x1 (len x2))))))
(sig subseq-list ((listof :a) nat nat) => (listof :a)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3)))
(sig subseq ((listof :a) nat nat) => (listof :a)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3)))

(sig put-assoc-equal (:a :b (alistof :a :b)) => (alistof :a :b))

(include-book "arithmetic-5/top" :dir :system)

