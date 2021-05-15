#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "base-theory" :ttags :all)

; I (Pete) went through the built-in functions and added signature
; rules where appropriate. This list is not complete for two
; reasons. First, there are some cases in which we fail due to the
; algorithm not being as general as it can be. See the acl2s-issues
; file. Second, I made one pass through the documentation of
; ACL2-built-ins. I should check again and I should check functions
; defined in the books we load.

(sig append ((listof :a) (listof :a)) => (listof :a))
(sig append ((alistof :a :b) (alistof :a :b)) => (alistof :a :b)
     :suffix alistof)

(sig acl2::rev ((listof :a)) => (listof :a))
(sig acl2::rev ((alistof :a :b)) => (alistof :a :b)
     :suffix alistof)

(sig nth (nat (listof :a)) => :a
     :satisfies (< x1 (len x2)))
; PETE: I added and removed the sig below because it caused the
; theorem prover to get super slow.
;(sig car ((listof :a)) => :a :satisfies (consp x1)) ;new: check
(sig cons (:a (listof :a)) => (listof :a))
(sig acl2::fix-true-list ((listof :a)) => (listof :a))
(sig acl2::fix-true-list ((alistof :a :b)) => (alistof :a :b)
     :suffix alistof)
(sig last ((listof :a)) => (listof :a))
(sig last ((alistof :a :b)) => (alistof :a :b) :suffix alistof)
(sig acl2::repeat (nat :a) => (listof :a)) ;renamed from replicate-fn
(sig make-list-ac (nat :a (listof :a)) => (listof :a))
(sig nthcdr (nat (listof :a)) => (listof :a))
(sig nthcdr (nat (alistof :a :b)) => (alistof :a :b) :suffix alistof)
(sig remove (all (listof :a)) => (listof :a))
(sig remove (all (alistof :a :b)) => (alistof :a :b) :suffix alistof)
(sig remove1-equal (all (listof :a)) => (listof :a))
(sig remove1-equal (all (alistof :a :b)) => (alistof :a :b) :suffix alistof)
(sig remove-duplicates ((listof :a)) => (listof :a))
(sig remove-duplicates ((alistof :a :b)) => (alistof :a :b) :suffix alistof)
(sig cdr ((listof :a)) => (listof :a))
(sig cdr ((alistof :a :b)) => (alistof :a :b) :suffix alistof)
(sig revappend ((listof :a) (listof :a)) => (listof :a))
(sig revappend ((alistof :a :b) (alistof :a :b)) => (alistof :a :b)
     :suffix alistof)
(sig reverse ((listof :a)) => (listof :a))
(sig reverse ((alistof :a :b)) => (alistof :a :b) :suffix alistof)
(sig set-difference$ ((listof :a) (listof :a)) => (listof :a))
(sig set-difference$ ((alistof :a :b) (alistof :a :b)) => (alistof :a :b)
     :suffix alistof)
(sig first-n-ac (nat (listof :a) (listof :a)) => (listof :a)
     :satisfies (< x1 (len x2)))
(sig first-n-ac (nat (alistof :a :b) (alistof :a :b)) => (alistof :a :b)
     :satisfies (< x1 (len x2))
     :suffix alistof)
(local (in-theory (enable take)))
(sig take (nat (listof :a)) => (listof :a)
     :satisfies (<= x1 (len x2))
     :hints (("Goal" :cases ((equal x1 (len x2))))))
(sig take (nat (alistof :a :b)) => (alistof :a :b)
     :satisfies (<= x1 (len x2))
     :suffix alistof
     :hints (("Goal" :cases ((equal x1 (len x2))))))
(local (in-theory (e/d (natp) (take))))
(sig subseq-list ((listof :a) nat nat) => (listof :a)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3)))
(sig subseq-list ((alistof :a :b) nat nat) => (alistof :a :b)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3))
     :suffix alistof)
(sig subseq ((listof :a) nat nat) => (listof :a)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3)))
(sig subseq ((alistof :a :b) nat nat) => (alistof :a :b)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3))
     :suffix alistof)

(sig put-assoc-equal (:a :b (alistof :a :b)) => (alistof :a :b))
(sig pairlis$ ((listof :a) (listof :b)) => (alistof :a :b)
     :satisfies (= (len x1) (len x2)))
(sig update-nth (nat :a (listof :a)) => (listof :a) ;new: check
     :satisfies (<= x1 (len x3)))

;; This is in sorting/sorting.lisp
; (sig evens ((listof :a)) => (listof :a))
; (sig odds ((listof :a)) => (listof :a))
