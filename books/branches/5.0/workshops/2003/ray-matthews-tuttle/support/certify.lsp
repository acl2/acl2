#|

  certify.lisp
  ~~~~~~~~~~~~

The collection of events below provides a proof of our compositional reduction
algorithm in ACL2. The script works in v2-7, but takes an inordinate amount of
time (about 24 hours on a 1.8GHz P3 machine running GCL on top of
linux). Admittedly, the proof is not optimized and the rewrite rules are not
that great, but I am too tired to look at that at this moment.

To see the proof silently go thru, just type (ld "certify.lisp") and that will
work. To see ACL2 work thru the proof, simply comment out the first line of
this file and do the ld.

|#

(set-inhibit-output-lst '(proof-tree prove))

(ubt! 1)

;; This is simply Pete's total order book. I have it in the directory so that I
;; dont have to change the path-names in the different books that call it.

(certify-book "total-order")
(u)

;; We add some other functionality to total-order, including keys etc. to
;; support reasoning about vectors. We use this book here since it has
;; definitions of memberp.

(certify-book "apply-total-order")
(u)

;; This is the records book provide with the distribution of ACL2. This book is
;; terribly important for us, since everything we do is with respect to this book.

(certify-book "records")
(u)

;; We just define a collection of functions for flat sets in ACL2. This book is
;; used in the context of our proof. This is not intended to be a general-purpose
;; book on (even flat) sets.

(certify-book "sets")
(u)

;; This book models the syntax and semantics of LTL. We have managed to define
;; the semantics with respect to eventually periodic paths. Of course, we moved
;; the actual function in concrete-ltl.lisp. Please see the accompanying note
;; for concrete-ltl, and the actual file ltl.lisp, for explanation as to what we
;; did and why.

(certify-book "ltl")
(u)

;; Just a trivial book justifying that conjunctive reduction is sound.

(certify-book "conjunction") 
(u) 

;; This is one hell of a book. It should be cleaned up when I have time, but I
;; have not done that yet. This book proves that bisimilar Kripke Structures
;; have the same ltl-semantics. Notice we needed to define bisimilarity with
;; respect to vars. For explanation, please refer to our paper.

(certify-book "bisimilarity") 
(u) 

;; We define the bisimulation relation for circuit models, which are special
;; types of Kripke Structures built out of our finite state machine
;; representations defined below.

(certify-book "circuit-bisim") 
(u) 

;; In this book, we model circuits or finite state machines. These are
;; efficient representations of Kripke Structures.

(certify-book "circuits") 
(u) 

;; This book verifies the cone of influence reduction implementation in ACL2.

(certify-book "cone-of-influence") 
(u) 

;; This book proves the final theorem about compositional reductions.

(certify-book "reductions") 
(u) 

;; This does not have any technical material at all. But the book allows us to
;; rewrite the ltl-semantics function into a function that we can efficiently
;; execute. In the underlying lisp, we replace calls to this efficient function
;; ltl-semantics-hack by a sys-call calling the external model checker (SMV).

(certify-book "impl-hack" 0 t :defaxioms-okp t) 
(u) 

;; Note: The book concrete-ltl is not used in the rest of the materials any
;; more. The book is present simply as a demonstration that we could actually
;; define the semantics of LTL. The proof of the theorem
;; ltl-ppath-semantics-cannot-distinguish-between-equal-labels used to take a
;; lot of time with v2-6, and considering the relative slowdown between v2-6
;; and v2-7, I did not experiment with that proof on v2-7 using
;; concrete-ltl. The proof has therefore been removed from this book. I do wish
;; to leave the comment here that the proof is not very trivial (actually I
;; also simplified the theorem a lot when I changed from concrete-ltl-semantics
;; to ltl-ppath-semantics which has the property encapsulated.) although very
;; simple at the high level. The proof simply inducts using the induction
;; suggested by concrete-ltl-semantics. However, I still find reasoning about
;; mutually recursive functions difficult in ACL2, and I did not want to
;; clutter the scripts with those theorems. (After all, if an implementation of
;; ltl-ppath-semantics does not satisfy that theorem, then we need to change
;; the definition rather than the theorem...:->)


(certify-book "concrete-ltl")
(u)

(set-inhibit-output-lst '(proof-tree))

