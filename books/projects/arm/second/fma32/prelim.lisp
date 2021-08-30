;; Cuong Chau <cuong.chau@arm.com>

;; July 2021

(in-package "RTL")

(include-book "fma32")
(include-book "projects/arm/utils/rtl-utils" :dir :system)
(include-book "projects/rac/lisp/internal-fns-gen" :dir :system)

;; ======================================================================

;; We impose the following constraints on the inputs of fma32:

(defund input-constraints (a b c d rmode scaleop)
  (and (bvecp a 32)
       (bvecp b 32)
       (bvecp c 32)
       (bvecp d 32)
       (natp rmode)
       (<= rmode 5)
       (bitp scaleop)))

;; Our ultimate objective is the following theorem:

;; (defthm fma32-correct
;;   (implies (input-constraints a b c d rmode scaleop)
;;            (equal (fma32      a b c d rmode scaleop)
;;                   (fma32-spec a b c d rmode scaleop))))

;; In order to address the lack of modularity of the ACL2 code, we take the
;; following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate
  (((a) => *)
   ((b) => *)
   ((c) => *)
   ((d) => *)
   ((rmode) => *)
   ((scaleop) => *))

  (local (defun a () 0))
  (local (defun b () 0))
  (local (defun c () 0))
  (local (defun d () 0))
  (local (defun rmode () 0))
  (local (defun scaleop () 0))

  (defthm input-constraints-lemma
    (input-constraints (a) (b) (c) (d) (rmode) (scaleop))))

(local (in-theory (disable input-constraints-lemma)))

(bvecthm bvecp32-a
  (bvecp (a) 32)
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

(bvecthm bvecp32-b
  (bvecp (b) 32)
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

(bvecthm bvecp32-c
  (bvecp (c) 32)
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

(bvecthm bvecp32-d
  (bvecp (d) 32)
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

(defthm natp-rmode
  (natp (rmode))
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints)))
  :rule-classes :type-prescription)

(defthm rmode-upper-bound
  (<= (rmode) 5)
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints)))
  :rule-classes :linear)

(bitthm bitp-scaleop
  (bitp (scaleop))
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

;; In terms of these constants, we shall define constants corresponding to the
;; local variables of fma32, culminating in the constant (data) corresponding
;; to the output.

;; The constant definitions will be derived from that of fma32 in such a way
;; that the proof of the following will be trivial:

;; (defthm fma32-lemma
;;   (equal (data)
;;          (fma32 (a) (b) (c) (d) (rmode) (scaleop))))

;; The real work will be the proof of the following theorem:

;; (defthm fma32-main
;;   (equal (fma32      (a) (b) (c) (d) (rmode) (scaleop))
;;          (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))

;; The desired theorem can then be derived by functional instantiation.

;; ======================================================================

;; In this book, we'll define the constants and prove the above fma32-lemma
;; using the CONST-FNS-GEN utility.

(make-event
 `,(const-fns-gen 'fma32 'data state
                  :sub-pairs '((c++1 c-scale)
                               (pexp-1 rexp))))

(make-event
 `,(const-fns-gen 'fmul32 'data-mul state
		  :sub-pairs '((pSign rSign)
			       (pExp rExp)
			       (pMant rMant))))

(make-event
 `,(const-fns-gen 'scale128 'data-scale128 state
                  :sub-pairs '((c++1 cadj)
                               (rexp++1 rexpadj)
                               (scale scaleadj)
                               (clz--0 clz-c))
                  :preserved-vars '(c)
                  :excluded-vars '(c--0)))

(make-event
 `,(const-fns-gen 'fadd32 'resrnd state
                  :sub-pairs '((c c-scale)
                               (clz lza)
                               (resmant++2-0 resmant-1))
                  :excluded-vars '(sumexp-0
                                   resexp-1
                                   rndinc++2
                                   resmant++2
                                   resexp++1
                                   resmant++1
                                   rndinc++1
                                   res-1
                                   res-2)))

(defthmd data-=-resrnd
  (equal (data) (resrnd))
  :hints (("Goal" :in-theory (enable data fadd32-lemma))))

(defundd signlarger ()
  (if1 (clarger) (csign) (psign)))

(make-event
 `,(const-fns-gen 'computesum 'data-sum state
                  :sub-pairs '((severe severe-1))
                  :excluded-vars '(gshft-1 pshft-1)))
