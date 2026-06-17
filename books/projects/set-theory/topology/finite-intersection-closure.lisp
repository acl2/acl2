; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
;   with contributions by Claude Code as noted below
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../base")
(include-book "../finite/base")
(include-book "prelims")
(include-book "../intersection")

(local (defun fic1-induction (f n ss)
         (cond ((zp n) (list f n ss))
               (t (fic1-induction
                   (diff f (singleton (cons (1- n) (apply f (1- n)))))
                   (1- n)
                   (diff ss (singleton (apply f (1- n)))))))))

(local (defthmz diff-n-singleton-n-1-1
         (implies (posp n)
                  (subset (diff n (pair (1- n) (1- n)))
                          (1- n)))
         :hints (("Goal" :in-theory (enable subset)))
         :props (zfc diff$prop)))

(local (defthmz diff-n-singleton-n-1-2
         (implies (posp n)
                  (subset (1- n)
                          (diff n (pair (1- n) (1- n)))))
         :hints (("Goal" :in-theory (enable subset)))
         :props (zfc diff$prop)))

(defthmz diff-n-singleton-n-1
  (implies (posp n)
           (equal (diff n (pair (1- n) (1- n)))
                  (1- n)))
  :hints (("Goal" :in-theory (enable extensionality)))
  :props (zfc diff$prop))

;;; Begin contributions by Claude Code ;;;
;;; Claude Code v2.1.176               ;;;
;;; Fable 5 with max effort            ;;;
; NOTE: All but the final lemma in these contributions by Claude Code have been
; made local to this book.  Some may subsequently be unnecessary due to further
; development of the set theory library.  Some supporting books were tweaked
; slightly after completion of the proof below.

; For the base case of finite-intersection-closure-1: a function with empty
; domain has empty image, so ss is empty and (intersection ss) is 0.

(local
 (defthmz image-when-domain-0
   (implies (and (funp f)
                 (equal (domain f) 0))
            (equal (image f) 0))
   :props (zfc domain$prop prod2$prop inverse$prop)))

; Removing the pair <a,b> from a function preserves membership in the image
; for any member other than b.

(local
 (defthmz in-image-diff-singleton
   (implies (and (in x (image f))
                 (not (equal x b)))
            (in x (image (diff f (pair (cons a b) (cons a b))))))
   :hints (("Goal" :restrict ((in-image-suff
                               ((p (cons (apply (inverse f) x) x)))))))
   :props (zfc domain$prop prod2$prop inverse$prop diff$prop)))

; Discharge the subset hypothesis of the induction hypothesis in
; finite-intersection-closure-1.

(local
 (defthmz subset-diff-image-diff
   (implies (subset ss (image f))
            (subset (diff ss (pair (apply f k) (apply f k)))
                    (image (diff f (pair (cons k (apply f k))
                                         (cons k (apply f k)))))))
   :hints (("Goal" :expand ((subset (diff ss (pair (apply f k) (apply f k)))
                                    (image (diff f
                                                 (pair (cons k (apply f k))
                                                       (cons k (apply f k)))))))))
   :props (zfc domain$prop prod2$prop inverse$prop diff$prop)))

(local
 (defthmz intersection-singleton-1
   (subset (intersection (pair y y)) y)
   :hints (("Goal" :in-theory (enable subset)))
   :props (zfc intersection$prop)))

(local
 (defthmz intersection-singleton-2
   (subset y (intersection (pair y y)))
   :hints (("Goal" :in-theory (enable subset in-all)))
   :props (zfc intersection$prop)))

(local
 (defthmz intersection-singleton
   (equal (intersection (pair y y)) y)
   :hints (("Goal" :in-theory (enable extensionality)))
   :props (zfc intersection$prop)))

(local
 (defthmz in-all-diff
   (implies (in-all x s)
            (in-all x (diff s z)))
   :hints (("Goal" :expand ((in-all x (diff s z)))))
   :props (zfc diff$prop)))

(local
 (defthmz in-all-diff-singleton
   (implies (and (in-all x (diff s (pair y y)))
                 (in x y)
                 (in y s))
            (in-all x s))
   :hints (("Goal"
            :expand ((in-all x s))
            :cases ((equal (in-all-witness x s) y))))
   :props (zfc diff$prop)))

(local
 (defthmz diff-singleton-not-in-1
   (subset (diff s (pair y y)) s)
   :hints (("Goal" :in-theory (enable subset)))
   :props (zfc diff$prop)))

(local
 (defthmz diff-singleton-not-in-2
   (implies (not (in y s))
            (subset s (diff s (pair y y))))
   :hints (("Goal" :in-theory (enable subset)))
   :props (zfc diff$prop)))

(local
 (defthmz diff-singleton-not-in
   (implies (not (in y s))
            (equal (diff s (pair y y)) s))
   :hints (("Goal" :in-theory (enable extensionality)))
   :props (zfc diff$prop)))

; If y is the only element of ss then (intersection ss) is y.

(local
 (defthmz intersection-when-diff-singleton-0
   (implies (and (in y ss)
                 (equal (diff ss (pair y y)) 0))
            (equal (intersection ss) y))
   :hints (("Goal"
            :in-theory (enable equal-diff-0-is-subset)
            :use ((:instance extensionality (x ss) (y (pair y y))))))
   :props (zfc intersection$prop diff$prop)))

; Decompose the intersection of ss as the binary intersection of y \in ss
; with the intersection of the remaining elements of ss.

(local
 (defthmz intersection-int2-decomp-1
   (implies (and (in y ss)
                 (not (equal (diff ss (pair y y)) 0)))
            (subset (intersection ss)
                    (int2 (intersection (diff ss (pair y y))) y)))
   :hints (("Goal" :in-theory (enable subset)))
   :props (zfc intersection$prop diff$prop)))

(local
 (defthmz intersection-int2-decomp-2
   (implies (in y ss)
            (subset (int2 (intersection (diff ss (pair y y))) y)
                    (intersection ss)))
   :hints (("Goal" :in-theory (enable subset)))
   :props (zfc intersection$prop diff$prop)))

(local
 (defthmz intersection-int2-decomp
   (implies (and (in y ss)
                 (not (equal (diff ss (pair y y)) 0)))
            (equal (intersection ss)
                   (int2 (intersection (diff ss (pair y y))) y)))
   :hints (("Goal" :in-theory (enable extensionality)))
   :props (zfc intersection$prop diff$prop)))

; Key step: if the intersection of ss without y is in the topology tp, then
; so is the intersection of ss, whether or not y is in ss.

(local
 (defthmz in-intersection-tp-step
   (implies (and (tpp tp)
                 (subset ss tp)
                 (in (intersection (diff ss (pair y y))) tp))
            (in (intersection ss) tp))
   :hints (("Goal" :cases ((and (in y ss)
                                (equal (diff ss (pair y y)) 0))
                           (and (in y ss)
                                (not (equal (diff ss (pair y y)) 0))))))
   :props (zfc intersection$prop diff$prop)))

;;; End contributions by Claude Code ;;;
; (The following lemma was wrapped with skip-proofs and Claude Code
; automatically generated the missing lemmas below and certified the book.
; Thanks to Eric Smith for generating the query to Claude Code.)

(defthmz finite-intersection-closure-1
  (implies (and (tpp tp)
                (funp f)
                (natp (domain f))
                (subset ss (image f))
                (equal n (domain f))
                (subset ss tp))
           (in (intersection ss) tp))
  :hints (("Goal" :induct (fic1-induction f n ss)))
  :props (zfc intersection$prop prod2$prop domain$prop inverse$prop diff$prop))

(defthmz finite-intersection-closure
  (implies (and (tpp tp)
                (finite ss)
                (subset ss tp))
           (in (intersection ss) tp))
  :hints (("Goal" :in-theory (enable finite)))
  :props (zfc intersection$prop prod2$prop domain$prop inverse$prop diff$prop))
