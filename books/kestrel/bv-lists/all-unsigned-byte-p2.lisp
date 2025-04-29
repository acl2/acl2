; More theorems about all-unsigned-byte-p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book mixes all-unsigned-byte-p with other non-buit-in functions

(include-book "all-unsigned-byte-p")
(include-book "bvchop-list")
(include-book "../lists-light/repeat")
(include-book "../lists-light/reverse-list-def")
(include-book "../lists-light/subrange-def")
(include-book "../lists-light/update-subrange")
(include-book "../lists-light/update-subrange2")
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(local (include-book "../lists-light/subrange"))
(local (include-book "../lists-light/len"))
(local (include-book "../lists-light/take"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(defthm all-unsigned-byte-p-of-repeat
  (equal (all-unsigned-byte-p width (repeat n x))
         (or (zp n)
             (unsigned-byte-p width x)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p repeat))))

(defthm all-unsigned-byte-p-of-reverse-list
  (equal (all-unsigned-byte-p width (reverse-list x))
         (all-unsigned-byte-p width x))
  :hints (("Goal" :in-theory (enable reverse-list all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-of-firstn
  (implies (all-unsigned-byte-p size lst)
           (all-unsigned-byte-p size (firstn n lst)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p firstn))))

;move?
(defthm all-unsigned-byte-p-of-subrange
  (implies (and (all-unsigned-byte-p size x)
                (integerp start)
                (integerp end))
           (equal (all-unsigned-byte-p size (subrange start end x))
                  (or (< (nfix end) start)
                      (< end (len x)))))
  :hints (("Goal" :in-theory (enable subrange))))

;this may help get rid of the values of x, which may be large terms!
;todo: where does the take come from?
;todo: is this too special-purpose?  it may be useful just for efficiency..
(defthm all-unsigned-byte-p-of-take-of-subrange
  (implies (and (all-unsigned-byte-p width x)
                (natp width)
                (natp start)
                (natp end)
                (natp i)
                )
           (equal (all-unsigned-byte-p width (take i (subrange start end x)))
                  (if (< (+ 1 (- end start)) i)
                      (and (< end start)
                           (equal i 0))
                    (or (equal i 0)
                        (< (+ start i -1) (len x)))))))

;; ;this may help get rid of irrelevant values in x...
;; ;or is it gross to introduce repeat?
;; ;fffixme can this loop?!
;; (defthmd all-unsigned-byte-p-of-take-of-subrange
;;   (implies (and (all-unsigned-byte-p width x)
;;                 (natp width)
;;                 (natp start)
;;                 (natp end)
;;                 (natp i)
;;                 )
;;            (equal (all-unsigned-byte-p width (take i (subrange start end x)))
;;                   (all-unsigned-byte-p width (take i (subrange start end (repeat (len x) 0))))))
;;   :hints (("Goal" :cases ((< (+ 1 (- end start)) i)))))


(defthm all-unsigned-byte-p-of-update-subrange
  (implies (and (all-unsigned-byte-p size lst)
                (all-unsigned-byte-p size vals)
                (integerp start) (natp start)
                (integerp end)
                (natp size)
                (true-listp lst) ;drop?
                (<= start (len lst))
                (<= (+ end 1 (- start)) (len vals)))
           (all-unsigned-byte-p size (update-subrange start end vals lst)))
  :hints (("Goal" ;:cases ((equal -1 end))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (update-subrange natp update-nth-of-update-subrange-diff-back)
                           (update-nth-of-update-subrange-diff)))))

;move
;gen?
(defthm all-unsigned-byte-p-of-update-subrange2
  (implies (and (all-unsigned-byte-p size lst)
                (all-unsigned-byte-p size vals)
                (natp start) ;gen?
                (integerp end) ;(natp end) ;gen?
                (<= (+ end 1 (- start)) (len vals)) ;what if len causes not all vals to be used?
                (<= len (len lst)) ;gen?
                (true-listp lst)
                (natp size))
           (all-unsigned-byte-p size (update-subrange2 len start end vals lst)))
  :hints (("Goal" :cases ((<= start len))
           :in-theory (enable natp))))

(defthm all-unsigned-byte-p-of-bvchop-list-gen2
  (implies (and ;(<= element-size size)
            (all-unsigned-byte-p size lst)
            (natp size)
            (natp element-size))
           (all-unsigned-byte-p size (bvchop-list element-size lst)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p bvchop-list))))

;used in some examples
(defthmd all-unsigned-byte-p-of-myif-strong
  (equal (all-unsigned-byte-p n (myif test a b))
         (myif test (all-unsigned-byte-p n a)
               (all-unsigned-byte-p n b)))
  :hints (("Goal" :in-theory (enable myif))))
