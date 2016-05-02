; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;(include-book "gacc-with-meta")

(in-package "GACC")

(er hard 'books/gacc/mark.lsp "Jared thinks nobody is using this file.  If he ~
                               is wrong, please send him an email and delete ~
                               this error message.  If nobody sends me such an ~
                               email, I'm just going to delete this.")

(defmacro ac (&rest rst) `(accumulated-persistence ,@(if rst rst `(t))))
(defmacro sac () `(show-accumulated-persistence))

(in-theory (enable (blk)))

(defun atype (m)
  (if (zp m) nil
    `(
      (a 0 0 8 0 nil)
      (b 0 1 8 0 ,(atype (1- m)))
      (c 0 2 8 0 nil)
      (g 0 6 8 0 ,(atype (1- m)))
      (d 0 3 8 0 nil)
;      (e 0 4 8 0 nil)
;      (f 0 5 8 0 nil)
;      (h 0 7 8 0 ,(atype (1- m)))
;      (i 0 8 8 0 ,(atype (1- m)))
;      (j 0 9 8 0 ,(atype (1- m)))
      )))

(defthm unique-blks-atype
  (unique (blks (atype n))))

(defthm uniform-base-atype
  (uniform-base (atype m)))

(defthm weak-skel-atype
  (and (weak-skel (atype m))
       (wf-skel (atype m))))

(defthm open-atype
  (and
   (implies
    (and
     (syntaxp (syntax-atom m))
     (not (zp m)))
    (equal (atype m)
           `(
             (a 0 0 8 0 nil)
             (b 0 1 8 0 ,(atype (1- m)))
             (c 0 2 8 0 nil)
             (g 0 6 8 0 ,(atype (1- m)))
             (d 0 3 8 0 nil)
;             (e 0 4 8 0 nil)
;             (f 0 5 8 0 nil)
;             (h 0 7 8 0 ,(atype (1- m)))
;             (i 0 8 8 0 ,(atype (1- m)))
;             (j 0 9 8 0 ,(atype (1- m)))
             )))
   (implies
    (and
     (syntaxp (syntax-atom m))
     (zp m))
    (equal (atype m) nil))))

(in-theory (disable atype))

(defun a-mark (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((vc (rx 8 (+ 2 ptr) ram)))
        (let ((vc (wfixn 8 1 (1+ vc))))
          (let ((ram (wx 8 (+ 2 ptr) vc ram)))
            (let ((pb (rx 8 (+ 1 ptr) ram)))
              (a-mark (1- n) pb ram))))))))

(defthm open-a-mark
  (and
   (implies
    (and
     (syntaxp (syntax-atom n))
     (not (zp n)))
    (equal (a-mark n ptr ram)
           (if (zerop ptr) ram
             (let ((vc (rx 8 (+ 2 ptr) ram)))
               (let ((vc (wfixn 8 1 (1+ vc))))
                 (let ((ram (wx 8 (+ 2 ptr) vc ram)))
                   (let ((pb (rx 8 (+ 1 ptr) ram)))
                     (a-mark (1- n) pb ram))))))))
   (implies
    (and
     (syntaxp (syntax-atom n))
     (zp n)
     )
    (equal (a-mark n ptr ram) ram)))
  :hints (("goal" :expand (a-mark n ptr ram))))

(in-theory (disable a-mark))
(in-theory (enable (:induction a-mark)))

(defthm a-mark-over-wx
  (let ((askel (g* mptr (atype n) ram)))
    (let ((flat (flatten askel)))
      (implies
       (and
        (disjoint (blk wptr (1+ (max-offset size))) flat)
        (unique flat)
        (integerp n)
        (integerp mptr)
        (integerp wptr)
        )
       (equal (a-mark n mptr (wx size wptr value ram))
              (wx size wptr value (a-mark n mptr ram))))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defthm rx-over-a-mark
  (let ((askel (g* mptr (atype n) ram)))
    (let ((flat (flatten askel)))
      (implies
       (and
        (disjoint (blk rptr (1+ (max-offset size))) flat)
        (unique flat)
        (integerp n)
        (integerp mptr)
        (integerp rptr)
        )
       (equal (rx size rptr (a-mark n mptr ram))
              (rx size rptr ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defthm g*-over-a-mark
  (let ((mskel (g* mptr (atype n) ram))
        (askel (g* rptr rskel ram)))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (syntaxp (not (syntax-consp-or-quote rskel)))
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel rskel)
        (integerp n)
        (integerp mptr)
        (integerp rptr))
       (equal (g* rptr rskel (a-mark n mptr ram))
              (g* rptr rskel ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defthm s*-over-a-mark
  (let ((mskel (g* mptr (atype n) ram))
        (askel wskel))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel wskel)
        (integerp n)
        (integerp mptr))
       (equal (a-mark n mptr (s* wskel ram))
              (s* wskel (a-mark n mptr ram))))))
  :hints (("goal" :induct (s* wskel ram))))

(defthm x*-over-a-mark
  (let ((mskel (g* mptr (atype n) ram))
        (askel rskel))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (syntaxp (not (syntax-consp-or-quote rskel)))
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel rskel)
        (integerp n)
        (integerp mptr))
       (equal (x* rskel (a-mark n mptr ram))
              (x* rskel ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defun a-mark-closed (n ptr ram)
  (a-mark n ptr ram))

#|

(defun updater-exists (expr args fns)
  (declare (type t expr args fns))
  (if (and (consp expr)
           (consp args))
      (or (and (equal (car args) 'ram)
               (consp (car expr))
               (memberp (caar expr) fns))
          (updater-exists (cdr expr) (cdr args) fns))
    nil))


(mutual-recursion

 (defun rx-denormal-list (term spec)
   (declare (type (satisfies eqlable-alistp) spec))
   (if (consp term)
       (or (rx-denormal (car term) spec)
           (rx-denormal-list (cdr term) spec))
     nil))

 (defun rx-denormal (term spec)
   (declare (type (satisfies eqlable-alistp) spec))
   (if (consp term)
       (let ((hit (assoc (car term) spec)))
         (if (and (consp hit)
                  (consp (cdr hit)))
             (let ((args (cadr hit))
                   (fns  (cddr hit)))
               (or (updater-exists term args fns)
                   (rx-denormal-list (cdr term) spec)))
           (rx-denormal-list (cdr term) spec)))
     nil))

 )

(defun spec ()
  `(
    (rx (size ptr ram) . (wx))
    ))


|#


(defthm a-mark-definition
  (let ((askel (g* ptr (atype n) ram)))
    (implies
     (and
      (unique (flatten askel))
      (integerp n)
      (integerp ptr)
      )
     (equal (a-mark n ptr ram)
            (s* (x* askel (a-mark-closed n ptr ram)) ram))))
  :hints (("goal" :induct (a-mark n ptr ram))
          ("Subgoal *1/3" :in-theory (cons 'open-atype (theory 'simplify-uniqueness)))
          ("Subgoal *1/3.2" :in-theory (current-theory :here))
          ("Subgoal *1/3.1" :in-theory (current-theory :here))))

(in-theory (disable a-mark-definition))

(defthm a-mark-use
  (let ((askel (g* ptr (atype n) ram)))
    (let ((ramx (s* askel st2)))
      (implies
       (and
        (unique (flatten askel))
        (integerp n)
        (integerp ptr)
        )
       (equal (x* askel (a-mark-closed n ptr ramx))
              (x* askel (a-mark-closed n ptr ram))
              ))))
  :hints (("goal" :induct (a-mark n ptr ram))
          ("Subgoal *1/3" :in-theory (cons 'open-atype (theory 'simplify-uniqueness)))
          ("Subgoal *1/3.4'" :in-theory (current-theory :here))
          ("Subgoal *1/3.3'" :in-theory (current-theory :here))
          ("Subgoal *1/3.2'" :in-theory (current-theory :here))
          ("Subgoal *1/3.1'" :in-theory (current-theory :here))
          ))

(in-theory (disable a-mark-use))
(in-theory (disable a-mark-closed))

(defthm a-mark-definition-use
  (let ((askel (g* ptr (atype n) ram)))
    (let ((ramx (s* askel st2)))
      (implies
       (and
        (free st2)
        (unique (flatten askel))
        (integerp n)
        (integerp ptr)
        )
       (equal (a-mark n ptr ram)
              (s* (x* askel (a-mark-closed n ptr ramx)) ram)))))
  :hints (("goal" :in-theory (enable a-mark-definition a-mark-use))))


#|

(defun btype (m)
  (if (zp m) nil
    `(
      (a 0 0 8 0 nil)
      (b 0 1 8 0 ,(btype (1- m)))
      (c 0 2 8 0 nil)
      (d 0 3 8 0 ,(btype (1- m)))
      )))

(defthm unique-blks-btype
  (unique (blks (btype n))))

(defthm uniform-base-btype
  (uniform-base (btype m)))

(defthm weak-skel-btype
  (and (weak-skel (btype m))
       (wf-skel (btype m))))

(defthm open-btype
  (implies
   (and
    (integerp m)
    (< 0 m))
   (equal (btype m)
          `(
            (a 0 0 8 0 nil)
            (b 0 1 8 0 ,(btype (1- m)))
            (c 0 2 8 0 nil)
            (d 0 3 8 0 ,(btype (1- m)))
            ))))


(defun b-mark (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((vc (rx 8 (+ ptr 2) ram)))
        (let ((vc (wfixn 8 1 (1+ vc))))
          (let ((ram (wx 8 (+ ptr 2) vc ram)))
            (let ((pb (rx 8 (+ ptr 1) ram)))
              (let ((ram (b-mark (1- n) pb ram)))
      (let ((va (rx 8 ptr ram)))
        (let ((va (wfixn 8 1 (1+ va))))
          (let ((ram (wx 8 ptr va ram)))
            (let ((pd (rx 8 (+ ptr 3) ram)))
              (b-mark (1- n) pd ram)))))))))))))

(defthm open-b-mark
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (b-mark n ptr ram)
           (let ((vc (rx 8 (+ ptr 2) ram)))
        (let ((vc (wfixn 8 1 (1+ vc))))
          (let ((ram (wx 8 (+ ptr 2) vc ram)))
            (let ((pb (rx 8 (+ ptr 1) ram)))
              (let ((ram (b-mark (1- n) pb ram)))
        (let ((va (rx 8 ptr ram)))
          (let ((va (wfixn 8 1 (1+ va))))
            (let ((ram (wx 8 ptr va ram)))
              (let ((pd (rx 8 (+ ptr 3) ram)))
                (b-mark (1- n) pd ram))))))))))))
   (implies
    (zp n)
    (equal (b-mark n ptr ram) ram))
   (implies
    (zerop ptr)
    (equal (b-mark n ptr ram) ram))))

;;
;; Here is where it starts ..
;;

#+joe
(defun-sk forall-rptr (mptr n size ram)
  (forall rptr
          (let ((askel (g* mptr (atype n) ram)))
            (let ((flat (flatten askel)))
              (implies
               (and
                (disjoint (blk rptr (1+ (max-offset size))) flat)
                (unique flat)
                (integerp n)
                (integerp mptr)
                (integerp rptr)
                )
               (equal (rx size rptr (a-mark n mptr ram))
                      (rx size rptr ram)))))))

(defthm rx-over-amark-skolem
  (forall-rptr mptr n size ram))

#+joe
(defthm rx-over-a-mark
  (let ((askel (g* mptr (atype n) ram)))
    (let ((flat (flatten askel)))
      (implies
       (and
        (disjoint (blk rptr (1+ (max-offset size))) flat)
        (memberp rptr (blk mptr (g* mptr (atype n) ram)))
        (unique flat)
        (integerp n)
        (integerp mptr)
        (integerp rptr)
        )
       (equal (rx size rptr (a-mark n mptr ram))
              (rx size rptr ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

#+joe
(defthm b-mark-over-wx
  (let ((mskel (g* mptr (btype n) ram)))
    (let ((mflat (flatten mskel)))
      (implies
       (and
        (disjoint (blk wptr (1+ (max-offset size))) mflat)
        (unique mflat)
        (integerp n)
        (integerp mptr)
        (integerp wptr)
        )
       (equal (b-mark n mptr (wx size wptr value ram))
              (wx size wptr value (b-mark n mptr ram))))))
  :hints (("goal" :induct (b-mark n mptr ram))))

#|

(defun swap-body (ptr ram)
  (let ((vc (rx 8 (+ ptr 2) ram)))
    (let ((vc (wfixn 8 1 (1+ vc))))
      (let ((ram (wx 8 (+ ptr 2) vc ram)))
        (let ((pb (rx 8 (+ ptr 1) ram))
              (pd (rx 8 (+ ptr 3) ram)))
          (let ((ram (wx 8 (+ ptr 1) pd ram)))
            (let ((ram (wx 8 (+ ptr 3) pb ram)))
              ram)))))))

(defun swap (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((ram (swap-body ptr ram)))
        (let ((pb (rx 8 (+ ptr 1) ram))
              (pd (rx 8 (+ ptr 3) ram)))
          (let ((ram (swap (1- n) pb ram)))
            (swap (1- n) pd ram)))))))

(defthm open-swap
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (swap n ptr ram)
           (let ((ram (swap-body ptr ram)))
             (let ((pb (rx 8 (+ ptr 1) ram))
                   (pd (rx 8 (+ ptr 3) ram)))
               (let ((ram (swap (1- n) pb ram)))
                 (swap (1- n) pd ram))))))
   (implies
    (zp n)
    (equal (swap n ptr ram) ram))
   (implies
    (zerop ptr)
    (equal (swap n ptr ram) ram)))
  :hints (("goal" :expand (swap n ptr ram))))



(defthm swap-over-wx
  (let ((mskel (g* mptr (btype n) ram)))
    (let ((mflat (flatten mskel)))
      (implies
       (and
        (disjoint (blk wptr (1+ (max-offset size))) mflat)
        (unique mflat)
        (integerp n)
        (integerp mptr)
        (integerp wptr)
        )
       (equal (swap n mptr (wx size wptr value ram))
              (wx size wptr value (swap n mptr ram))))))
  :hints (("goal" :induct (swap n mptr ram))))

(defthm rx-over-swap
  (let ((mskel (g* mptr (btype n) ram)))
    (let ((mflat (flatten mskel)))
      (implies
       (and
        (disjoint (blk rptr (1+ (max-offset size))) mflat)
        (unique mflat)
        (integerp n)
        (integerp mptr)
        (integerp rptr)
        )
       (equal (rx size rptr (swap n mptr ram))
              (rx size rptr ram)))))
  :hints (("goal" :induct (swap n mptr ram))))

(defthm g*-over-swap
  (let ((mskel (g* mptr (btype n) ram))
        (askel (g* rptr rskel ram)))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel rskel)
        (integerp n)
        (integerp mptr)
        (integerp rptr))
       (equal (g* rptr rskel (swap n mptr ram))
              (g* rptr rskel ram)))))
  :hints (("goal" :induct (swap n mptr ram))))
|#

;; c-mark



(defun c-type (m)
  (if (zp m) nil
    `(
      (a 0 0 8 0 nil)
      (b 0 1 8 0 ,(c-type (1- m)))
      (c 0 2 8 0 ,(c-type (1- m)))
      )))

(defthm unique-blks-c-type
  (unique (blks (c-type n))))

(defthm uniform-base-c-type
  (uniform-base (c-type m)))

(defthm weak-skel-c-type
  (and (weak-skel (c-type m))
       (wf-skel (c-type m))))

(defthm open-c-type
  (implies
   (and
    (integerp m)
    (< 0 m))
   (equal (c-type m)
          `(
            (a 0 0 8 0 nil)
            (b 0 1 8 0 ,(c-type (1- m)))
            (c 0 2 8 0 ,(c-type (1- m)))
            ))))

(defun c-mark (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((ram (wx 8 ptr 0 ram)))
        (let ((pb (rx 8 (+ ptr 1) ram)))
          (let ((ram (c-mark (1- n) pb ram)))
            (let ((pc (rx 8 (+ ptr 2) ram)))
              (let ((ram (c-mark (1- n) pc ram)))
                ram))))))))


(defthm open-c-mark
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (c-mark n ptr ram)
           (let ((ram (wx 8 ptr 0 ram)))
             (let ((pb (rx 8 (+ ptr 1) ram)))
               (let ((ram (c-mark (1- n) pb ram)))
                 (let ((pc (rx 8 (+ ptr 2) ram)))
                   (let ((ram (c-mark (1- n) pc ram)))
                     ram)))))))
   (implies
    (zp n)
    (equal (c-mark n ptr ram) ram))
   (implies
    (zerop ptr)
    (equal (c-mark n ptr ram) ram)))
  :hints (("goal" :expand (c-mark n ptr ram))))



(defun c-mark-body (skel ptr ram)
  (if (consp skel) (c-mark 1 ptr ram)
    ram))

(defthm c-mark-body-props
  (and
   (implies
    (not (consp skel))
    (equal (c-mark-body skel ptr ram) ram))
   (implies
    (consp skel)
    (equal (c-mark-body skel ptr ram) (c-mark 1 ptr ram)))))

(in-theory (disable c-mark-body))

(defun c-mark-rec (n ptr skel ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (if (consp skel)
          (let ((entry (car skel)))
            (let ((indx (caddr entry))       ; index
                  (type (cadddddr entry)))   ; type
              (let ((v (rx 8 (+ ptr indx) ram)))
                (let ((ram (c-mark-body type v ram)))
                  (let ((ram (c-mark-rec (1- n) v type ram)))
                    (c-mark-rec n ptr (cdr skel) ram))))))
        ram))))

(defthm open-c-mark-rec
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (c-mark-rec n ptr skel ram)
           (if (consp skel)
               (let ((entry (car skel)))
                 (let ((indx (caddr entry))       ; index
                       (type (cadddddr entry)))   ; type
                   (let ((v (rx 8 (+ ptr indx) ram)))
                     (let ((ram (c-mark-body type v ram)))
                       (let ((ram (c-mark-rec (1- n) v type ram)))
                         (c-mark-rec n ptr (cdr skel) ram))))))
             ram)))
   (implies
    (zp n)
    (equal (c-mark-rec n ptr skel ram) ram))
   (implies
    (zerop ptr)
    (equal (c-mark-rec n ptr skel ram) ram))))


(defthm c-mark-proof
  (implies
   (integerp ptr)
   (equal (c-mark-rec n ptr (c-type n) ram)
          ))
  :hints (("goal" :induct (c-mark n ptr ram))))

|#
