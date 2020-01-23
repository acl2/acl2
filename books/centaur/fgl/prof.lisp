; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/misc/u32-listp" :dir :system)
(include-book "defsort/defsort" :dir :system)
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

(fty::defalist nat-nat-alist :key-type natp :val-type natp :true-listp t)

(defstobj interp-profiler
  (prof-enabledp :type (satisfies booleanp))
  (prof-indextable)
  (prof-totalcount :type (integer 0 *) :initially 0)
  (prof-nextindex :type (integer 0 *) :initially 0)
  (prof-array :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (prof-stack :type (satisfies nat-nat-alist-p)))

(define interp-profiler-init (interp-profiler)
  :prepwork ((local (defthm equal-of-len
                      (implies (syntaxp (quotep n))
                               (equal (equal (len x) n)
                                      (cond ((not (natp n)) nil)
                                            ((equal n 0) (not (consp x)))
                                            (t (and (Consp x)
                                                    (equal (len (cdr x)) (1- n))))))))))
  :guard-hints (("goal" :in-theory (enable update-nth nth)
                 :do-not-induct t))
  :enabled t
  (mbe :logic (non-exec (create-interp-profiler))
       :exec (b* ((interp-profiler (update-prof-enabledp nil interp-profiler))
                  (interp-profiler (update-prof-indextable nil interp-profiler))
                  (interp-profiler (update-prof-totalcount 0 interp-profiler))
                  (interp-profiler (update-prof-nextindex 0 interp-profiler))
                  (interp-profiler (resize-prof-array 0 interp-profiler)))
               (update-prof-stack nil interp-profiler))))


;; Prof-array layout:
;; The index for each rule is associated with the rule in prof-indextable.
;; Each rule name gets 5 slots --
;; (* 5 index)       -- tries (successful)
;; (+ 1 (* 5 index)) -- tries (unsuccessful)
;; (+ 2 (* 5 index)) -- frames (successful)
;; (+ 3 (* 5 index)) -- frames (unsuccessful)
;; (+ 4 (* 5 index)) -- number of occurrences of the rule remaining on the stack.

;; Previously, we naively counted tries/frames by recording on the stack the
;; current total count of rule applications attempted, then adding the
;; difference between the new total count and the recorded total count when
;; popping that frame off the stack. However, when rules are applied under
;; other applications of the same rule, this counts many applications multiple
;; times for that rule.  E.g., if a rule is applied inside 99 other
;; applications of that same rule, then the frames counted under that
;; application are counted 100x toward that rule!

;; There is some double-counting inherent in counting frames (versus tries,
;; which are pretty straightforward).  Each rule application attempt will be
;; counted toward the frame count of every rule in the stack.  But we'll avoid
;; this sort of N^2 behavior within a single rule by only counting frames when
;; on the outermost application of a rule -- that is, when the number of
;; occurrences of the rule remaining on the stack is 1.


(defmacro prof-index-to-slot (index tries/frames succ/fail)
  (if (and (or (eq tries/frames :tries)
               (eq tries/frames :frames))
           (or (eq succ/fail :succ)
               (eq succ/fail :fail)))
      (if (eq tries/frames :tries)
          (if (eq succ/fail :succ)
              `(* 5 ,index)
            `(+ 1 (* 5 ,index)))
        (if (eq succ/fail :succ)
            `(+ 2 (* 5 ,index))
          `(+ 3 (* 5 ,index))))
    (er hard? 'prof-index-to-slot "Bad inputs~%")))

(defmacro prof-index-stackcount (index)
  `(+ 4 (* 5 ,index)))

(defmacro prof-index-in-range (index length)
  `(< (+ 4 (* 5 ,index)) ,length))

(local (defthm prof-arrayp-is-u32-listp
         (equal (prof-arrayp x)
                (acl2::u32-listp x))))

(local (in-theory (e/d (acl2::nth-in-u32-listp-integerp
                        acl2::nth-in-u32-listp-natp)
                       (unsigned-byte-p loghead nth update-nth natp))))

(local (defthm integerp-+
         (implies (and (integerp a) (integerp b))
                  (integerp (+ a b)))))

(local (defthm acl2-numberp-when-integerp
         (implies (integerp x)
                  (acl2-numberp x))))

(define prof-ensure-index (name interp-profiler)
  :returns (mv (index natp :rule-classes :type-prescription)
               (new-interp-profiler))
  :guard-hints (("goal" :do-not-induct t))
  (b* ((indextable (prof-indextable interp-profiler))
       (index (cdr (hons-get name indextable)))
       ((when (and (natp index)
                   (prof-index-in-range index (prof-array-length interp-profiler))))
        (mv index interp-profiler))
       (index (lnfix (prof-nextindex interp-profiler)))
       (interp-profiler (update-prof-nextindex (+ 1 index) interp-profiler))
       (interp-profiler (if (prof-index-in-range index (prof-array-length interp-profiler))
                            interp-profiler
                          (resize-prof-array (max 16 (* 8 (+ 1 index))) interp-profiler)))
       (interp-profiler (update-prof-indextable (hons-acons name index indextable) interp-profiler))
       (interp-profiler (update-prof-arrayi (prof-index-to-slot index :tries :succ) 0 interp-profiler))
       (interp-profiler (update-prof-arrayi (prof-index-to-slot index :tries :fail) 0 interp-profiler))
       (interp-profiler (update-prof-arrayi (prof-index-to-slot index :frames :succ) 0 interp-profiler))
       (interp-profiler (update-prof-arrayi (prof-index-to-slot index :frames :fail) 0 interp-profiler))
       (interp-profiler (update-prof-arrayi (prof-index-stackcount index) 0 interp-profiler)))
    (mv index interp-profiler))
  ///
  (std::defret prof-index-in-range-of-prof-ensure-index
    (prof-index-in-range index (len (nth *prof-arrayi* new-interp-profiler)))
    :rule-classes :linear)

  (std::defret prof-ensure-index-frame
    (implies (not (member n (list *prof-indextable*
                                  *prof-nextindex*
                                  *prof-arrayi*)))
             (equal (nth n new-interp-profiler)
                    (nth n interp-profiler)))))
  

;; (local (defthm plus-one-when-unsigned-byte-p
;;          (implies (and (unsigned-byte-p 32 x)
;;                        (<= (+ 1 x) #xffffffff))
;;                   (unsigned-byte-p 32 (+ 1 x)))
;;          :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(local (in-theory (enable acl2::nth-in-u32-listp-u32p)))

;; (local (defthm rationalp-when-integerp
;;          (implies (integerp x)
;;                   (rationalp x))))

(define prof-increment-stackcount ((index natp)
                                   interp-profiler)
  :returns (new-interp-profiler)
  :guard (prof-index-in-range index (prof-array-length interp-profiler))
  (b* ((stackcount-idx (prof-index-stackcount (lnfix index))))
    (update-prof-arrayi stackcount-idx
                        ;; needs to be 32-bit
                        (logand #xffffffff (+ 1 (prof-arrayi stackcount-idx interp-profiler)))
                        interp-profiler))
  ///

  (std::defret prof-increment-stackcount-frame
    (implies (not (member n (list *prof-arrayi*)))
             (equal (nth n new-interp-profiler)
                    (nth n interp-profiler)))
    :hints(("Goal" :in-theory (disable (force)))))

  (std::defret prof-increment-stackcount-len
    (implies (prof-index-in-range (nfix index) (len (nth *prof-arrayi* interp-profiler)))
             (Equal (len (nth *prof-arrayi* new-interp-profiler))
                    (len (nth *prof-arrayi* interp-profiler))))
    :hints(("Goal" :in-theory (disable (force))))))

(define prof-decrement-stackcount ((index natp)
                                   interp-profiler)
  :returns (mv (new-stackcount natp :rule-classes :type-prescription)
               (new-interp-profiler))
  :guard (prof-index-in-range index (prof-array-length interp-profiler))
  (b* ((stackcount-idx (prof-index-stackcount (lnfix index)))
       (new-stackcount (max 0 (+ -1 (lnfix (prof-arrayi stackcount-idx interp-profiler)))))
       (interp-profiler (update-prof-arrayi stackcount-idx
                                            new-stackcount
                                            interp-profiler)))
    (mv new-stackcount interp-profiler))
  ///

  (std::defret prof-decrement-stackcount-frame
    (implies (not (member n (list *prof-arrayi*)))
             (equal (nth n new-interp-profiler)
                    (nth n interp-profiler)))
    :hints(("Goal" :in-theory (disable (force)))))

  (std::defret prof-decrement-stackcount-len
    (implies (prof-index-in-range (nfix index) (len (nth *prof-arrayi* interp-profiler)))
             (Equal (len (nth *prof-arrayi* new-interp-profiler))
                    (len (nth *prof-arrayi* interp-profiler))))
    :hints(("Goal" :in-theory (disable (force))))))


;; Stack contains conses (rule-index . totalcount) that are pushed on when beginning to relieve a rule's hyps.  Each 
(define prof-push (name interp-profiler)
  :returns (new-interp-profiler)
  (b* (((unless (prof-enabledp interp-profiler)) interp-profiler)
       (totalcount (prof-totalcount interp-profiler))
       ((mv index interp-profiler) (prof-ensure-index name interp-profiler))
       (interp-profiler (prof-increment-stackcount index interp-profiler)))
    (update-prof-stack (cons (cons index totalcount) (prof-stack interp-profiler))
                       interp-profiler)))


(define prof-increment-index ((index natp)
                              successp
                              (diff posp)
                              interp-profiler)
  :returns (new-interp-profiler)
  :guard (prof-index-in-range index (prof-array-length interp-profiler))
  (b* ((tries-index (if successp
                        (prof-index-to-slot index :tries :succ)
                      (prof-index-to-slot index :tries :fail)))
       (frames-index (if successp
                         (prof-index-to-slot index :frames :succ)
                       (prof-index-to-slot index :frames :fail)))
       (interp-profiler (update-prof-arrayi tries-index
                                            ;; needs to be 32-bit
                                            (logand #xffffffff (+ 1 (prof-arrayi tries-index interp-profiler)))
                                            interp-profiler)))
    (update-prof-arrayi frames-index
                        ;; needs to be 32-bit
                        (logand #xffffffff (+ diff (prof-arrayi frames-index interp-profiler)))
                        interp-profiler))
  ///

  (std::defret prof-increment-index-frame
    (implies (not (member n (list *prof-arrayi*)))
             (equal (nth n new-interp-profiler)
                    (nth n interp-profiler)))
    :hints(("Goal" :in-theory (disable (force))))))

(define prof-increment-base ((index natp) (prev-count natp) successp interp-profiler)
  :returns (new-interp-profiler)
  :guard (prof-index-in-range index (prof-array-length interp-profiler))
  :guard-hints (("goal" :do-not-induct t))
  (b* ((totalcount (+ 1 (prof-totalcount interp-profiler)))
       ((unless (< (lnfix prev-count) totalcount))
        (cw "Interp-profiler count invariant violated~%")
        interp-profiler)
       (interp-profiler (update-prof-totalcount totalcount interp-profiler))
       ((mv stackcount interp-profiler) (prof-decrement-stackcount index interp-profiler))
       ((unless (eql stackcount 0))
        interp-profiler)
       (diff (- totalcount (lnfix prev-count))))
    (prof-increment-index index successp diff interp-profiler))
  ///
  (std::defret prof-increment-base-frame
    (implies (not (member n (list *prof-totalcount*
                                  *prof-arrayi*)))
             (equal (nth n new-interp-profiler)
                    (nth n interp-profiler)))))


(define prof-pop-increment (successp interp-profiler)
  ;; Takes the top entry off the stack and increments the given index with the given 
  :returns (new-interp-profiler)
  :guard-hints (("goal" :do-not-induct t
                 :expand ((nat-nat-alist-p (nth *prof-stack* interp-profiler)))))
  (b* (((unless (prof-enabledp interp-profiler))
        interp-profiler)
       (stack (prof-stack interp-profiler))
       ((unless (consp stack))
        (cw "Interp profiler: popping empty stack~%")
        interp-profiler)
       (interp-profiler (update-prof-stack (cdr stack) interp-profiler))
       ((cons index prev-count) (car stack))
       ((unless (prof-index-in-range index (prof-array-length interp-profiler)))
        (cw "Interp profiler: stack index out of range~%")
        interp-profiler))
    (prof-increment-base index prev-count successp interp-profiler))
  ///
  (std::defret prof-pop-increment-reduces-stack
    (implies (and (prof-enabledp interp-profiler)
                  (consp (prof-stack interp-profiler)))
             (equal (len (nth *prof-stack* new-interp-profiler))
                    (1- (len (nth *prof-stack* interp-profiler))))))

  (std::defret prof-pop-increment-frame
    (implies (not (member n (list *prof-totalcount*
                                  *prof-arrayi*
                                  *prof-stack*)))
             (equal (nth n new-interp-profiler)
                    (nth n interp-profiler)))))

(define prof-simple-increment (name interp-profiler)
  :returns (new-interp-profiler)
  :guard (prof-enabledp interp-profiler)
  (b* (((mv index interp-profiler) (prof-ensure-index name interp-profiler))
       (count (prof-totalcount interp-profiler)))
    (prof-increment-base index count t interp-profiler)))

(define prof-simple-increment-exec (name interp-profiler)
  :returns (new-interp-profiler)
  (b* (((unless (prof-enabledp interp-profiler))
        interp-profiler))
    (prof-simple-increment `(:x ,name) interp-profiler)))

(define prof-simple-increment-g (name interp-profiler)
  :returns (new-interp-profiler)
  (b* (((unless (prof-enabledp interp-profiler))
        interp-profiler))
    (prof-simple-increment `(:g ,name) interp-profiler)))

(define prof-reset (interp-profiler)
  :returns (new-interp-profiler)
  (b* ((interp-profiler (update-prof-indextable nil interp-profiler))
       (interp-profiler (update-prof-totalcount 0 interp-profiler))
       (interp-profiler (update-prof-nextindex 0 interp-profiler))
       (interp-profiler (resize-prof-array 0 interp-profiler))
       (interp-profiler (update-prof-stack nil interp-profiler)))
    interp-profiler))

(define prof-unwind-stack-aux (interp-profiler)
  :returns (new-interp-profiler)
  :guard (prof-enabledp interp-profiler)
  :measure (len (prof-stack interp-profiler))
  (b* (((unless (and (mbt (prof-enabledp interp-profiler))
                     (consp (prof-stack interp-profiler))))
        interp-profiler)
       (interp-profiler (prof-pop-increment nil interp-profiler)))
    (prof-unwind-stack-aux interp-profiler)))

(define prof-unwind-stack (interp-profiler)
  (b* (((unless (prof-enabledp interp-profiler))
        (cw "Profiler not enabled -- not unwinding stack~%")
        interp-profiler))
    (prof-unwind-stack-aux interp-profiler)))
       
  

(fty::defprod prof-entry
  ((name)
   (tries-succ natp :rule-classes :type-prescription)
   (tries-fail natp :rule-classes :type-prescription)
   (frames-succ natp :rule-classes :type-prescription)
   (frames-fail natp :rule-classes :type-prescription))
  :layout :list)

(fty::deflist prof-entrylist :elt-type prof-entry :true-listp t)

(define prof-entry-compare-tries ((x prof-entry-p)
                                  (y prof-entry-p))
  (> (+ (prof-entry->tries-succ x)
        (prof-entry->tries-fail x))
     (+ (prof-entry->tries-succ y)
        (prof-entry->tries-fail y)))
  ///

  (acl2::defsort prof-entry-tries-sort
    :prefix prof-entry-tries
    :compare< prof-entry-compare-tries
    :comparablep prof-entry-p
    :comparable-listp prof-entrylist-p
    :true-listp t))

(define prof-entry-compare-frames ((x prof-entry-p)
                                    (y prof-entry-p))
  (> (+ (prof-entry->frames-succ x)
        (prof-entry->frames-fail x))
     (+ (prof-entry->frames-succ y)
        (prof-entry->frames-fail y)))
  ///

  (acl2::defsort prof-entry-frames-sort
    :prefix prof-entry-frames
    :compare< prof-entry-compare-frames
    :comparablep prof-entry-p
    :comparable-listp prof-entrylist-p
    :true-listp t))

(define prof->prof-entry (name (index natp) interp-profiler)
  :guard (prof-index-in-range index (prof-array-length interp-profiler))
  :returns (entry prof-entry-p)
  (make-prof-entry :name name
                   :tries-succ (lnfix (prof-arrayi (prof-index-to-slot index :tries :succ) interp-profiler))
                   :tries-fail (lnfix (prof-arrayi (prof-index-to-slot index :tries :fail) interp-profiler))
                   :frames-succ (lnfix (prof-arrayi (prof-index-to-slot index :frames :succ) interp-profiler))
                   :frames-fail (lnfix (prof-arrayi (prof-index-to-slot index :frames :fail) interp-profiler))))

(define prof->prof-entrylist-aux (table
                                  interp-profiler
                                  (acc prof-entrylist-p))
  :returns (entries prof-entrylist-p)
  (b* (((when (atom table)) (prof-entrylist-fix acc))
       ((when (atom (car table)))
        (prof->prof-entrylist-aux (cdr table) interp-profiler acc))
       ((cons name index) (car table))
       ((unless (and (natp index)
                     (prof-index-in-range index (prof-array-length interp-profiler))))
        (cw "Interp-profiler invariant violated~%")
        (prof->prof-entrylist-aux (cdr table) interp-profiler acc))
       (entry (prof->prof-entry name index interp-profiler)))
    (prof->prof-entrylist-aux (cdr table) interp-profiler (cons entry acc))))

(define prof->prof-entrylist (interp-profiler)
  :returns (entries prof-entrylist-p)
  (prof->prof-entrylist-aux (prof-indextable interp-profiler)
                            interp-profiler
                            nil))

(define prof-print-separator ()
  (cw "   --------------------------------~%"))

(define prof-entry-print ((x prof-entry-p))
  ;; mostly copied from show-accumulated-persistence-phrase0
  (b* (((prof-entry x))
       (total-frames (+ x.frames-succ x.frames-fail))
       (total-tries (+ x.tries-succ x.tries-fail))
       (total-tries (if (eql total-tries 0) 1 total-tries))) ;; shouldn't be 0
    (progn$ (cw "~c0 ~c1 (~c2.~f3~f4) ~y5"
                (cons total-frames 10) (cons total-tries 8)
                (cons (floor total-frames total-tries) 5)
                (mod (floor (* 10 total-frames) total-tries) 10)
                (mod (floor (* 100 total-frames) total-tries) 10)
                x.name)
            (cw "~c0 ~c1    [useful]~%"
                (cons x.frames-succ 10)
                (cons x.tries-succ 8))
            (cw "~c0 ~c1    [useless]~%"
                (cons x.frames-fail 10)
                (cons x.tries-fail 8))
            (prof-print-separator))))

(define prof-entrylist-print ((entries prof-entrylist-p))
  (if (atom entries)
      nil
    (progn$ (prof-entry-print (car entries))
            (prof-entrylist-print (cdr entries)))))

(define prof-print-report (interp-profiler)
  (b* (((unless (prof-enabledp interp-profiler)) nil)
       (entries (prof->prof-entrylist interp-profiler))
       (by-frames (prof-entry-frames-sort entries)))
    (cw "FGL Accumulated Persistence~%~%")
    (cw "Total rule application attempts: ~x0~%~%" (prof-totalcount interp-profiler))
    (cw "   :frames   :tries    :ratio  rune~%")
    (prof-entrylist-print by-frames)))

(define prof-report (interp-profiler)
  (b* (((unless (prof-enabledp interp-profiler)) interp-profiler)
       (stack (prof-stack interp-profiler))
       (interp-profiler (prof-unwind-stack interp-profiler)))
    (prof-print-report interp-profiler)
    (and (consp stack)
         (cw "Note: ~x0 profiler stack entries were merged into the results.~%" (len stack)))
    interp-profiler))

