; Centaur Miscellaneous Books
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "nats-equiv")
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/equiv" :dir :system))
(local (in-theory (enable* arith-equiv-forwarding)))


; Abstract stobj containing an array of naturals.  Represented by a list of
; naturals, accessed/updated by nth/update-nth.


; General theorems about nth/update-nth and nat-lists.

(local (defthm equal-of-booleans-rewrite
         (implies (and (booleanp x)
                       (booleanp y))
                  (equal (equal x y)
                         (iff x y)))
         :rule-classes ((:rewrite :backchain-limit-lst 1))))

(defthm natp-of-nth-when-nat-listp
  (implies (nat-listp x)
           (equal (natp (nth n x))
                  (< (nfix n) (len x))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                          (implies (nat-listp x)
                                   (<= 0 (nth n x))))))

(defthm nat-listp-of-update-nth
  (implies (nat-listp x)
           (equal (nat-listp (update-nth n v x))
                  (and (<= (nfix n) (len (double-rewrite x)))
                       (natp v)))))

(defthm nat-listp-of-resize-list
  (implies (and (nat-listp x)
                (natp default))
           (nat-listp (resize-list x n default))))



(defstobj natarr$c
  (nats$c :type (array (integer 0 *) (0))
          :initially 0
          :resizable t)
  :inline t)

(defthm nats$cp-is-nat-listp
  (equal (nats$cp x) (nat-listp x)))

(defun natarr$ap (natarr$a)
  (declare (xargs :guard t))
  (nat-listp natarr$a))
(defun create-natarr$a ()
  (declare (xargs :guard t))
  nil)
(defun nats$a-length (natarr$a)
  (declare (xargs :guard (natarr$ap natarr$a)
                  :verify-guards t))
  (len natarr$a))
(defun resize-nats$a (i natarr$a)
  (declare (xargs :guard (natarr$ap natarr$a)))
  (resize-list natarr$a i 0))

(defun nats$ai (i natarr$a)
  (declare (xargs :guard (and (natarr$ap natarr$a)
                              (natp i)
                              (< i (nats$a-length natarr$a)))
                  :verify-guards t))
  (nfix (nth i natarr$a)))

(defun update-nats$ai (i v natarr$a)
  (declare (xargs :guard (and (natarr$ap natarr$a)
                              (natp i)
                              (< i (nats$a-length natarr$a))
                              (natp v))
                  :verify-guards t))
  (update-nth i (nfix v) natarr$a))

(defun-nx natarr$corr (natarr$c natarr$a)
  (and (natarr$cp natarr$c)
       (equal (len natarr$a) (len (nth 0 natarr$c)))
       (nats-equiv natarr$a (nth 0 natarr$c))))

(local (in-theory (disable nth (natarr$corr))))

(DEFTHM CREATE-NATARR{CORRESPONDENCE}
        (NATARR$CORR (CREATE-NATARR$C)
                     (CREATE-NATARR$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-NATARR{PRESERVED}
        (NATARR$AP (CREATE-NATARR$A))
        :RULE-CLASSES NIL)

(DEFTHM NATS-LENGTH{CORRESPONDENCE}
        (IMPLIES (AND (NATARR$CORR NATARR$C NATARR)
                      (NATARR$AP NATARR))
                 (EQUAL (NATS$C-LENGTH NATARR$C)
                        (NATS$A-LENGTH NATARR)))
        :RULE-CLASSES NIL)

(DEFTHM GET-NAT{CORRESPONDENCE}
        (IMPLIES (AND (NATARR$CORR NATARR$C NATARR)
                      (NATARR$AP NATARR)
                      (NATP I)
                      (< I (NATS$A-LENGTH NATARR)))
                 (EQUAL (NATS$CI I NATARR$C)
                        (NATS$AI I NATARR)))
        :RULE-CLASSES NIL
        :hints(("Goal"
                :in-theory (disable NATS-EQUIV-IMPLIES-NAT-EQUIV-NTH-2)
                :use ((:instance NATS-EQUIV-IMPLIES-NAT-EQUIV-NTH-2
                                 (n i)
                                 (x (NTH *NATS$CI* NATARR$C))
                                 (x-equiv natarr))))))

(DEFTHM GET-NAT{GUARD-THM}
        (IMPLIES (AND (NATARR$CORR NATARR$C NATARR)
                      (NATARR$AP NATARR)
                      (NATP I)
                      (< I (NATS$A-LENGTH NATARR)))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (NATS$C-LENGTH NATARR$C))))
        :RULE-CLASSES NIL)

(DEFTHM SET-NAT{CORRESPONDENCE}
        (IMPLIES (AND (NATARR$CORR NATARR$C NATARR)
                      (NATARR$AP NATARR)
                      (NATP I)
                      (< I (NATS$A-LENGTH NATARR))
                      (NATP V))
                 (NATARR$CORR (UPDATE-NATS$CI I V NATARR$C)
                              (UPDATE-NATS$AI I V NATARR)))
        :RULE-CLASSES NIL)

(DEFTHM SET-NAT{GUARD-THM}
        (IMPLIES (AND (NATARR$CORR NATARR$C NATARR)
                      (NATARR$AP NATARR)
                      (NATP I)
                      (< I (NATS$A-LENGTH NATARR))
                      (NATP V))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (NATS$C-LENGTH NATARR$C))
                      (INTEGERP V)
                      (<= 0 V)))
        :RULE-CLASSES NIL)

(DEFTHM SET-NAT{PRESERVED}
        (IMPLIES (AND (NATARR$AP NATARR)
                      (NATP I)
                      (< I (NATS$A-LENGTH NATARR))
                      (NATP V))
                 (NATARR$AP (UPDATE-NATS$AI I V NATARR)))
        :RULE-CLASSES NIL)

(encapsulate
  ()
  (local (defun my-ind (n x y)
           (if (zp n)
               (list n x y)
             (my-ind (- n 1) (cdr x) (cdr y)))))

  (local (defthm crock
           (implies (and (syntaxp (not (equal x y)))
                         (nats-equiv x y)
                         (equal (len x) (len y)))
                    (nats-equiv (resize-list x n default-value)
                                (resize-list y n default-value)))
           :rule-classes ((:rewrite :loop-stopper ((y x))))
           :hints(("Goal" :induct (my-ind n x y)))))

  (local (defthm len-resize-list
           (equal (len (resize-list lst m default))
                  (nfix m))))

  (DEFTHM RESIZE-NATS{CORRESPONDENCE}
    (IMPLIES (AND (NATARR$CORR NATARR$C NATARR)
                  (NATARR$AP NATARR))
             (NATARR$CORR (RESIZE-NATS$C I NATARR$C)
                          (RESIZE-NATS$A I NATARR)))
    :RULE-CLASSES NIL))

(DEFTHM RESIZE-NATS{PRESERVED}
        (IMPLIES (NATARR$AP NATARR)
                 (NATARR$AP (RESIZE-NATS$A I NATARR)))
        :RULE-CLASSES NIL)


(defabsstobj natarr
  :exports ((nats-length :exec nats$c-length  :logic nats$a-length)
            (get-nat     :exec nats$ci        :logic nats$ai)
            (set-nat     :exec update-nats$ci :logic update-nats$ai)
            resize-nats))


