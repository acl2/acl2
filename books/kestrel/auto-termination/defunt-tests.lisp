; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See the README file in this directory and see :doc defunt.

(in-package "ACL2")

(include-book "defunt-top")
(include-book "std/testing/must-fail" :dir :system)

; Below, we insert, as comments, "*Defunt note*" remarks from the output of
; defunt.  We use some multi-line comments so that the include-book forms will
; be seen by the dependency scanner.

(must-fail

; Failure should be fast.  Interactively, using time$, we have seen this take
; 0.00 seconds.
; We can expect to see the following error message:

; ACL2 Error in (DEFUNT FFF ...):  Unable to find previous termination
; theorem!

 (defunt fff (x)
   (if (consp x)
       (fff (cddddr (cddddr x)))
     x)))

(defunt f0 (x y)
; *Defunt note*: Using termination theorem for EVENS.
  (if (endp x)
      y
    (list (f0 (cddr x) (cons 23 y)) 100)))

(defunt f1 (x y)

; *Defunt note*: Using termination theorem for COMPRESS211.

; This takes advantage of the subsumption-replacement-loop in norm-clause-lst.
; Before that, during development, this still succeeded by taking advantage of
; truncated-integer-sin/cos-table-fn, book "misc/sin-cos".

  (if (zp (- y x))
      (list x y)
    (f1 (1+ x) y)))

(defunt string-equal1-alt (str1 str2 i maximum)
; *Defunt note*: Using termination theorem for STRING-EQUAL1.
  (let ((i (nfix i)))
    (cond
     ((>= i (ifix maximum))
      t)
     (t (and (char-equal (char str1 i)
                         (char str2 i))
             (string-equal1-alt str1 str2 (+ 1 i) maximum))))))

(defunt compress211-alt (name l i x j default)
; *Defunt note*: Using termination theorem for COMPRESS211.
  (declare (irrelevant name default))
  (cond ((zp (- j x))
         nil)
        (t (let ((pair (assoc2 i x l)))
             (cons pair
                   (compress211-alt name l i (+ 1 x) j default))))))

(defunt f2 (x y)

; NOTE: Uses more than one termination theorem.

; *Defunt note*: Using termination theorems for EVENS and TRUE-LISTP.

  (if (consp x)
      (if (atom y)
          (f2 (cddr x) y)
        (f2 (cdr x) y))
    (list x y)))

(defunt f3 (x y)

; This defunt call is like the one above, except that it uses three previous
; theorems, and it locally includes a book in the generated encapsulate, as
; follows.

; *Defunt note*: Using termination theorems for SYMBOL-BTREE-TO-ALIST-AUX,
; EVENS and TRUE-LISTP.

#||
*Defunt note*: Evaluating
(LOCAL (INCLUDE-BOOK
        "misc/symbol-btree" :DIR :SYSTEM))
to define function SYMBOL-BTREE-TO-ALIST-AUX.
||#

  (if (consp x)
      (if (atom y)
          (list (f3 (cddr x) y) (f3 (cadr x) y))
        (f3 (cdr x) y))
    (list x y)))

(defunt f4 (x y)

; *Defunt note*: Using termination theorem for STR::BASIC-NATCHARS.

#||
*Defunt note*: Evaluating
(LOCAL (INCLUDE-BOOK
        "std/strings/decimal" :DIR :SYSTEM))
to define function STR::BASIC-NATCHARS.
||#

  (cond ((zp x) y)
        (t (f4 (floor x 10)
               (cons x y)))))

(defunt my-merge (x y)

; *Defunt note*: Using termination theorem for <-MERGE.

#||
*Defunt note*: Evaluating 
(LOCAL (INCLUDE-BOOK
        "projects/irv/irv" :DIR :SYSTEM))
to define function <-MERGE.
||#

  (cond ((endp x) y)
        ((endp y) x)
        ((< (car x) (car y))
         (cons (car x)
               (my-merge (cdr x) y)))
        (t (cons (car y)
                 (my-merge x (cdr y))))))

(defunt count-up-to (bound from)
; *Defunt note*: Using termination theorem for COMPRESS211.
   (cond ((zp (- bound from)) 0)
         (t (cons from (count-up-to bound (+ 1 from))))))

(DEFUNt DFS-COLLECT-new (NODES EDGES STACK)

#||
*Defunt note*: Executing the following form in order to define the
well-founded relation, NAT-LIST-<:
(INCLUDE-BOOK
 "std/basic/two-nats-measure" :DIR :SYSTEM)
||#

; *Defunt note*: Using termination theorem for DFS-COLLECT.

#||
*Defunt note*: Evaluating
(LOCAL (INCLUDE-BOOK
        "centaur/misc/dfs-measure" :DIR :SYSTEM))
to define function DFS-COLLECT.
||#

  (B* (((WHEN (ATOM NODES)) STACK)
       (NODE (CAR NODES))
       ((WHEN (HONS-GET NODE STACK))
        (DFS-COLLECT-new (CDR NODES) EDGES STACK))
       (SUCCS (CDR (HONS-GET NODE EDGES)))
       (STACK1 (HONS-ACONS NODE T STACK))
       (STACK1 (DFS-COLLECT-new SUCCS EDGES STACK1))
       ((UNLESS (MBT (SUFFIXP STACK STACK1)))
        STACK1))
    (DFS-COLLECT-new (CDR NODES) EDGES STACK1)))
