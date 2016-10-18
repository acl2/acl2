; Copyright (C) 2013, Regents of the University of Texas
; Written by: J Strother Moore and Qiang Zhang
;             Department of Computer Sciences
;             Univesity of Texas at Austin
;             October, 2004
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "script")

; A Proof of the Correctness of Dijkstra's Shortest Path Algorithm in
; ACL2

; See the paper ``Dijkstra's Shortest Path Algorithm Verified with ACL2''
; by the authors for a description of this script.

; Historical Notes: The first version of this proof was completed by
; Moore in September, 2003.  See /u/moore/shortest-path/dsp6.lisp.
; That file contained 92 defthms, 35 :hints, about 75 clause
; identifiers like "Goal" and "Subgoal" (some occur in comments), and
; 40 :use hints.  In order to learn ACL2, Zhang was given the task by
; Moore, first, to discover (independently) a proof (given the
; invariant), and, then, to clean it up.

; Zhang finished his first proof in December, 2003, using ACL2 Version
; 2.7.  In October, 2004, he cleaned up the proof, eliminating some of
; his hints.  This file is his second proof script.  In February,
; 2005, the authors wrote the paper above and in doing so renamed some
; of Zhang's functions and theorems.

; The current file contains 39 defuns, 126 defthms, 51 hints, 23 of
; which are :use hints mentioning 31 lemma instances.

(in-package "ACL2")

;All definitions
(defun del (x y)
  (if (endp y) nil
    (if (equal x (car y))
        (cdr y)
      (cons (car y) (del x (cdr y))))))

(defun memp (e x)
  (if (endp x) nil
    (or (equal e (car x))
        (memp e (cdr x)))))

(defun setp (s)
  (cond ((endp s) t)
        ((memp (car s) (cdr s)) nil)
        (t (setp (cdr s)))))

(defun my-union (s1 s2)
  (cond ((endp s1) s2)
        ((memp (car s1) s2)
         (my-union (cdr s1) s2))
        (t (cons (car s1)
                 (my-union (cdr s1) s2)))))

(defun my-subsetp (s1 s2)
  (cond ((endp s1) t)
        (t (and (memp (car s1) s2)
                (my-subsetp (cdr s1) s2)))))

(defun infinitep (x) (null x)) 

(defun lt (x y)
  (cond ((infinitep x) nil)
        ((infinitep y) t)
        (t (< x y))))

(defun plus (x y)
  (cond ((or (infinitep x)
             (infinitep y))
         nil)
        (t (+ x y))))

(defun edge-listp (lst)
  (cond ((endp lst) (equal lst nil))
        ((and (consp (car lst))
              (rationalp (cdar lst))
              (<= 0 (cdar lst))
              (not (assoc-equal (caar lst)
                          (cdr lst))))
         (edge-listp (cdr lst)))
        (t nil)))

(defun graphp (g)
  (cond ((endp g) (equal g nil))
        ((and (consp (car g))
              (edge-listp (cdar g)))
         (graphp (cdr g)))
        (t nil)))

(defun cons-set (e s)
  (if (memp e s) s
    (cons e s)))

(defun all-nodes (g)
  (cond ((endp g) nil)
        (t (cons-set (caar g)
                     (my-union (strip-cars (cdar g))
                               (all-nodes (cdr g)))))))

(defun nodep (n g) (memp n (all-nodes g)))

(defun neighbors (n g)
  (strip-cars (cdr (assoc-equal n g))))

(defun pathp-aux (path g)
  (cond ((endp path) nil)
        ((endp (cdr path))
         (nodep (car path) g))
        (t (and (memp (cadr path)
                     (neighbors (car path) g))
                (pathp-aux (cdr path) g)))))

(defun pathp (path g)
  (and (true-listp path)
       (pathp-aux path g)))

(defun edge-len (a b g)
  (cdr (assoc-equal b (cdr (assoc-equal a g)))))

(defun path-len (path g)
  (cond ((endp path) nil)
        ((endp (cdr path))
         (if (nodep (car path) g) 0 nil))
        (t (plus (edge-len (car path) (cadr path) g)
                 (path-len (cdr path) g)))))

(defun path (n pt) (cdr (assoc-equal n pt)))

(defun d (n pt g)
  (path-len (path n pt) g))

#|
(defun choose-next (ts pt g)
  (cond ((endp ts) '(non-node))
        ((endp (cdr ts)) (car ts))
        ((lt (d (car ts) pt g)
             (d (choose-next (cdr ts) pt g) pt g))
         (car ts))
        (t (choose-next (cdr ts) pt g))))
|#

(defun choose-next (ts pt g)
  (cond ((endp ts) '(non-node))
        ((endp (cdr ts)) (car ts))
        (t (let ((u (choose-next (cdr ts) pt g)))
             (if (lt (d (car ts) pt g) (d u pt g))
                 (car ts)
               u)))))

(defun reassign (u v-lst pt g)
  (cond ((endp v-lst) pt)
        (t (let* ((v (car v-lst))
                  (w (edge-len u v g)))
             (cond ((lt (plus (d u pt g) w)
                        (d v pt g))
                    (cons (cons v (append (path u pt) (list v)))
                          (reassign u (cdr v-lst) pt g)))
                   (t (reassign u (cdr v-lst) pt g)))))))

(defun dsp (ts pt g)
  (cond ((endp ts) pt)
        (t (let ((u (choose-next ts pt g)))
             (dsp (del u ts)
                  (reassign u (neighbors u g) pt g)
                  g)))))

(defun dijkstra-shortest-path (a b g)
  (let ((p (dsp (all-nodes g)
                (list (cons a (list a))) g)))
    (path b p)))

;===================================================================
(defun pathp-from-to (p a b g)
  (and (pathp p g)
       (equal (car p) a)
       (equal (car (last p)) b)))



(defun pt-propertyp (a pt g)
  (if (endp pt) t
    (and (or (null (cdar pt))
             (pathp-from-to (cdar pt) a (caar pt) g))
         (pt-propertyp a (cdr pt) g))))


(defun lte (n1 n2)
  (not (lt n2 n1)))

(defun shorterp (p1 p2 g)
  (lte (path-len p1 g)
       (path-len p2 g)))

(defun confinedp (p fs)
  (if (endp p) t
    (if (endp (cdr p)) t
      (and (memp (car p) fs)
           (confinedp (cdr p) fs)))))
#|
(defun-sk shortest-confined-pathp (a b p fs g)
  (forall path (implies (and (pathp-from-to path a b g)
                             (confinedp path fs))
                        (shorterp p path g))))
|#

(ENCAPSULATE
      NIL (LOGIC)
      (SET-MATCH-FREE-DEFAULT :ALL)
      (SET-INHIBIT-WARNINGS "Theory"
                            "Use" "Free" "Non-rec" "Infected")
      (ENCAPSULATE
           ((SHORTEST-CONFINED-PATHP-WITNESS (A B P FS G) PATH)
            (SHORTEST-CONFINED-PATHP (A B P FS G) T))
           (LOCAL (IN-THEORY '(IMPLIES)))
           (LOCAL (DEFCHOOSE SHORTEST-CONFINED-PATHP-WITNESS (PATH)
                             (A B P FS G)
                             (NOT (IMPLIES (AND (PATHP-FROM-TO PATH A B G)
                                                (CONFINEDP PATH FS))
                                           (SHORTERP P PATH G)))))
           (LOCAL (DEFUN SHORTEST-CONFINED-PATHP (A B P FS G)
                     (LET ((PATH (SHORTEST-CONFINED-PATHP-WITNESS A B P FS G)))
                          (IMPLIES (AND (PATHP-FROM-TO PATH A B G)
                                        (CONFINEDP PATH FS))
                                   (SHORTERP P PATH G)))))
;(IN-THEORY (DISABLE (SHORTEST-CONFINED-PATHP)))
           (DEFTHM SHORTEST-CONFINED-PATHP-DEF
             (EQUAL (SHORTEST-CONFINED-PATHP A B P FS G)
                    (LET ((PATH (SHORTEST-CONFINED-PATHP-WITNESS A B P FS G)))
                         (IMPLIES (AND (PATHP-FROM-TO PATH A B G)
                                       (CONFINEDP PATH FS))
                                  (SHORTERP P PATH G)))))
           (DEFTHM SHORTEST-CONFINED-PATHP-NECC
                   (IMPLIES (NOT (IMPLIES (AND (PATHP-FROM-TO PATH A B G)
                                               (CONFINEDP PATH FS))
                                          (SHORTERP P PATH G)))
                            (NOT (SHORTEST-CONFINED-PATHP A B P FS G)))
                   :HINTS (("Goal" :USE (SHORTEST-CONFINED-PATHP-WITNESS SHORTEST-CONFINED-PATHP)
                            :IN-THEORY (THEORY 'MINIMAL-THEORY))))))
(include-book "data-structures/utilities" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "ordinals/e0-ordinal" :dir :system)
(encapsulate ()
;Auxiliary functions for fixers and for instantiating defun-sk
  (defun count-non-members (x y)
   (cond ((endp x) 0)
         ((member (car x) y) (count-non-members (cdr x) y))
         (t (+ 1 (count-non-members (cdr x) y)))))

(defun measure (c stack g)
   (cons (+ 1 (count-non-members (strip-cars g) stack))
         (len c)))

(defun neighbors2 (node g)
  (cond ((endp g) nil)
        ((equal node (car (car g))) (cdr (car g)))
        (t (neighbors2 node (cdr g)))))


(set-well-founded-relation e0-ord-<)
(local (in-theory (enable strip-cars)))

(defun find-all-next-steps (c stack b g)
    (declare (xargs :measure (measure c stack g)))
    (cond
     ((endp c) nil)
     ((member (car c) stack)
      (find-all-next-steps (cdr c) stack b g))
     ((equal (car c) b)
      (cons (reverse (cons b stack))
            (find-all-next-steps (cdr c) stack b g)))
     (t (append (find-all-next-steps (neighbors2 (car c) g)
                                     (cons (car c) stack)
                                     b g)
                (find-all-next-steps (cdr c) stack b g)))))

(defun change-rep (vs g)
  ;remove weights and also add empty entries for non-neighbour vertices
  (if (endp vs)
    g
    (b* ((entry (assoc-equal (car vs) g))
         ((when (null entry)) (change-rep (cdr vs) (put-assoc-equal (car vs) nil g)))
         (edges-with-weights (cdr entry))
         (edges (strip-cars edges-with-weights)))
        (change-rep (cdr vs) (put-assoc-equal (car vs) edges g)))))
  
(defun find-all-simple-paths (a b g)
  (if (and (equal a b) (nodep a g)) ; added for type-safety and less-restrictive fixer rules
    (list (list a))
    (b* ((g1 (change-rep (all-nodes g) g)))
        (find-all-next-steps (neighbors2 a g1) ;(neighbours a g1) bug 
                             (list a) b g1))))
)

(u::defloop shortest-confined-pathp/exec1 (paths a b p fs g)
  (for ((path in paths)) (always (implies (and (pathp-from-to path a b g)
                                               (confinedp path fs))
                                          (shorterp p path g)))))

(defun shortest-confined-pathp/exec (a b p fs g)
  (shortest-confined-pathp/exec1 (find-all-simple-paths a b g) a b p fs g))

(defttag t)
;(defattach (shortest-confined-pathp shortest-confined-pathp/exec)) guards not verified
(defattach (shortest-confined-pathp shortest-confined-pathp/exec) :skip-checks t)
(defttag nil)

#|  
(defun-sk shortest-pathp (a b p g)
  (forall path (implies (pathp-from-to path a b g)
                        (shorterp p path g))))
|#

(ENCAPSULATE NIL (LOGIC)
              (SET-MATCH-FREE-DEFAULT :ALL)
              (SET-INHIBIT-WARNINGS "Theory"
                                    "Use" "Free" "Non-rec" "Infected")
              (ENCAPSULATE ((SHORTEST-PATHP-WITNESS (A B P G) PATH)
                             (SHORTEST-PATHP (A B P G) T))
                           (LOCAL (IN-THEORY '(IMPLIES)))
                           (LOCAL (DEFCHOOSE SHORTEST-PATHP-WITNESS (PATH)
                                             (A B P G)
                                             (NOT (IMPLIES (PATHP-FROM-TO PATH A B G)
                                                           (SHORTERP P PATH G)))))
                           (LOCAL (DEFUN SHORTEST-PATHP (A B P G)
                                    (LET ((PATH (SHORTEST-PATHP-WITNESS A B P G)))
                                      (IMPLIES (PATHP-FROM-TO PATH A B G)
                                               (SHORTERP P PATH G)))))
;(IN-THEORY (DISABLE (SHORTEST-PATHP)))
                           (DEFTHM SHORTEST-PATHP-DEF
                             (EQUAL (SHORTEST-PATHP A B P G)
                                    (LET ((PATH (SHORTEST-PATHP-WITNESS A B P G)))
                                         (IMPLIES (PATHP-FROM-TO PATH A B G)
                                                  (SHORTERP P PATH G)))))
                           (DEFTHM SHORTEST-PATHP-NECC
                                   (IMPLIES (NOT (IMPLIES (PATHP-FROM-TO PATH A B G)
                                                          (SHORTERP P PATH G)))
                                            (NOT (SHORTEST-PATHP A B P G)))
                                   :HINTS (("Goal" :USE (SHORTEST-PATHP-WITNESS SHORTEST-PATHP)
                                            :IN-THEORY (THEORY 'MINIMAL-THEORY))))))

(u::defloop shortest-pathp/exec1 (paths a b p g)
            (for ((path in paths)) (always (implies (pathp-from-to path a b g)
                                                    (shorterp p path g)))))

(defun shortest-pathp/exec (a b p g)
  (shortest-pathp/exec1 (find-all-simple-paths a b g) a b p g))

(defttag t)
(defattach (shortest-pathp shortest-pathp/exec) :skip-checks t)
(defttag nil)

(defun ts-propertyp (a ts fs pt g)
  (if (endp ts) t
    (and (shortest-confined-pathp a (car ts) (path (car ts) pt) fs g)
         (confinedp (path (car ts) pt) fs)
         (ts-propertyp a (cdr ts) fs pt g))))

(defun fs-propertyp (a fs fs0 pt g)
  (if (endp fs) t
    (and (shortest-pathp a (car fs) (path (car fs) pt) g)
         (confinedp (path (car fs) pt) fs0)
         (fs-propertyp a (cdr fs) fs0 pt g))))

(defun comp-set (ts s)
  (if (endp s) nil
    (if (memp (car s) ts)
        (comp-set ts (cdr s))
      (cons (car s) (comp-set ts (cdr s))))))

(defun invp (ts pt g a)
  (let ((fs (comp-set ts (all-nodes g))))
    (and (ts-propertyp a ts fs pt g)
         (fs-propertyp a fs fs pt g)
         (pt-propertyp a pt g))))

(defun find-partial-path (p s)
  (if (endp p) nil
    (if (memp (car p) s)
        (cons (car p) (find-partial-path (cdr p) s))
      (list (car p)))))

(defun find-last-next-path (p)
  (if (or (endp p) (endp (cdr p))) nil
    (cons (car p) (find-last-next-path (cdr p)))))

(defun last-node (p)
  (car (last (find-last-next-path p))))

(defun find-partial-path-to-u (p u)
  (cond ((not (memp u p)) nil)
        ((equal (car p) u) (list u))
        (t (cons (car p)
                 (find-partial-path-to-u (cdr p) u)))))
