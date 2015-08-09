; Reduction of TMI to an Algorithm to be Implemented on M1
; J Strother Moore
; April 10, 2012

; (ld '((include-book "../m1/m1") . "tmi-reductions.lisp") :ld-pre-eval-print t)

; Certification instructions:
; cd /u/moore/courses/cs378/jvm/spring-12/equivalence/
; acl2h536t
; (include-book "../m1/m1-lemmas")
; (time$ (with-output :off :all (certify-book "tmi-reductions" 1)))

; Timing on Whitehart
; 190.28 seconds realtime, 184.22 seconds runtime

; Some comments below could be wrong... All of them need to be read carefully
; in light of what is now in the file.

; ---
; The proof is really messy toward the end.  Start with theorem-b-raw and work
; forward.  The hack lemmas and hints are depressing and probably fragile.
; Try to get rewrite rules to do the work.

; Notes: This file was tmi5.lisp before being completed.  Here are my
; frequently used build commands.

; (ld "tmi5.lisp" :ld-pre-eval-print t)
; (acl2::with-output :off :all (ld "tmi5.lisp" :ld-pre-eval-print nil))

; See improved-assembler.lisp for some random thoughts followed by a suggestion
; for a better assembly langugage.  If you implement it, redo all of the M1
; proofs!

; Some problems were discovered in the arithmetic library.

; Tell Robert that (set-default-arithmetic-theory) doesn't do the job advertised in
; the README.  If you
; (include-book "arithmetic-5/top" :dir :system)
; (defun log2 (n)
;   (cond ((zp n) 0)
;         ((equal n 1) 0)
;         (t (+ 1 (log2 (floor n 2))))))
; the defun of log2 works.  But if you (set-default-arithmetic-theory) before the
; defun, it does not.  I want to be able to switch back and forth between
; minimal-arithmetic-theory and the default and cannot.

; Tell Robert about not-equal-ncons-nnil below!

(in-package "M1")

;(set-gag-mode :goals)
(set-irrelevant-formals-ok t)
(set-ignore-ok :warn)

(defun rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x))
              (list (car x)))))

(defun rev1 (x a)
  (if (endp x)
      a
      (rev1 (cdr x) (cons (car x) a))))

(defun symp (x)
  (member x '(0 1)))

(defun sym (x)
  (if (consp x) (car x) 0))

(defun half-tape (x)
  (if (endp x)
      (equal x nil)
      (and (symp (car x))
           (half-tape (cdr x)))))

(defun tapep (x)
  (and (consp x)
       (half-tape (car x))
       (half-tape (cdr x))))

(defun show-tape (tape)
  (cond ((consp tape)
         (rev1 (car tape)
               (cons '[ (cons (sym (cdr tape)) (cons '] (cdr (cdr tape)))))))
        (t nil)))

(defun current-sym (tape) (sym (cdr tape)))

(defun operationp (x)
  (member x '(L R 0 1)))

(defun state-namep (x)
  (symbolp x))

(defun turing-4-tuple (x)
  (and (true-listp x)
       (equal (len x) 4)
       (state-namep (nth 0 x))
       (symp (nth 1 x))
       (operationp (nth 2 x))
       (state-namep (nth 3 x))))

(defun turing-machinep (x)
  (if (endp x)
      (equal x nil)
      (and (turing-4-tuple (car x))
           (turing-machinep (cdr x)))))

(defun instr (st sym tm)

; This function retrieves the first 4-tuple in Turing machine tm with
; state-name st and symbol sym, if any.  If no such tuple exists, it returns
; nil.

  (if (endp tm)
      nil
      (if (and (equal st (nth 0 (car tm)))
               (equal sym (nth 1 (car tm))))
          (car tm)
          (instr st sym (cdr tm)))))

(defun new-tape (op tape)

; Returns a new tape by carrying out operation op on tape.

  (case op
    (L (cons (cdr (car tape))
             (cons (sym (car tape))
                   (cdr tape))))
    (R (cons (cons (sym (cdr tape))
                   (car tape))
             (cdr (cdr tape))))
    (otherwise
     (cons (car tape)
           (cons op (cdr (cdr tape)))))))

(defun test-tape (ops tape)
  (cond ((endp ops) (list (show-tape tape)))
        (t (cons (show-tape tape)
                 (test-tape (cdr ops)
                            (new-tape (car ops) tape))))))

(defthm test-tape-demo
  (equal (test-tape '(L L L 1 R R R R R R 1 L L L) '(nil . nil))
         '(([ 0 ])
           ([ 0 ])
           ([ 0 ] 0)
           ([ 0 ] 0 0)
           ([ 1 ] 0 0)
           (1 [ 0 ] 0)
           (1 0 [ 0 ])
           (1 0 0 [ 0 ])
           (1 0 0 0 [ 0 ])
           (1 0 0 0 0 [ 0 ])
           (1 0 0 0 0 0 [ 0 ])
           (1 0 0 0 0 0 [ 1 ])
           (1 0 0 0 0 [ 0 ] 1)
           (1 0 0 0 [ 0 ] 0 1)
           (1 0 0 [ 0 ] 0 0 1)))
  :rule-classes nil)

(defun tmi (st tape tm n)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) nil)
        ((instr st (current-sym tape) tm)
         (tmi (nth 3 (instr st (current-sym tape) tm))
              (new-tape (nth 2 (instr st (current-sym tape) tm)) tape)
              tm
              (- n 1)))
        (t tape)))

(defconst *rogers-tm*
  '((Q0 1 0 Q1)
    (Q1 0 R Q2)
    (Q2 1 0 Q3)
    (Q3 0 R Q4)
    (Q4 1 R Q4)
    (Q4 0 R Q5)
    (Q5 1 R Q5)
    (Q5 0 1 Q6)
    (Q6 1 R Q6)
    (Q6 0 1 Q7)
    (Q7 1 L Q7)
    (Q7 0 L Q8)
    (Q8 1 L Q1)
    (Q1 1 L Q1)))

(defconst *example-tape*
  '(nil . (1 1 1 1 1)))

(defthm rogers-tm-demo
  (let ((tape *example-tape*))
    (and (equal (show-tape tape) '([ 1 ] 1 1 1 1))
         (equal (show-tape (tmi 'Q0 tape *rogers-tm* 77))
                nil)
         (equal (show-tape (tmi 'Q0 tape *rogers-tm* 78))
                '(0 0 0 0 [ 0 ] 0 1 1 1 1 1 1 1 1))))
  :rule-classes nil)


; My plan is to implement a Turing machine interpreter on M1 by representing a
; tape as a natural number whose bits correspond to the 0s and 1s on the tape.
; Similarly, I will transform the Turing machine program into a natural number
; that can be unpacked by M1 into the ``same'' 4-tuples.  However, the presence
; of the symbols in the definition of Turing machines prevents us from direct
; numeric translation.  So step 1 is to convert our Turing machine program into
; something involving only 4-tuples of numbers.  We'll rename the states to be
; the consecutive natural numbers and we'll represent op=L with 2 and op=R with
; 3, so legal ops in the new representation will be 0, 1, 2, 3.  We'll define
; tmi1 to operate on these programs and prove that it is equivalent to tmi.

; Step 2 will introduce tmi2, in which the Turing machine program is a single
; big number.  We'll prove tmi1 equivalent to tmi2.

; Step 3 will introduce tmi3, in which the tape is a big number.  We'll prove
; tmi2 equivalent to tmi3.

; Step 4 will define m1-tmi which is the algorithm we'll implement on M1.  We
; will prove tmi equivalent to m1-tmi.  Thus, it will remain only to prove the
; M1 code correct.

(defun renaming-map2 (st i map)
  (cond ((assoc st map)
         (mv i map))
        (t (mv (+ i 1)
               (cons (cons st i) map)))))

(defun renaming-map1 (tm i map)
  (cond ((endp tm) map)
        (t (let ((st-in   (nth 0 (car tm)))
                 (st-out  (nth 3 (car tm))))
             (mv-let (i map)
                     (renaming-map2 st-in i map)
                     (mv-let (i map)
                             (renaming-map2 st-out i map)
                             (renaming-map1 (cdr tm) i map)))))))

(defun renaming-map (st tm)
  (mv-let (i map)
          (renaming-map2 st 0 nil)
          (renaming-map1 tm i map)))

(defun tm-to-tm1 (tm map)
  (cond ((endp tm) nil)
        (t (let ((st-in  (nth 0 (car tm)))
                 (sym    (nth 1 (car tm)))
                 (op     (nth 2 (car tm)))
                 (st-out (nth 3 (car tm))))
             (cons (list (cdr (assoc st-in map))
                         sym
                         (case op (L 2) (R 3) (otherwise op))
                         (cdr (assoc st-out map)))
                   (tm-to-tm1 (cdr tm) map))))))

(defun assoc-inverse (key alist)
  (cond ((endp alist) nil)
        ((equal key (cdr (car alist))) (car alist))
        (t (assoc-inverse key (cdr alist)))))

(defun tm1-to-tm (tm1 map)
  (cond ((endp tm1) nil)
        (t (let ((st-in  (nth 0 (car tm1)))
                 (sym    (nth 1 (car tm1)))
                 (op     (nth 2 (car tm1)))
                 (st-out (nth 3 (car tm1))))
             (cons (list (car (assoc-inverse st-in map))
                         sym
                         (case op (2 'L) (3 'R) (otherwise op))
                         (car (assoc-inverse st-out map)))
                   (tm1-to-tm (cdr tm1) map))))))

(defun descending-map (map)
  (cond ((endp map) t)
        ((endp (cdr map)) t)
        ((> (cdr (car map)) (cdr (car (cdr map))))
         (descending-map (cdr map)))
        (t nil)))

(defun total-map (tm map)
  (cond ((endp tm) t)
        (t (let ((st-in  (nth 0 (car tm)))
                 (st-out (nth 3 (car tm))))
             (and (assoc st-in map)
                  (assoc st-out map)
                  (total-map (cdr tm) map))))))

(defun natp-map (map)
  (cond ((endp map) t)
        (t (and (natp (cdr (car map)))
                (natp-map (cdr map))))))

(defthm natp-map-renaming-map
  (implies (and (natp-map map)
                (natp i))
           (natp-map (renaming-map1 tm i map))))

(defthm renaming-map-preserves-map
  (implies (assoc st map)
           (equal (assoc st (renaming-map1 tm i map))
                  (assoc st map))))

(defthm total-map-renaming-map
  (total-map tm (renaming-map1 tm i map)))

(defthm descending-map-renaming-map
  (implies (and (natp i)
                (descending-map map)
                (or (not (consp map))
                    (< (cdr (car map)) i)))
           (descending-map (renaming-map1 tm i map))))

(defthm assoc-inverse-assoc-lemma
  (implies (and (consp alist)
                (not (equal key (car (car alist))))
                (assoc key (cdr alist))
                (integerp (cdr (car alist)))
                (<= 0 (cdr (car alist)))
                (natp-map (cdr alist))
                (< (cdr (car (cdr alist)))
                   (cdr (car alist)))
                (descending-map (cdr alist)))
           (not (equal (cdr (assoc key (cdr alist)))
                       (cdr (car alist)))))
  :otf-flg t)

(defthm assoc-inverse-assoc
  (implies (and (assoc key alist)
                (natp-map alist)
                (descending-map alist))
           (equal (assoc-inverse (cdr (assoc key alist)) alist)
                  (assoc key alist))))


(defthm car-assoc
  (implies (assoc key alist)
           (equal (car (assoc key alist)) key)))

(defthm equal-len-0
 (equal (equal (len x) 0) (atom x)))

(defthm equal-len-1
  (equal (equal (len x) 1)
         (and (consp x)
              (atom (cdr x)))))

(defthm tm-to-tm1-to-tm
  (implies (and (turing-machinep tm)
                (natp-map map)
                (total-map tm map)
                (descending-map map))
           (equal (tm1-to-tm (tm-to-tm1 tm map) map)
                  tm)))

(defun new-tape1 (op1 tape)
; Like new-tape, but uses numeric ops
  (case op1
    ((0 1)
     (cons (car tape)
           (cons op1 (cdr (cdr tape)))))
    (2 (cons (cdr (car tape))
             (cons (sym (car tape))
                   (cdr tape))))
    (otherwise (cons (cons (sym (cdr tape))
                           (car tape))
                     (cdr (cdr tape))))))

(defun tmi1 (st tape tm1 n)
; Like tmi but tm1 is a list of 4-tuples composed entirely of numbers.
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) nil)
        ((instr st (current-sym tape) tm1)
         (tmi1 (nth 3 (instr st (current-sym tape) tm1))
               (new-tape1 (nth 2 (instr st (current-sym tape) tm1)) tape)
               tm1
               (- n 1)))
        (t tape)))

(defthm car-instr
  (implies (turing-machinep tm)
           (and (equal (car (instr st sym tm))
                       (if (instr st sym tm)
                           st
                           nil))
                (equal (car (cdr (instr st sym tm)))
                       (if (instr st sym tm)
                           sym
                           nil)))))

(defthm instr-implies-mapped-instr
  (implies (and (turing-machinep tm)
                (natp-map map)
                (total-map tm map)
                (descending-map map)
                (instr st sym tm))
           (instr (cdr (assoc st map)) sym (tm-to-tm1 tm map))))

(defthm cdr-assoc-descending-lemma
  (implies (and (consp map)
                (descending-map map)
                (force (assoc key (cdr map))))
           (< (cdr (assoc key (cdr map)))  (cdr (car map))))
  :rule-classes :linear)

(defthm map-property
  (implies (and (natp-map map)
                (descending-map map))
           (equal (equal (cdr (assoc key1 map))
                         (cdr (assoc key2 map)))
                  (if (assoc key1 map)
                      (if (assoc key2 map)
                          (equal key1 key2)
                          nil)
                      (if (assoc key2 map)
                          nil
                          t)))))

(defthm instr-implies-mapped-instr-vice-versa
  (implies (and (turing-machinep tm)
                (natp-map map)
                (total-map tm map)
                (descending-map map)
                (not (instr st sym tm)))
           (not (instr (cdr (assoc st map)) sym (tm-to-tm1 tm map)))))

(defthm instr-implies-assoc
  (implies (and (turing-machinep tm)
                (instr st sym tm))
           (assoc st tm)))

(defthm mapped-instr
  (implies (and (turing-machinep tm)
                (natp-map map)
                (total-map tm map)
                (descending-map map))
           (equal (instr (cdr (assoc st map)) sym (tm-to-tm1 tm map))
                  (if (instr st sym tm)
                      (let ((st-in  (nth 0 (instr st sym tm)))
                            (sym    (nth 1 (instr st sym tm)))
                            (op     (nth 2 (instr st sym tm)))
                            (st-out (nth 3 (instr st sym tm))))
                        (list (cdr (assoc st-in map))
                              sym
                              (case op (L 2) (R 3) (otherwise op))
                              (cdr (assoc st-out map))))
                      nil))))

(defthm symbolp-st-out-instr
  (implies (and (turing-machinep tm)
                (instr st sym tm))
           (symbolp (car (cdr (cdr (cdr (instr st sym tm))))))))

(defthm total-map-covers-tm
  (implies (and (turing-machinep tm)
                (instr st sym tm)
                (total-map tm map))
           (assoc (car (cdr (cdr (cdr (instr st sym tm))))) map)))

(defthm mapped-new-tape1
  (implies (natp op1)
           (equal (new-tape1 op1 tape)
                  (new-tape (case op1 ((0 1) op1) (2 'L) (otherwise 'R))
                            tape))))

(defthm op-instr
  (implies (and (turing-machinep tm)
                (instr st sym tm)
                (not (equal (nth 2 (instr st sym tm)) 'L))
                (not (equal (nth 2 (instr st sym tm)) 'R))
                (not (equal (nth 2 (instr st sym tm))  0)))
           (equal (car (cdr (cdr (instr st sym tm)))) 1)))

(defthm op-instr-lessp-trick
  (implies (and (turing-machinep tm)
                (instr st sym tm))
           (< (car (cdr (cdr (instr st sym tm)))) 2))
  :rule-classes :linear)

(defthm tmi1-is-tmi-lemma
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm)
                (natp-map map)
                (total-map tm map)
                (assoc st map)
                (descending-map map))
           (equal (tmi1 (cdr (assoc st map))
                        tape
                        (tm-to-tm1 tm map)
                        n)
                  (tmi st tape tm n)))
  :hints (("Goal" :induct (tmi st tape tm n))
          ("Subgoal *1/2.13" :expand (TMI1 (CDR (ASSOC-EQUAL ST MAP))
                                           TAPE (TM-TO-TM1 TM MAP)
                                           N))
          ("Subgoal *1/2.5''" :expand (TMI1 (CDR (ASSOC-EQUAL ST MAP))
                                            TAPE (TM-TO-TM1 TM MAP)
                                            N)))
  :rule-classes nil)

(defthm tmi1-is-tmi
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm))
           (equal (tmi1 (cdr (assoc st (renaming-map st tm)))
                        tape
                        (tm-to-tm1 tm (renaming-map st tm))
                        n)
                  (tmi st tape tm n)))
  :hints (("Goal"
           :use ((:instance tmi1-is-tmi-lemma (map (renaming-map st tm)))))))

; That completes step 1.  Now we move to step 2: introduce tmi2, in which the
; Turing machine program is a single big number.  We'll prove tmi1 equivalent
; to tmi2.

; Consider a tm1-style machine.  It is a list of 4-tuples of natural numbers.
; Each tuple is (st-in sym op st-out) where st-in and st-out are arbitrary nats
; (``state numbers''), sym is 0 or 1 and op is a nat less than 4.  We will
; first determine the width, w, into which we can pack all the state numbers.

(defun log2 (n)
  (cond ((zp n) 0)
        ((equal n 1) 0)
        (t (+ 1 (log2 (floor n 2))))))

(defun log2-implies-expt-upperbound-hint (n w)
  (cond ((zp n) (list n w))
        ((equal n 1) (list n w))
        (t (log2-implies-expt-upperbound-hint (floor n 2) (- w 1)))))

(defthm log2-implies-expt-upperbound
  (implies (and (natp w)
                (natp n))
           (equal (< w (log2 n))
                  (not (< n (expt 2 (+ w 1))))))
  :hints (("Goal" :induct (log2-implies-expt-upperbound-hint n w))))

(defthm log2-implies-expt-upperbound-corollary
  (implies (and (not (< w (+ 1 (log2 n))))
                (natp w)
                (natp n))
           (< n (expt 2 w)))
  :rule-classes ((:linear)
                 (:linear :corollary
                          (implies (and (not (< n (expt 2 w)))
                                        (natp w)
                                        (natp n))
                                   (< w (+ 1 (log2 n))))))
  :hints (("Goal" :use (:instance log2-implies-expt-upperbound
                                  (w (- w 1))
                                  (n n))
           :in-theory (disable log2-implies-expt-upperbound))))


(defun max-width1 (tm1)
  (if (endp tm1)
      0
      (max (+ 1 (max (log2 (nth 0 (car tm1)))
                     (log2 (nth 3 (car tm1)))))
           (max-width1 (cdr tm1)))))

(defun max-width (tm map)
  (max-width1 (tm-to-tm1 tm map)))

(defun turing1-4-tuple (x w)
  (and (true-listp x)
       (equal (len x) 4)
       (natp (nth 0 x))
       (< (nth 0 x) (expt 2 w))
       (natp (nth 1 x))
       (< (nth 1 x) 2)
       (natp (nth 2 x))
       (< (nth 2 x) 4)
       (natp (nth 3 x))
       (< (nth 3 x) (expt 2 w))))

(defun turing1-machinep (x w)
  (if (endp x)
      (equal x nil)
      (and (turing1-4-tuple (car x) w)
           (turing1-machinep (cdr x) w))))


; We will pack each tuple into a ``cell'' using simple arithmetic.  The two
; state numbers fit in w bits each, the sym fits in 1 bit, and the op fits in
; 2.  However, we will allocate 3 bits for op.  Consider how we'll ``assoc''
; for a given st-in and sym through the big number that is the concatenation of
; all these cells.  We will repeatedly extract the st-in and sym from the
; low-order cell and if they're not the ones we are looking for we'll shift the
; big number right by the cell length.  But how do we know when we've reached
; the end?  (A cell of all 0s is perfectly legal.)  We must have a non-0 marker
; cell.  That will be an otherwise all 0 cell with an op of 4.  Thus, ops will
; have 3 bits allocated for them.

(defun make-cell (tuple w)

; W is the number of bits required to represent a state number.  For example,
; if the highest state number is 8, then four bits are required: 8 = #b1000.
; (So w is in fact (log2 <max-state-number>)+1.

; I pack tuple with st-in and sym in the least significant bits, so (mod cell
; (expt 2 (+ 1 w))) gets them both.

  (let ((st-in  (nth 0 tuple))  ; w bits
        (sym    (nth 1 tuple))  ; 1 bit
        (op     (nth 2 tuple))  ; 3 bits (see above)
        (st-out (nth 3 tuple))) ; w bits
    (+ (* (expt 2 (+ 3 1 w)) st-out)
       (* (expt 2 (+ 1 w)) op)
       (* (expt 2 w) sym)
       st-in)))

; Now we use make-cell to create a big number representing the given tmi1-style
; machine.

(defun ncons (cell tail w)
  (+ cell
     (* (expt 2 (+ 4 (* 2 w))) tail)))

(defun ncar (tm w)
  (mod tm (expt 2 (+ 4 (* 2 w)))))

(defun ncdr (tm w)
  (ash tm (- (+ 4 (* 2 w)))))

(defun cellp (cell w)
  (and (natp cell)
       (< cell (expt 2 (+ 4 (* 2 w))))))

(defthm ncar-ncons
  (implies (and (natp w)
                (cellp cell w)
                (natp tail))
           (equal (ncar (ncons cell tail w) w)
                  cell)))

(defthm ncdr-ncons
  (implies (and (natp w)
                (cellp cell w)
                (natp tail))
           (equal (ncdr (ncons cell tail w) w)
                  tail)))

(defthm cellp-make-cell
  (implies (and (natp w)
                (turing1-4-tuple tuple w))
           (cellp (make-cell tuple w) w))
  :hints (("Goal" :nonlinearp t))
  :rule-classes (:rewrite
                 (:linear :corollary
                          (implies (and (natp w)
                                        (force (turing1-4-tuple tuple w)))
                                   (<= 0 (make-cell tuple w))))
                 (:type-prescription :corollary
                                     (implies (and (natp w)
                                                   (force (turing1-4-tuple tuple w)))
                                              (integerp (make-cell tuple w))))))

(defthm ncdr-decreases
  (implies (and (natp w)
                (not (zp tm)))
           (< (ncdr tm w) tm))
  :rule-classes :linear)

(defthm natp-ncdr
  (implies (and (natp w)
                (natp tm))
           (natp (ncdr tm w)))
  :rule-classes :type-prescription)

(defthm positive-natp-ncons
  (implies (and (natp w)
                (natp cell)
                (integerp tail)
                (< 0 tail))
           (and (integerp (ncons cell tail w))
                (< 0 (ncons cell tail w))))
  :rule-classes
  ((:type-prescription :corollary
                       (implies (and (force (natp w))
                                     (force (natp cell))
                                     (force (integerp tail))
                                     (force (< 0 tail)))
                                (integerp (ncons cell tail w))))
   (:linear :corollary
            (implies (and (force (natp w))
                          (force (natp cell))
                          (force (integerp tail))
                          (force (< 0 tail)))
                     (< 0 (ncons cell tail w))))))

(in-theory (disable ncons ncar ncdr cellp))

(defun nst-in (cell w)
  (mod cell (expt 2 w)))

(defun nsym (cell w)
  (mod (ash cell (- w)) 2))

(defun nop (cell w)
  (mod (ash cell (- (+ 1 w))) (expt 2 3)))

(defun nst-out (cell w)
  (mod (ash cell (- (+ 4 w)))
       (expt 2 w)))

(defun nnil (w)
  (make-cell (list 0 0 4 0) w))

(defun ncode (tm w)
  (cond ((endp tm) (nnil w))
        (t (ncons (make-cell (car tm) w)
                  (ncode (cdr tm) w)
                  w))))

(defthm positive-natp-nnil
  (implies (natp w)
           (and (integerp (nnil w))
                (< 0 (nnil w))))
  :rule-classes :type-prescription)

(defthm positive-natp-ncode
  (implies (and (natp w)
                (turing1-machinep tm w))
           (and (integerp (ncode tm w))
                (< 0 (ncode tm w))))
  :rule-classes ((:type-prescription :corollary
                                     (implies (and (force (natp w))
                                                   (force (turing1-machinep tm w)))
                                              (integerp (ncode tm w))))
                 (:linear :corollary
                          (implies (and (force (natp w))
                                        (force (turing1-machinep tm w)))
                                   (< 0 (ncode tm w))))))

(defthm nst-in-make-cell
  (implies (and (natp w)
                (turing1-4-tuple tuple w))
           (equal (nst-in (make-cell tuple w) w)
                  (nth 0 tuple))))

(defthm nsym-make-cell
  (implies (and (natp w)
                (turing1-4-tuple tuple w))
           (equal (nsym (make-cell tuple w) w)
                  (nth 1 tuple))))

(defthm nop-make-cell
  (implies (and (natp w)
                (turing1-4-tuple tuple w))
                (equal (nop (make-cell tuple w) w)
                       (nth 2 tuple)))
  :hints (("Goal" :in-theory (e/d (acl2::scatter-exponents-theory)
                                  (acl2::gather-exponents-theory))
           :nonlinearp t
                  :do-not-induct t)))

(defthm nst-out-make-cell
  (implies (and (natp w)
                (turing1-4-tuple tuple w))
           (equal (nst-out (make-cell tuple w) w)
                  (nth 3 tuple)))
  :hints (("Goal" :in-theory (e/d (acl2::scatter-exponents-theory)
                                  (acl2::gather-exponents-theory))
           :nonlinearp t
           :do-not-induct t)))

(defthm nop-nnil
  (implies (natp w)
           (equal (nop (nnil w) w) 4))
  :hints (("Goal" :in-theory (e/d (acl2::scatter-exponents-theory)
                                  (acl2::gather-exponents-theory))
           :nonlinearp t
           :do-not-induct t)))

(defthm not-equal-ncons-nnil
  (implies (and (natp w)
                (cellp cell w)
                (turing1-machinep tm w))
           (< (nnil w) (ncons cell (ncode tm w) w)))
  :rule-classes :linear
  :hints (("Goal" :nonlinearp t
           :in-theory (enable ncons cellp))
          ("Subgoal *1/1'''"
           :in-theory nil
           :use (:instance (:theorem
                            (implies (and (natp i)
                                          (natp j)
                                          (natp cell)
                                          (< i j))
                                     (< (expt 2 i) (+ cell (expt 2 j)))))
                           (i (+ 3 W))
                           (j (+ 7 (* 3 W)))))
          ("Subgoal *1/1.3" :in-theory (enable natp))
          ("Subgoal *1/1.2" :in-theory (enable natp))
          ("Subgoal *1/1.1" :in-theory (enable natp))))

(in-theory (disable nst-in nsym nop nst-out make-cell nnil))

(defun ninstr (st sym tm w)
  (if (natp w)
      (if (zp tm)
          -1
          (if (equal tm (nnil w))
              -1
              (let ((cell (ncar tm w)))
                (if (and (equal st (nst-in cell w))
                         (equal sym (nsym cell w)))
                    cell
                    (ninstr st sym (ncdr tm w) w)))))
      -1))

(defthm ninstr-ncode
  (implies (and (force (natp w))
                (force (natp st))
                (force (< st (expt 2 w)))
                (force (natp sym))
                (force (< sym 2))
                (force (turing1-machinep tm w)))
           (equal (ninstr st sym (ncode tm w) w)
                  (if (instr st sym tm)
                      (make-cell (instr st sym tm) w)
                      -1))))

(defun tmi2 (st tape tm2 w n)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) nil)
        ((equal (ninstr st (current-sym tape) tm2 w) -1)
         tape)
        (t
         (tmi2 (nst-out (ninstr st (current-sym tape) tm2 w) w)
               (new-tape1 (nop (ninstr st (current-sym tape) tm2 w) w) tape)
               tm2
               w
               (- n 1)))))

(defthm natp-make-cell
  (implies (and (force (natp w))
                (force (turing1-4-tuple tuple w)))
           (natp (make-cell tuple w)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable make-cell))))

(defthm properties-of-instr
  (implies (and (force (turing1-machinep tm w))
                (force (natp w))
                (instr st sym tm))
           (and (equal (nth 0 (instr st sym tm)) st)
                (equal (nth 1 (instr st sym tm)) sym)
                (integerp (nth 2 (instr st sym tm)))
                (<= 0 (nth 2 (instr st sym tm)))
                (< (nth 2 (instr st sym tm)) 4)
                (integerp (nth 3 (instr st sym tm)))
                (<= 0 (nth 3 (instr st sym tm)))
                (< (nth 3 (instr st sym tm)) (expt 2 w))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (force (turing1-machinep tm w))
                           (force (natp w))
                           (instr st sym tm))
                      (and (equal (nth 0 (instr st sym tm)) st)
                           (equal (nth 1 (instr st sym tm)) sym))))
   (:type-prescription :corollary
                 (implies (and (force (turing1-machinep tm w))
                               (force (natp w))
                               (instr st sym tm))
                          (and (integerp (nth 2 (instr st sym tm)))
                               (<= 0 (nth 2 (instr st sym tm))))))
   (:type-prescription :corollary
                 (implies (and (force (turing1-machinep tm w))
                               (force (natp w))
                               (instr st sym tm))
                          (and (integerp (nth 3 (instr st sym tm)))
                               (<= 0 (nth 3 (instr st sym tm))))))
   (:linear :corollary
            (implies (and (force (turing1-machinep tm w))
                          (force (natp w))
                          (instr st sym tm))
                     (and (<= 0 (nth 2 (instr st sym tm)))
                          (< (nth 2 (instr st sym tm)) 4)
                          (<= 0 (nth 3 (instr st sym tm)))
                          (< (nth 3 (instr st sym tm)) (expt 2 w)))))))


(defthm turing1-4-tuple-instr
  (implies (and (natp w)
                (instr st sym tm)
                (turing1-machinep tm w))
           (turing1-4-tuple (instr st sym tm) w))
  :hints (("Goal" :in-theory (disable turing1-4-tuple))))


(defthm tapep-new-tape1
  (implies (and (tapep tape)
                (natp op))
           (tapep (new-tape1 op tape))))



(defthm natp-current-sym
  (implies (tapep tape)
           (and (integerp (current-sym tape))
                (<= 0 (current-sym tape))
                (< (current-sym tape) 2)))
  :rule-classes
  ((:type-prescription :corollary
                       (implies (tapep tape)
                                (integerp (current-sym tape))))
   (:linear :corollary
            (implies (tapep tape)
                     (and (<= 0 (current-sym tape))
                          (< (current-sym tape) 2))))))

(defthm tmi2-is-tmi1
  (implies (and (natp w)
                (natp st)
                (< st (expt 2 w))
                (tapep tape)
                (turing1-machinep tm1 w))
           (equal (tmi2 st tape (ncode tm1 w) w n)
                  (tmi1 st tape tm1 n)))
  :hints (("Goal" :in-theory (disable tmi1-is-tmi ninstr turing1-4-tuple instr ncode
                                      current-sym nth nth-add1!
                                      tapep new-tape1 MAPPED-NEW-TAPE1
                                      ))))


; That completes step 2.  Step 3 will introduce tmi3, in which the tape is a
; big number.  We'll prove tmi2 equivalent to tmi3.


; Our next goal is to re-represent the tape as a pair of natural numbers, (n . pos)
; where the bits between the bottom and the topmost 1 in the binary expansion of n
; represent the tape and pos is the bit position of the current bit.  For example,
; ((0 1 0 0) . (1 1 0 0 0))
; = (0 0 1 0 [ 1 ] 1 0 0 0)
; = (#B0010110001 . 4)

; We need to be able to convert back and forth between tapes and these pairs.

; (i-am-here)


(defun convert-half-tape-to-nat (htape)
 (cond ((endp htape) 0)
       (t (+ (car htape)
             (* 2 (convert-half-tape-to-nat (cdr htape)))))))

(defun convert-tape-to-tapen-pos (tape)
  (let ((lo (convert-half-tape-to-nat (rev (car tape))))
        (lo-size (len (car tape)))
        (hi (convert-half-tape-to-nat (cdr tape)))
        (hi-size (len (cdr tape))))
    (mv (+ lo (* (expt 2 lo-size) hi) (expt 2 (+ lo-size hi-size)))
        lo-size)))

(defun nat-to-half-tape (n size)
  (cond ((zp size) nil)
        (t (cons (mod n 2) (nat-to-half-tape (floor n 2) (- size 1))))))

(defun decode-tape-and-pos (tapen pos)
  (let* ((n tapen)
         (lo-size pos)
         (hi-size (log2 n)))
    (cons (rev (nat-to-half-tape n lo-size))
          (nat-to-half-tape (ash n (- lo-size))
                            (- hi-size lo-size)))))

(in-theory (enable member))

(defthm natp-convert-half-tape-to-nat
  (implies (half-tape htape)
           (and (integerp (convert-half-tape-to-nat htape))
                (<= 0 (convert-half-tape-to-nat htape))))
  :rule-classes ((:rewrite) (:type-prescription)
                 (:linear :corollary
                          (implies (half-tape htape)
                                   (<= 0 (convert-half-tape-to-nat htape))))))


(defthm half-tape-conversion
  (implies (half-tape htape)
           (equal (nat-to-half-tape (convert-half-tape-to-nat htape)
                                    (len htape))
                  htape)))


(defthm half-tape-append
  (implies (half-tape x)
           (equal (half-tape (append x (list bit)))
                  (or (equal bit 0)
                      (equal bit 1)))))

(defthm half-tape-rev
  (implies (half-tape x)
           (half-tape (rev x))))

(defthm convert-half-tape-to-nat-append
  (implies (and (half-tape htape)
                (or (equal bit 0)
                    (equal bit 1)))
           (equal (convert-half-tape-to-nat (append x (list bit)))
                  (+ (convert-half-tape-to-nat x) (* bit (expt 2 (len x)))))))


(defthm half-tape-below-expt
  (implies (and (natp k)
                (half-tape htape))
           (equal (NAT-TO-HALF-TAPE (+ (CONVERT-HALF-TAPE-TO-NAT htape)
                                       (* k (EXPT 2 (LEN htape))))
                                    (LEN htape))
                  htape))
  :rule-classes nil)

(defthm len-rev
  (equal (len (rev x)) (len x)))

(defthm rev-rev
  (implies (true-listp x)
           (equal (rev (rev x)) x)))

(defthm half-tape-implies-true-listp
  (implies (half-tape htape)
           (true-listp htape)))

(defthm convert-half-tape-to-nat-upper-bound
  (implies (half-tape x)
           (< (convert-half-tape-to-nat x) (expt 2 (len x))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm convert-half-tape-to-nat-upper-bound-corollary
  (implies (half-tape x)
           (< (convert-half-tape-to-nat (rev x)) (expt 2 (len x))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defun hint (k n) (if (zp n) (list k n) (hint (floor k 2) (- n 1))))

(defthm log2-sum
  (implies (and (natp n)
                (natp k)
                (< k (expt 2 n)))
           (equal (log2 (+ k (expt 2 n)))  n))
  :hints (("Goal" :induct (hint k n)))
  :rule-classes nil)

(defthm log2-sum-corollary
  (implies (and (half-tape htape1)
                (half-tape htape2))
           (equal (LOG2 (+ (CONVERT-HALF-TAPE-TO-NAT (REV htape1))
                           (* (CONVERT-HALF-TAPE-TO-NAT htape2)
                              (EXPT 2 (LEN htape1)))
                           (EXPT 2
                                 (+ (LEN htape1)
                                    (LEN htape2)))))
                  (+ (LEN htape1)
                     (LEN htape2))))
  :hints (("Goal" :nonlinearp t
                  :use (:instance log2-sum
                                  (k (+ (CONVERT-HALF-TAPE-TO-NAT (REV htape1))
                                        (* (CONVERT-HALF-TAPE-TO-NAT htape2)
                                           (EXPT 2 (LEN htape1)))))
                                  (n (+ (LEN htape1)
                                        (LEN htape2)))))))

(defthm floor-lemma-1
  (implies (and (natp i)
                (natp j)
                (natp n)
                (natp m)
                (< i (expt 2 n)))
           (equal (floor (+ i (* j (expt 2 n)) (expt 2 (+ n m)))
                         (expt 2 n))
                  (+ j (expt 2 m)))))

(defthm get-the-upper-half-tape
  (IMPLIES (HALF-TAPE TAPE2)
           (EQUAL (NAT-TO-HALF-TAPE (+ (CONVERT-HALF-TAPE-TO-NAT TAPE2)
                                       (EXPT 2 (LEN TAPE2)))
                                    (LEN TAPE2))
                  TAPE2)))

(defthm tape-conversion-theorem
  (implies (tapep tape)
           (equal (decode-tape-and-pos
                   (mv-nth 0 (convert-tape-to-tapen-pos tape))
                   (mv-nth 1 (convert-tape-to-tapen-pos tape)))
                  tape))
  :hints
  (("Goal" :do-not-induct t)
   ("Goal'4'" :use (:instance half-tape-below-expt
                                (htape (rev tape1))
                                (k (+ (CONVERT-HALF-TAPE-TO-NAT tape2)
                                      (expt 2 (len tape2))))))))

#| this npair theorem is no longer possible to state because it abuses types
(defthm tape-conversion-theorem-stronger
  (implies (or (tapep tape)
               (equal tape nil))
           (equal (convert-npair-to-tape
                   (convert-tape-to-npair tape))
                  tape))
  :hints
  (("Goal" :in-theory (disable convert-npair-to-tape
                               convert-tape-to-npair))))
|#

; I think of the theorem above as an important sanity check.  But the real work
; comes in implementing and verifying the numeric analogues of current-sym and
; new-tape:

(defun current-symn (tapen pos)

; If we shift the tape down by pos and find that it is just 1, then we've
; reached the end of the tape and everything thereafter is 0.  That 1 is just a
; marker, not a legitimate bit.

  (if (equal pos (log2 tapen))
      0
      (mod (ash tapen (- pos)) 2)))

(defthm current-symn-convert-tape-to-tapen-pos
  (implies (tapep tape)
           (equal (current-symn (mv-nth 0 (convert-tape-to-tapen-pos tape))
                                (mv-nth 1 (convert-tape-to-tapen-pos tape)))
                  (current-sym tape))))


(defun new-tape2 (op tapen pos)
  (CASE OP
    ((0 1)
     (if (equal pos (log2 tapen))
         (if (equal op 0)
             (mv (+ tapen (expt 2 pos)) pos)
             (mv (+ tapen (expt 2 (+ pos 1))) pos))
         (let ((sym (current-symn tapen pos)))
           (cond ((equal sym op)
                  (mv tapen pos))
                 ((equal sym 0)
                  (mv (+ tapen (expt 2 pos))
                      pos))
                 (t (mv (- tapen (expt 2 pos))
                        pos))))))
    (2 (if (zp pos)
           (mv (* 2 tapen) 0)
           (mv tapen (- pos 1))))
    (otherwise (if (equal pos (log2 tapen))
                   (mv (+ (- tapen (expt 2 pos)) (expt 2 (+ 1 pos)))
                       (+ 1 pos))
                   (mv tapen (+ pos 1))))))

(defthm half-tape-below-expt-rule1
  (implies (and (natp k)
                (natp n)
                (half-tape htape))
           (equal (NAT-TO-HALF-TAPE (+ (CONVERT-HALF-TAPE-TO-NAT (REV htape))
                                       (* k (EXPT 2 (LEN htape)))
                                       (EXPT 2 (+ n (LEN htape))))
                                    (LEN htape))
                  (rev htape)))
  :hints (("Goal" :do-not-induct t
                  :use (:instance half-tape-below-expt
                                  (htape (REV htape))
                                  (k (+ k (EXPT 2 n)))))))

(defthm half-tape-below-expt-rule2
  (implies (and (natp k)
                (natp i)
                (natp n)
                (half-tape htape))
           (equal (NAT-TO-HALF-TAPE (+ (CONVERT-HALF-TAPE-TO-NAT (REV htape))
                                       (* k (EXPT 2 (+ i (LEN htape))))
                                       (EXPT 2 (+ i n (LEN htape))))
                                    (LEN htape))
                  (rev htape)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable half-tape-below-expt-rule1)
           :use (:instance half-tape-below-expt-rule1
                           (k (* k (expt 2 i)))
                           (n (+ i n))))))

(defthm floor-lemma-1-special-case
  (implies (and (natp i)
                (natp j)
                (natp n)
                (natp m)
                (< i (expt 2 n)))
           (equal (floor (+ i
                            (* j (expt 2 (+ 1 n)))
                            (expt 2 (+ 1 m n)))
                         (expt 2 n))
                  (+ (* 2 j) (* 2 (expt 2 m)))))
  :hints (("Goal" :in-theory (disable floor-lemma-1)
                  :use (:instance floor-lemma-1
                                  (j (* 2 j))
                                  (m (+ 1 m))))))

(defthm log2-sum-corollary2
  (implies (and (natp n)
                (natp k1)
                (natp k2)
                (< (+ k1 k2) (expt 2 n)))
           (equal (log2 (+ k1 k2 (expt 2 n)))  n))
  :hints (("Goal" :use (:instance log2-sum
                                  (k (+ k1 k2))))))


(defthm half-tape-below-expt-rule3
  (implies (and (natp k)
                (natp i)
                (natp n)
                (half-tape htape))
           (equal (NAT-TO-HALF-TAPE (+ (CONVERT-HALF-TAPE-TO-NAT (REV htape))
                                       (expt 2 (len htape))
                                       (* k (EXPT 2 (+ i (LEN htape))))
                                       (EXPT 2 (+ i n (LEN htape))))
                                    (LEN htape))
                  (rev htape)))
  :hints (("Goal"
           :use (:instance half-tape-below-expt
                           (htape (REV htape))
                           (k (+ 1 (* k (expt 2 i)) (expt 2 (+ i n))))))))

(defthm floor-lemma-1-special-case-2
  (implies (and (natp i)
                (natp j)
                (natp n)
                (natp m)
                (< i (expt 2 n)))
           (equal (floor (+ i
                            (expt 2 n)
                            (* j (expt 2 (+ 1 n)))
                            (expt 2 (+ 1 m n)))
                         (expt 2 n))
                  (+ 1 (* 2 j) (* 2 (expt 2 m)))))
  :hints (("Goal" :in-theory (disable floor-lemma-1)
                  :use (:instance floor-lemma-1
                                  (j (+ 1 (* 2 j)))
                                  (m (+ 1 m))))))

(defthm log2-sum-corollary3
  (implies (and (natp n)
                (natp k1)
                (natp k2)
                (natp k3)
                (< (+ k1 k2 k3) (expt 2 n)))
           (equal (log2 (+ k1 k2 k3 (expt 2 n)))  n))
  :hints (("Goal" :use (:instance log2-sum
                                  (k (+ k1 k2 k3))))))


(defthm half-tape-below-expt-rule4
  (implies (half-tape htape)
           (equal (nat-to-half-tape (+ (convert-half-tape-to-nat htape)
                                       (expt 2 (len htape)))
                                    (len htape))
                  htape))
  :hints (("Goal" :use (:instance half-tape-below-expt
                                  (k 1))))
  :rule-classes nil)

; !!! this is identical to log2-sum, which has rule-classes nil...

(defthm log2-sum-corollary4
  (implies (and (natp n) (natp k) (< k (expt 2 n)))
           (equal (log2 (+ k (expt 2 n))) n))
  :hints (("Goal" :use log2-sum)))

(defthm floor-lemma-1-special-case-3
  (implies (and (natp i)
                (natp j)
                (natp n)
                (natp m)
                (< i (expt 2 n)))
           (equal (floor (+ i
                            (* j (expt 2 (+ 1 n)))
                            (expt 2 (+ 1 n m)))
                         (expt 2 (+ 1 n)))
                  (+ j (expt 2 m))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (disable floor-lemma-1)
                  :use (:instance floor-lemma-1
                                  (n (+ n 1))))))

(defthm rationalp-intp-+
  (implies (and (common-lisp::rationalp x)
                (common-lisp::rationalp y))
           (common-lisp::rationalp (acl2::intp-+ x y)))
  :rule-classes (:type-prescription :rewrite))

#|
(defun testn (op tape)
  (equal (new-tape2 op (convert-tape-to-npair tape))
         (convert-tape-to-npair (new-tape op tape))))|#

(defthm new-tape2-convert-tape-to-tapen-transformed
  (implies (and (natp op)
;                (< op 4)
                (tapep tape))
           (equal (new-tape2 op
                             (mv-nth 0 (convert-tape-to-tapen-pos tape))
                             (mv-nth 1 (convert-tape-to-tapen-pos tape)))
                  (convert-tape-to-tapen-pos (new-tape1 op tape)))))

(in-theory (disable current-sym current-symn
                    convert-tape-to-tapen-pos
                    decode-tape-and-pos
                    new-tape new-tape1 new-tape2 MAPPED-NEW-TAPE1 mv-nth))

(defthm new-tape2-convert-tape-to-tapen-pos
  (implies (and  (natp op)
;                (< op 4)
                 (tapep tape))
           (equal
            (decode-tape-and-pos
             (mv-nth 0 (new-tape2 op (mv-nth 0 (convert-tape-to-tapen-pos tape))
                                        (mv-nth 1 (convert-tape-to-tapen-pos tape))))
             (mv-nth 1 (new-tape2 op (mv-nth 0 (convert-tape-to-tapen-pos tape))
                                        (mv-nth 1 (convert-tape-to-tapen-pos tape)))))
            (new-tape1 op tape))))

(defun tmi3 (st tapen pos tm w n)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n)
         (mv 0 st tapen pos))
        ((equal (ninstr st (current-symn tapen pos) tm w) -1)
         (mv 1 st tapen pos))
        (t
         (mv-let (new-tapen new-pos)
                 (new-tape2 (nop (ninstr st (current-symn tapen pos) tm w) w)
                            tapen pos)
                 (tmi3 (nst-out (ninstr st (current-symn tapen pos) tm w) w)
                       new-tapen
                       new-pos
                       tm
                       w
                       (- n 1))))))

#| I prefer to avoid yet another level...
(defun tmi3! (st npair tm w n)
  (let* ((ans (tmi3 st npair tm w n))
         (haltedp (nth 0 ans))
         (final-st (nth 1 ans))
         (final-tape-pair (nth 2 ans)))
    (declare (ignore final-st))
    (if haltedp
        final-tape-pair
        nil)))
|#

(defthm nop-ninstr
  (implies (and (natp w)
                (natp tm)
                (natp st)
                (< st (expt 2 w))
                (natp sym)
                (< sym 2)
                (not (equal (ninstr st sym tm w) -1)))
           (and (integerp (nop (ninstr st sym tm w) w))
                (<= 0 (nop (ninstr st sym tm w) w))
                (< (nop (ninstr st sym tm w) w) 8)))
  :hints (("Subgoal *1/3''" :in-theory (enable nop ncar)))
  :rule-classes
  ((:type-prescription :corollary
                       (implies (and (force (natp w))
                                     (force (natp tm))
                                     (force (natp st))
                                     (force (< st (expt 2 w)))
                                     (force (natp sym))
                                     (force (< sym 2))
                                     (not (equal (ninstr st sym tm w) -1)))
                                (integerp (nop (ninstr st sym tm w) w))))
   (:linear :corollary
            (implies (and (force (natp w))
                          (force (natp tm))
                          (force (natp st))
                          (force (< st (expt 2 w)))
                          (force (natp sym))
                          (force (< sym 2))
                          (not (equal (ninstr st sym tm w) -1)))
                     (and (<= 0 (nop (ninstr st sym tm w) w))
                          (< (nop (ninstr st sym tm w) w) 8))))))

(defthm nst-out-ninstr
  (implies (and (natp w)
                (natp tm)
                (natp st)
                (< st (expt 2 w))
                (natp sym)
                (< sym 2)
                (not (equal (ninstr st sym tm w) -1)))
           (and (integerp (nst-out (ninstr st sym tm w) w))
                (<= 0 (nst-out (ninstr st sym tm w) w))
                (< (nst-out (ninstr st sym tm w) w) (expt 2 w))))
  :hints (("Subgoal *1/3''" :in-theory (enable nst-out ncar)))
  :rule-classes
  ((:type-prescription :corollary
                       (implies (and (force (natp w))
                                     (force (natp tm))
                                     (force (natp st))
                                     (force (< st (expt 2 w)))
                                     (force (natp sym))
                                     (force (< sym 2))
                                     (not (equal (ninstr st sym tm w) -1)))
                                (integerp (nst-out (ninstr st sym tm w) w))))
   (:linear :corollary
            (implies (and (force (natp w))
                          (force (natp tm))
                          (force (natp st))
                          (force (< st (expt 2 w)))
                          (force (natp sym))
                          (force (< sym 2))
                          (not (equal (ninstr st sym tm w) -1)))
                     (and (<= 0 (nst-out (ninstr st sym tm w) w))
                          (< (nst-out (ninstr st sym tm w) w) (expt 2 w)))))))

(in-theory (disable tapep new-tape1))

; This rather hideous theorem is phrased to rewrite tmi3 into tmi2 terms.
; Specifically, the 0th result of tmi3 is 1 or 0 depending on tmi2, and
; if tmi2 is non-nil then the 2nd and 3rd results of tmi3 are the result of tmi2,
; properly converted.

(defthm tmi3-is-tmi2
  (implies (and (natp w)
                (natp st)
                (< st (expt 2 w))
                (tapep tape)
                (natp tm))
           (and
            (equal (mv-nth 0
                                 (tmi3 st
                                       (mv-nth 0 (convert-tape-to-tapen-pos tape))
                                       (mv-nth 1 (convert-tape-to-tapen-pos tape))
                                       tm w n))
                   (if (tmi2 st tape tm w n) 1 0))

            (implies
             (tmi2 st tape tm w n)
             (and (equal (mv-nth 2 (tmi3 st
                                               (mv-nth 0 (convert-tape-to-tapen-pos tape))
                                               (mv-nth 1 (convert-tape-to-tapen-pos tape))
                                               tm w n))
                         (mv-nth 0 (convert-tape-to-tapen-pos (tmi2 st tape tm w n))))
                  (equal (mv-nth 3 (tmi3 st
                                               (mv-nth 0 (convert-tape-to-tapen-pos tape))
                                               (mv-nth 1 (convert-tape-to-tapen-pos tape))
                                               tm w n))
                         (mv-nth 1 (convert-tape-to-tapen-pos (tmi2 st tape tm w n)))))))))

(defthm tapep-tmi2
  (implies (and (natp w)
                (natp st)
                (< st (expt 2 w))
                (tapep tape)
                (natp tm))
           (or (tapep (tmi2 st tape tm w n))
               (equal (tmi2 st tape tm w n) nil)))
  :rule-classes nil)

#| As I said previously, I am resolutely avoiding needing tmi3!

(defthm tmi3!-is-tmi2
  (implies (and (natp w)
                (natp st)
                (< st (expt 2 w))
                (tapep tape)
                (natp tm))
           (equal (convert-npair-to-tape (tmi3! st (convert-tape-to-npair tape) tm w n))
                  (tmi2 st tape tm w n)))
  :hints (("Goal"
           :use tapep-tmi2
           :in-theory (disable tmi3!)
           :do-not-induct t)))

(in-theory (disable tmi3!))

|#

; -----------------------------------------------------------------

; Now I relate tmi3 all the back to tmi.  I need to establish the following hyps,
; which I discovered by making the three relevant rules force their hyps.

(defthm natp-cdr-assoc-map
  (implies (and (natp-map map)
                (assoc st map))
           (natp (cdr (assoc st map))))
  :rule-classes
  ((:rewrite  :corollary
              (implies (and (natp-map map)
                            (assoc st map))
                       (integerp (cdr (assoc st map)))))
   (:type-prescription :corollary
                       (implies (and (natp-map map)
                                     (assoc st map))
                                (integerp (cdr (assoc st map)))))
   (:linear :corollary
            (implies (and (natp-map map)
                          (assoc st map))
                     (<= 0 (cdr (assoc st map)))))))

(defthm natp-map-renaming-map-top
  (natp-map (renaming-map st tm)))

(defthm assoc-st-renaming-map
  (assoc st (renaming-map st tm)))

(defthm turing1-machinep-tm-to-tm1
  (implies (and (natp w)
                (turing-machinep tm)
                (total-map tm map)
                (natp-map map)
                (<= (max-width tm map) w))
           (turing1-machinep (tm-to-tm1 tm map) w)))

(defthm total-map-renaming-map-top
  (total-map tm (renaming-map st tm)))

(defthm cdr-assoc-renaming-map-upperbound
  (< (cdr (assoc st (renaming-map st tm)))
     (expt 2 (max-width1 (tm-to-tm1 tm (renaming-map st tm))))))


; Wow!  Ok, this is the theorem that shows that there is a way to start tmi3!
; so that it computes the same thing (modulo tape representation conversion) as
; tmi.  In particular, this theorem rewrites tmi3 calls to tmi calls.  The 0th
; result is 1 or 0 depending on whether tmi terminates and the 2nd and 3rd
; results are the corresponding parts of converting tmi's output from tape form
; to tapen and pos form.

(defthm tmi3-is-tmi
  (implies
   (and (symbolp st)
        (tapep tape)
        (turing-machinep tm))
   (and
    (equal
     (mv-nth 0
             (tmi3 (cdr (assoc st (renaming-map st tm)))
                   (mv-nth 0 (convert-tape-to-tapen-pos tape))
                   (mv-nth 1 (convert-tape-to-tapen-pos tape))
                   (ncode (tm-to-tm1 tm (renaming-map st tm))
                          (max-width1 (tm-to-tm1 tm (renaming-map st tm))))
                   (max-width1 (tm-to-tm1 tm (renaming-map st tm)))
                   n))
     (if (tmi st tape tm n) 1 0))
    (implies
     (tmi st tape tm n)
     (and (equal (mv-nth 2
                         (tmi3 (cdr (assoc st (renaming-map st tm)))
                               (mv-nth 0 (convert-tape-to-tapen-pos tape))
                               (mv-nth 1 (convert-tape-to-tapen-pos tape))
                               (ncode (tm-to-tm1 tm (renaming-map st tm))
                                      (max-width1 (tm-to-tm1 tm (renaming-map st tm))))
                               (max-width1 (tm-to-tm1 tm (renaming-map st tm)))
                               n))
                 (mv-nth 0
                         (convert-tape-to-tapen-pos (tmi st tape tm n))))
          (equal (mv-nth 3
                         (tmi3 (cdr (assoc st (renaming-map st tm)))
                               (mv-nth 0 (convert-tape-to-tapen-pos tape))
                               (mv-nth 1 (convert-tape-to-tapen-pos tape))
                               (ncode (tm-to-tm1 tm (renaming-map st tm))
                                      (max-width1 (tm-to-tm1 tm (renaming-map st tm))))
                               (max-width1 (tm-to-tm1 tm (renaming-map st tm)))
                               n))
                 (mv-nth 1
                         (convert-tape-to-tapen-pos (tmi st tape tm n))))))))

  :hints (("Goal" :do-not-induct t :in-theory (disable renaming-map))
          ("Goal''" :use (:instance tapep-tmi2
                                    (st (cdr (assoc st (renaming-map st tm))))
                                    (w (max-width1 (tm-to-tm1 tm (renaming-map st tm))))
                                    (tm (ncode (tm-to-tm1 tm (renaming-map st tm))
                                               (max-width1 (tm-to-tm1 tm (renaming-map st tm)))))))))

