;       A Mechanically Checked Proof of a
; Multiprocessor Result via a Uniprocessor View

;              J Strother Moore
;              Febuary 27, 1998

; This script proves the theorem described in the paper ``A Mechanically
; Checked Proof of a Multiprocessor Result via a Uniprocessor View'', J Moore,
; Formal Methods in System Design, 14(2), March, 1999, pp. 213-228.  See also

; http://www.cs.utexas.edu/users/moore/publications/multi-v-uni.pdf

(in-package "ACL2")

(defun make-mstate (alist mem code)
  (list alist mem code))
(defun pida (s) (nth 0 s))
(defun mem (s) (nth 1 s))
(defun code (s) (nth 2 s))

(defthm pida-make-mstate
  (equal (pida (make-mstate alist mem code)) alist))

(defthm mem-make-mstate
  (equal (mem (make-mstate alist mem code)) mem))

(defthm code-make-mstate
  (equal (code (make-mstate alist mem code)) code))

(in-theory (disable make-mstate pida mem code))

(defun make-ls (pcn regs)
  (list pcn regs))
(defun pcn (ls) (nth 0 ls))
(defun regs (ls) (nth 1 ls))

(defthm pcn-make-ls
  (equal (pcn (make-ls pcn regs)) pcn))

(defthm regs-make-ls
  (equal (regs (make-ls pcn regs)) regs))

(in-theory (disable make-ls pcn regs))

(defmacro modify (s &key
                    (pcn 'nil pcnp)
                    (regs 'nil regsp)
                    (pida 'nil pidap)
                    (mem 'nil memp)
                    (code 'nil codep))

; This is a weird macro which implements an overloaded form of modify.
; (modify s :pcn x) treats s as though it were a local state, while
; (modify s :mem x) treats s as though it were a mstate.

  (if (or pcnp regsp)
      `(make-ls
        ,(if pcnp pcn `(pcn ,s))
        ,(if regsp regs `(regs ,s)))
    `(make-mstate
      ,(if pidap
           pida
         `(pida ,s))
      ,(if memp mem `(mem ,s))
      ,(if codep code `(code ,s)))))

(defun bind (x y alist)
  (cond ((endp alist) (list (cons x y)))
        ((equal x (car (car alist)))
         (cons (cons x y) (cdr alist)))
        (t (cons (car alist) (bind x y (cdr alist))))))

(defun bound? (x alist)
  (cond ((endp alist) nil)
        ((equal x (caar alist)) (car alist))
        (t (bound? x (cdr alist)))))

(defmacro binding (x alist)
  `(cdr (bound? ,x ,alist)))

(defthm bound?-bind
  (equal (bound? var1 (bind var2 val alist))
         (if (equal var1 var2)
             (cons var1 val)
             (bound? var1 alist))))

(defun ls (pid s)
  (binding pid (pida s)))

(defun current-instruction (pid s)
  (nth (pcn (ls pid s)) (code s)))

; The code in question is:

#| ((LOAD OLD CTR)
    (INCR NEW OLD)
    (CAS CTR OLD NEW)
    (BR NEW 1)
    (JUMP 0))|#

(defun load-step (ins ls mem)
  (let ((reg (cadr ins))    ; (LOAD reg loc):   reg := mem(loc)
        (loc (caddr ins)))
    (mv (modify ls
                :pcn (1+ (pcn ls))
                :regs (bind reg (binding loc mem) (regs ls)))
        mem)))

(defun incr-step (ins ls mem)
  (let ((reg1 (cadr ins))    ; (INCR reg1 reg2): reg1 := reg2+1
        (reg2 (caddr ins)))
    (mv (modify ls
                :pcn (1+ (pcn ls))
                :regs (bind reg1
                            (1+ (binding reg2 (regs ls)))
                            (regs ls)))
        mem)))

(defun cas-step (ins ls mem)
; (CAS loc reg1 reg2): If mem(loc)=reg1
;                         then mem(loc):=reg2 ; reg2:=nil
;                         else reg1:=mem(loc) ; reg2:=t
  (let ((loc (cadr ins))
        (reg1 (caddr ins))
        (reg2 (cadddr ins)))
    (cond
     ((equal (binding reg1 (regs ls))
             (binding loc mem))
      (mv (modify ls
                  :pcn (1+ (pcn ls))
                  :regs (bind reg2 nil (regs ls)))
          (bind loc (binding reg2 (regs ls)) mem)))
     (t (mv (modify ls
                    :pcn (1+ (pcn ls))
                    :regs (bind reg1 (binding loc mem)
                                (bind reg2 t (regs ls))))
            mem)))))

(defun br-step (ins ls mem)
  (let ((reg (cadr ins)) ; (BR reg adr): if reg, go to adr
        (adr (caddr ins)))
    (mv (modify ls
                :pcn (if (binding reg (regs ls))
                        adr
                      (1+ (pcn ls))))
        mem)))

(defun jump-step (ins ls mem)
  (let ((adr (cadr ins)) ; (JUMP adr):  goto to adr
        )
    (mv (modify ls
                :pcn adr)
        mem)))

(defun execute (pid ins s)
  (let ((ls (ls pid s)))
    (mv-let (new-ls new-mem)
            (case (car ins)
              (load   (load-step   ins ls (mem s)))
              (incr   (incr-step   ins ls (mem s)))
              (cas (cas-step ins ls (mem s)))
              (br  (br-step  ins ls (mem s)))
              (jump   (jump-step   ins ls (mem s)))
              (otherwise (mv ls (mem s))))
            (modify s
                    :pida
                    (bind pid new-ls (pida s))
                    :mem new-mem))))

(defun mstep (pid s)
  (cond ((bound? pid (pida s))
         (execute pid
                  (current-instruction pid s)
                  s))
        (t s)))

(defun mrun (oracle s)
  (if (endp oracle)
      s
    (mrun (cdr oracle)
          (mstep (car oracle) s))))

; We now develop the basic rules for dealing with mrun.

(defthm multrun-opener
  (equal (mrun (cons pid L) s)
         (mrun L (mstep pid s)))
  :hints (("goal" :in-theory (disable mstep))))

(defthm mstep-opener
  (implies (consp (current-instruction pid s))
           (equal (mstep pid s)
                  (if (bound? pid (pida s))
                      (execute pid
                               (current-instruction pid s)
                               s)
                    s))))

(in-theory (disable mstep))

(defthm mrun-append
  (equal (mrun (append L1 L2) s)
         (mrun L2 (mrun L1 s))))

(defthm code-mstep
  (equal (code (mstep pid s))
         (code s))
  :hints (("Goal" :in-theory (enable mstep))))

(defthm code-mrun
  (equal (code (mrun L s))
         (code s)))

(defthm bound?-mstep
  (iff (bound? pid (pida (mstep active-pid s)))
       (bound? pid (pida s)))
  :hints (("Goal" :in-theory (enable mstep))))

(defthm bound?-mrun
  (iff (bound? pid (pida (mrun L s)))
       (bound? pid (pida s))))

(defthm bound?-pida
  (implies (not (member-equal pid L))
           (equal (bound? pid (pida (mrun L s)))
                  (bound? pid (pida s))))
  :hints (("Goal" :in-theory (enable mstep))))

; ----------------------------------------------------------------------------

; We now develop the single processor view of the system.

(defun make-ustate (uls umem ucode)
  (list uls umem ucode))
(defun uls (us) (nth 0 us))
(defun umem (us) (nth 1 us))
(defun ucode (us) (nth 2 us))

(defthm uls-make-ustate
  (equal (uls (make-ustate uls umem ucode)) uls))
(defthm umem-make-ustate
  (equal (umem (make-ustate uls umem ucode)) umem))
(defthm ucode-make-ustate
  (equal (ucode (make-ustate uls umem ucode)) ucode))
(in-theory (disable make-ustate uls umem ucode))

(defun current-uinstruction (us)
  (nth (pcn (uls us)) (ucode us)))

(defun uexecute (ins us actual-mem)
  (LET
    ((LS (uls us)))
    (MV-LET (NEW-LS NEW-MEM)
            (CASE (CAR INS)
              (LOAD (LOAD-STEP INS LS actual-mem))
              (INCR (INCR-STEP INS LS actual-mem))
              (CAS (CAS-STEP INS LS actual-mem))
              (BR (BR-STEP INS LS actual-mem))
              (JUMP (JUMP-STEP INS LS actual-mem))
              (OTHERWISE (MV LS actual-mem)))
            (make-ustate new-ls
                         new-mem
                         (ucode us)))))

(defun ustep (us actual-mem)
  (uexecute (current-uinstruction us) us actual-mem))

(defun urun (us M)
  (cond ((endp M) us)
        ((endp (cdr M))
         (make-ustate (uls us)
                      (car M)
                      (ucode us)))
        (t (urun (ustep us (car M)) (cdr M)))))

; Originally, I defined (ascendingp M) to just check that the sequence
; of 'ctr bindings was weakly ascending.  That was insufficient to
; make our main theorem a theorem!  Imagine that ctr is fixed in
; M1-M6.  When the CAS is executed, it will do the write,
; increasing the CTR, say on the step applied to M3.  But the step
; applied to M4 will use M4, not the new memory!  The ascending
; predicate must be stronger.

(defthm urun-opener
  (equal (urun us (cons mem M))
         (if (endp M)
             (make-ustate (uls us) mem (ucode us))
             (urun (ustep us mem) M)))
  :hints (("goal" :in-theory (disable ustep))))

(defthm ustep-opener
  (implies (consp (current-uinstruction us))
           (equal (ustep us mem)
                  (uexecute
                           (current-uinstruction us)
                           us
                           mem))))
(in-theory (disable ustep))

(defun proj (pid s)
  (make-ustate (ls pid s)
               (mem s)
               (code s)))

(defun initial-subsequence (L pid)
  (cond ((endp L) nil)
        ((equal (car L) pid) nil)
        (t (cons (car L) (initial-subsequence (cdr L) pid)))))

(defthm acl2-count-member-equal
  (implies (member-equal pid L)
           (<= (acl2-count (member-equal pid L))
               (acl2-count L)))
  :rule-classes :linear)

(defun partition-oracle (pid L)
  (cond ((member-equal pid L)
         (cons (initial-subsequence L pid)
               (partition-oracle pid (cdr (member-equal pid L)))))
        (t (list L))))

(defun new-oracle (pid s partitions)
  (cond ((endp partitions) nil)
        (t (cons (mem (mrun (car partitions) s))
                 (new-oracle pid
                             (mstep pid (mrun (car partitions) s))
                             (cdr partitions))))))

(defun proj-oracle (pid s L)
  (new-oracle pid s (partition-oracle pid L)))

(defthm new-oracle-opener
  (equal (new-oracle pid s (cons part L))
         (cons (mem (mrun part s))
               (new-oracle pid
                           (mstep pid (mrun part s))
                           L))))

(defun mrun-is-urun-hint (pid L s)
  (cond ((member-equal pid L)
         (mrun-is-urun-hint
          pid
          (cdr (member-equal pid L))
          (mstep pid (mrun (initial-subsequence L pid) s))))
        (t s)))

(defthm consp-new-oracle
  (iff (consp (new-oracle pid s L))
       (consp L)))

(defthm initial-subsequence-elim
  (implies (member-equal pid L)
           (equal (append (initial-subsequence L pid)
                          (cons pid (cdr (member-equal pid L))))
                  L))
  :rule-classes :elim)

(defthm ustep-is-mstep
  (implies (and (not (member-equal pid L))
                (bound? pid (pida s))
                (equal code (code s)))
           (equal (ustep (make-ustate (binding pid (pida s))
                                      (mem s)
                                      code)
                         (mem (mrun L s)))
                  (make-ustate
                   (binding pid
                            (pida
                             (mstep pid (mrun L s))))
                   (mem (mstep pid (mrun L s)))
                   (code s))))
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories (enable ustep mstep)
                                               '(load-step
                                                 incr-step
                                                 cas-step
                                                 br-step
                                                 jump-step)))))

(defthm member-equal-initial-subsequence
  (not (member-equal pid (initial-subsequence L pid))))

(defmacro processp (pid s)
  `(bound? ,pid (pida ,s)))

(defthm commutative-diagram
  (implies (processp pid s)
           (equal (urun (proj pid s)
                        (proj-oracle pid s L))
                  (proj pid (mrun L s))))
  :hints (("Goal" :induct (mrun-is-urun-hint pid L s))))

(defthm umem-proj
  (equal (umem (proj pid s)) (mem s)))

(defthm commutative-diagram-corollary
  (implies (processp pid s)
           (equal (mem (mrun L s))
                  (umem
                   (urun (proj pid s)
                         (proj-oracle pid s L)))))
  :hints (("Goal" :in-theory (disable proj proj-oracle))))

(in-theory (disable commutative-diagram-corollary))

; if you enable this rule, (disable ustep-is-mstep commutative-diagram)!

(defthm len-new-oracle
  (equal (len (new-oracle pid s L))
         (len L)))

(defthm uls-proj (equal (uls (proj pid s)) (ls pid s)))

(defthm ucode-proj (equal (ucode (proj pid s)) (code s)))

; ----------------------------------------------------------------------------

; We now develop the Preorder Projection Theorem.

(encapsulate
 ((P (s) t)
  (R (mem1 mem2) t))
 (local
  (defun P (s) (declare (ignore s)) t))
 (local
  (defun R (mem1 mem2) (declare (ignore mem1 mem2)) t))
 (defthm R-reflexive
   (implies (P s)
            (R (mem s) (mem s))))
 (defthm R-transitive
   (implies (and (R mem1 mem2)
                 (R mem2 mem3))
            (R mem1 mem3)))
 (defthm P-mstep
   (implies (P s) (P (mstep pid s))))
 (defthm R-mstep
   (implies (P s)
            (R (mem s) (mem (mstep pid s))))))

(defun R-urunp (us M)
  (declare (xargs :measure (acl2-count M)))
  (cond ((endp M) t)
        ((R (umem us) (car M))
         (R-urunp (ustep us (car M))
                  (cdr M)))
        (t nil)))

(defthm R-urunp-opener
  (equal (R-urunp us (cons mem M))
         (and (R (umem us) mem)
              (R-urunp (ustep us mem) M))))

(defthm P-mrun
  (implies (P s) (P (mrun L s))))

(defthm R-mrun
  (implies (P s)
           (R (mem s) (mem (mrun L s))))
  :hints (("Subgoal *1/3"
           :use
           (:instance R-mstep
                      (pid (car L))
                      (s s))
           :in-theory (disable R-mstep))))

(defthm preorder-projection
  (implies (and (P s)
                (bound? pid (pida s)))
           (R-urunp (proj pid s) (proj-oracle pid s L)))
  :hints (("Goal" :induct (mrun-is-urun-hint pid L s))))

; The above theorem is interesting because it lets us conclude
; something about a urun of a projection from an analogous thing about
; a mrun.  I show how to use this in the example proof below.
; -----------------------------------------------------------------------------

; Utilities about occurrences and oracles...

(defun occurrences (pid L)
  (cond ((endp L) 0)
        ((equal pid (car L))
         (1+ (occurrences pid (cdr L))))
        (t (occurrences pid (cdr L)))))

(defthm equal-len-n
  (implies (and (syntaxp (quotep n))
                (< 0 n))
           (equal (equal (len x) n)
                  (and (consp x)
                       (equal (len (cdr x)) (1- n))))))

(in-theory (disable equal-len-n))

(defthm equal-len-0
  (equal (equal (len x) 0) (endp x)))

(defthm alt-occurrences
  (equal (occurrences pid L)
         (if (member-equal pid L)
             (1+ (occurrences pid (cdr (member-equal pid L))))
           0))
  :rule-classes
  ((:definition :clique (occurrences)
                :controller-alist ((occurrences nil t)))))

(defthm occurrences-non-0-implies-member-equal
  (implies (< 0 (occurrences pid L))
           (member-equal pid L)))

(defthm len-partition-oracle
  (equal (len (partition-oracle pid L))
         (1+ (occurrences pid L))))

(defthm len-proj-oracle
  (equal (len (proj-oracle pid s L))
         (1+ (occurrences pid L))))

; -----------------------------------------------------------------------------

; We now develop the proof of the program per se.

(defmacro ctr (s)
  `(binding 'ctr (mem ,s)))

(defun good-local-statep (ls)
  (and (integerp (pcn ls))
       (<= 0 (pcn ls))
       (<= (pcn ls) 4)
       (integerp (binding 'old (regs ls)))
       (implies (equal (pcn ls) 2)
                (equal (1+ (binding 'old (regs ls)))
                       (binding 'new (regs ls))))))

(defun pida-invariantp (alist)
  (cond ((endp alist)
         (equal alist nil))
        (t (and (consp (car alist))
                (good-local-statep (cdar alist))
                (pida-invariantp (cdr alist))))))

(defun good-statep (s)
  (and (pida-invariantp (pida s))
       (integerp (ctr s))
       (equal (code s)
              '((LOAD OLD CTR)
                (INCR NEW OLD)
                (CAS CTR OLD NEW)
                (BR NEW 1)
                (JUMP 0)))))

; See the essay at the bottom for some explanation of the next two
; lemmas.

(defthm good-local-statep!
  (implies (good-local-statep ls)
           (and (integerp (pcn ls))
                (<= 0 (pcn ls))
                (<= (pcn ls) 4)
                (integerp (binding 'old (regs ls)))
                (implies (equal (pcn ls) 2)
                         (equal (1+ (binding 'old (regs ls)))
                                (binding 'new (regs ls))))))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (good-local-statep ls)
             (integerp (pcn ls))))
   (:type-prescription
    :corollary
    (implies (good-local-statep ls)
             (integerp (binding 'old (regs ls)))))
   (:rewrite
    :corollary
    (implies (and (good-local-statep ls)
                  (equal (pcn ls) 2))
             (equal (binding 'new (regs ls)) ; note orientation
                    (1+ (binding 'old (regs ls))))))
   (:linear
    :corollary
    (implies (good-local-statep ls)
             (and (<= 0 (pcn ls))
                  (<= (pcn ls) 4))))))

(defthm pida-invariantp!
  (implies (and (pida-invariantp alist)
                (bound? pid alist))
           (good-local-statep (binding pid alist)))
  :rule-classes :type-prescription)

(defthm pida-invariantp-bind
  (implies (pida-invariantp alist)
           (equal (pida-invariantp (bind pid ls alist))
                  (good-local-statep ls))))

; The following theorem was not needed by ACL2 Version 1.9, which existed in
; 1998 when this proof was first done.  The reason is that Version 1.9
; opened recursive functions more agressively than subsequent ACL2 releases.

; Basically (nth pcn '((LOAD OLD CTR) ...)) is the expansion of the
; (current-instruction s) under our good-statep hypothesis.  When trying to
; prove that good-statep is preserved by mstep, one must consider which
; instruction mstep is executing.  When, for example, executing a LOAD into
; OLD, we must be able to show that the memory location being laoded is an
; integer.  But the only such knowledge about mem is for CTR.  Thus, the only
; legal LOAD to OLD is (LOAD OLD CTR).  Any other LOAD to OLD would break the
; good-statep invariant.  So the only way to prove the invariance of
; good-statep is to make sure that each of the five instructions in our program
; preserves it.  Thus rule forces ACL2 to case split on the pcn and consider
; each of the possbilities.

(defthm pcn-case-split
  (equal (nth pcn
              '((LOAD OLD CTR)     ; 0
                (INCR NEW OLD)     ; 1
                (CAS CTR OLD NEW)  ; 2
                (BR NEW 1)         ; 3
                (JUMP 0)))         ; 4
         (case pcn
           (0 '(LOAD OLD CTR))
           (1 '(INCR NEW OLD))
           (2 '(CAS CTR OLD NEW))
           (3 '(BR NEW 1))
           (4 '(JUMP 0))
           (otherwise (if (zp pcn)
                          '(LOAD OLD CTR)
                          nil)))))

; So it is easy to see now that good-statep is preserved by mstep,

(defthm good-statep-mstep
  (implies (good-statep s)
           (good-statep (mstep pid s)))
  :hints
  (("Goal" :in-theory (enable mstep))))

; and hence by mrun.

(defthm good-statep-mrun
  (implies (good-statep s)
           (good-statep (mrun L s))))

; Now we define the predicate on M that insures that memory values are
; legal.  They dominate the value seen by the selected process.

(defun ascendingp (us M)
  (declare (xargs :measure (acl2-count M)))
  (cond ((endp M) t)
        (t (and (integerp (binding 'ctr (car M)))
                (<= (binding 'ctr (umem us))
                    (binding 'ctr (car M)))
                (ascendingp (ustep us (car M)) (cdr M))))))

; To prove that by our preorder-projection we really just need two
; facts:

(defthm ctr-<=-ctr-mstep
  (implies (good-statep s)
           (<= (ctr s) (ctr (mstep pid s))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable mstep))))

(defthm integerp-ctr-mstep
  (implies (good-statep s)
           (integerp (ctr (mstep pid s))))
  :hints (("Goal" :in-theory (enable mstep)))
  :rule-classes (:rewrite :type-prescription))

; So the projection property tells us that the projected state/oracle
; ascend.

(defthm preorder-projection-corollary
  (implies (and (good-statep s)
                (processp pid s))
           (ascendingp (proj pid s)
                       (proj-oracle pid s L)))
  :hints (("Goal"
           :use
           ((:functional-instance
             preorder-projection
             (P good-statep)
             (R (lambda (mem1 mem2)
                  (and (integerp (binding 'ctr mem2))
                       (<= (binding 'ctr mem1) (binding 'ctr mem2)))))
             (R-urunp ascendingp))))))

(defthm ascendingp-opener
  (equal (ascendingp us (cons mem M))
         (and (integerp (binding 'ctr mem))
              (<= (binding 'ctr (umem us))
                  (binding 'ctr mem))
              (ascendingp (ustep us mem) M)))
  :hints (("goal" :in-theory (disable ustep))))

(defthm crux-lemma
  (let ((M (list* M1 M2 M3 M4 M5 M6 M7 end)))
    (implies (and (endp end)
                  (ascendingp us M)
                  (good-local-statep (uls us))
                  (equal (ucode us)
                         '((LOAD OLD CTR)
                           (INCR NEW OLD)
                           (CAS CTR OLD NEW)
                           (BR NEW 1)
                           (JUMP 0))))
             (< (binding 'ctr (umem us)) (binding 'ctr (umem (urun us M))))))
  :rule-classes nil
  :hints
  (("Goal" :cases ((equal (pcn (uls us)) 0)
                   (equal (pcn (uls us)) 1)
                   (equal (pcn (uls us)) 2)
                   (equal (pcn (uls us)) 3)
                   (equal (pcn (uls us)) 4)))))

(defun good-u-statep (us)
  (and (good-local-statep (uls us))
       (equal (ucode us)
              '((LOAD OLD CTR)
                (INCR NEW OLD)
                (CAS CTR OLD NEW)
                (BR NEW 1)
                (JUMP 0)))))

(defthm crux
  (implies (and (equal (len M) 7)
                (ascendingp us M)
                (good-u-statep us))
           (< (binding 'ctr (umem us))
              (binding 'ctr (umem (urun us M)))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (equal (len M) 7)
                           (equal mem (umem us))
                           (ascendingp us M)
                           (good-u-statep us))
                      (< (binding 'ctr mem)
                         (binding 'ctr (umem (urun us M)))))))
  :hints (("Goal" :do-not-induct t
           :use
           (:instance crux-lemma
                      (m1 (car M))
                      (m2 (cadr M))
                      (m3 (caddr M))
                      (m4 (cadddr M))
                      (m5 (car (cddddr M)))
                      (m6 (cadr (cddddr M)))
                      (m7 (caddr (cddddr M)))
                      (end (cdddr (cddddr M))))
           :in-theory
           (set-difference-theories
            (enable equal-len-n)
            '(len umem ascendingp good-local-statep uls
                   ucode urun
                   urun-opener
                   ascendingp-opener)))))

(defthm lemma
  (implies (and (good-statep s)
                (processp pid s)
                (equal 6 (occurrences pid L)))
           (< (ctr s)
              (ctr (mrun L s))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory
           (union-theories '(commutative-diagram-corollary)
                           (disable proj proj-oracle
                                    good-local-statep
                                    ustep-is-mstep
                                    commutative-diagram)))))

; -----------------------------------------------------------------------------

; Essay on good-local-statep! and pida-invariantp!

; Our goal formulas will have a hypothesis of (good-statep s).  This
; will expand to (pida-invariantp (pida s)).  From this we will have
; to be able to conclude such things as (integerp (pcn (binding pid
; (pida s)))).  How do we arrange for this to happen?

; Since the integerp fact is "type-like" we build it in at the
; :type-prescription level.  The lemma good-local-statep! causes us to
; backchain from (integerp (pcn ...)) to (good-local-statep ls).  But in
; general we won't have (good-local-statep ls) in the goal.  Instead we
; have to continue to backchain to (pida-invariantp ...).
; Furthermore, we have to do this backchain at the :type-prescription
; level for it to have the desired effect.

; We could reduce these two lemmas to one, eliminating the talk about
; good-local-statep and going directly from pida-invariantp down to
; integerp.  I chose this way because it is more illustrative of a
; hierarchical decomposition.

; -----------------------------------------------------------------------------

; I now finish the proof off.  We're here concerned with the Pigeon
; Hold Principle and the problem that the actual oracle may contain
; more than 6 occurrences of pid.

(defun cardinality (x)
  (if (endp x)
      0
    (if (member-equal (car x) (cdr x))
        (cardinality (cdr x))
      (1+ (cardinality (cdr x))))))

(defun delete-all (x L)
  (cond ((endp L) L)
        ((equal x (car L)) (delete-all x (cdr L)))
        (t (cons (car L) (delete-all x (cdr L))))))

(defthm acl2-count-delete-all
  (<= (acl2-count (delete-all x L))
      (acl2-count L))
  :rule-classes :linear)

(defthm not-member-equal-delete-all
  (implies (not (member-equal x L))
           (equal (delete-all x L) L)))

(defthm member-equal-delete-all
  (iff (member-equal x (delete-all y L))
       (if (equal x y)
           nil
         (member-equal x L))))

(defun choose (n L)
  (cond ((endp L) nil)
        ((<= n (occurrences (car L) (cdr L))) (car L))
        (t (choose n
                   (delete-all (car L) (cdr L))))))

(defthm cardinality<=len
  (<= (cardinality x) (len x))
  :rule-classes :linear)

(defun weird-induction-hint (L)
  (cond ((endp L) t)
        (t (weird-induction-hint (delete-all (car L) (cdr L))))))

(in-theory (disable initial-subsequence-elim))

(defthm cardinality-delete-all
  (equal (cardinality (delete-all x L))
         (if (member-equal x L)
             (1- (cardinality L))
           (cardinality L))))

(defthm alt-cardinality
  (equal (cardinality L)
         (if (endp L)
             0
           (1+ (cardinality (delete-all (car L) (cdr L))))))
  :rule-classes
  ((:definition :clique (cardinality)
                :controller-alist ((cardinality t)))))

(in-theory (disable cardinality-delete-all))

(defthm len-delete-all
  (equal (len (delete-all x L))
         (- (len L) (occurrences x L))))

(defthm occurrence-delete-all
  (equal (occurrences x (delete-all y L))
         (if (equal x y)
             0
           (occurrences x L))))

; Here is the crucial fact:

(defthm pigeon-hole-principle
  (implies (and (integerp i)
                (<= 0 i)
                (< (* i (cardinality L)) (len L)))
           (< i (occurrences (choose i L) L)))
  :rule-classes :linear)

; Given (< (* 5 (cardinality L)) (len L)) we know (<= 6 (occurrences
; (choose 5 L) L)).  Thus we can partition L into two bits:

(defun first-n-occurrences (n x L)
  (cond ((zp n) nil)
        ((endp L) L)
        ((equal x (car L))
         (cons (car L) (first-n-occurrences (1- n) x (cdr L))))
        (t (cons (car L) (first-n-occurrences n x (cdr L))))))

(defun all-but-first-n-occurrences (n x L)
  (cond ((zp n) L)
        ((endp L) L)
        ((equal x (car L))
         (all-but-first-n-occurrences (1- n) x (cdr L)))
        (t (all-but-first-n-occurrences n x (cdr L)))))

(defthm partition-after-first-n
  (implies (<= n (occurrences x L))
           (equal L (append (first-n-occurrences n x L)
                            (all-but-first-n-occurrences n x L))))
  :rule-classes nil)

; Of course, if everything in L is bound in (pida s), then choose
; returns something bound in (pida s).

(defun all-bound? (L alist)
  (cond ((endp L) t)
        (t (and (bound? (car L) alist)
                (all-bound? (cdr L) alist)))))


(defthm all-bound?-implies-choose-bound
  (implies (and (all-bound? L alist)
                (integerp n)
                (<= 0 n)
                (< n (occurrences (choose n L) L)))
           (bound? (choose n L) alist)))

; Given that, we can apply lemma to get past the first 6
; steps of the chosen pid, and then appeal to the fact

(defthm pida-invariantp-mstep
  (implies (good-statep s)
           (pida-invariantp (pida (mstep pid s))))
  :hints (("Goal" :in-theory (disable good-statep-mstep)
                  :use good-statep-mstep)))

(defthm ctr-<=-ctr-mrun
  (implies (good-statep s)
           (<= (ctr s) (ctr (mrun L s))))
  :rule-classes :linear)

; Finally, to appeal to lemma we need to know:

(defthm occurrences-first-n-occurrences
  (implies (and (integerp n)
                (<= 0 n)
                (<= n (occurrences x L)))
           (equal (occurrences x (first-n-occurrences n x L))
                  n)))

(defun every-element-a-processp (L s)
  (all-bound? L (pida s)))

; So here is our main goal, stated simply:

(defthm theorem
  (implies (and (good-statep s)
                (every-element-a-processp L s)
                (< (* 5 (cardinality L)) (len L)))
           (< (ctr s) (ctr (mrun L s))))
  :hints (("Goal"
           :in-theory (disable good-statep)
           :use ((:instance lemma (s s)
                              (pid (choose 5 L))
                              (L (first-n-occurrences 6 (choose 5 L) L)))
                 (:instance partition-after-first-n
                            (n 6)
                            (x (choose 5 L))
                            (L L))))))

; -----------------------------------------------------------------------------
; I finish by proving that good states exist.  In particular, the
; function n-processor-s0 constructs one for n processors,
; provided you give it a memory with a integerp ctr.

(defun pida0 (n)
  (cond ((zp n) nil)
        (t (cons (cons n (make-ls 0 '((old . 0)(new . 0))))
                 (pida0 (1- n))))))

(defun n-processor-s0 (n mem)
  (make-mstate (pida0 n)
               mem
               '((LOAD OLD CTR)
                 (INCR NEW OLD)
                 (CAS CTR OLD NEW)
                 (BR NEW 1)
                 (JUMP 0))))

(defthm good-states-exist
  (implies (integerp (binding 'ctr mem))
           (good-statep (n-processor-s0 n mem))))


