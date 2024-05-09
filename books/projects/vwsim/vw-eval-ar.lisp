
; vw-eval-ar.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; Started in August, 2020.  Edited many times.  Example usage
; at the end of this file.

; (ld "vw-eval-ar.lisp" :ld-pre-eval-print t)
; (certify-book "vw-eval-ar.lisp" ?)
; (include-book "vw-eval-ar.lisp")

(in-package "ACL2")

(set-inhibit-warnings "Double-rewrite")
(set-inhibit-warnings "Non-rec")

(include-book "std/util/bstar" :dir :system)
(include-book "nth-lemmas")
(include-book "constants")
(include-book "arith-fp")
(include-book "num")
(include-book "names-and-indices")
(include-book "records")
;; (include-book "vw-eval-fns")
(include-book "vw-eval")
;; (include-book "sra-matrix-defuns")
(include-book "rtime")
(include-book "projects/apply/top" :dir :system)

(local ; speeds up vw-eval-term-nat-alistp-all-subterms
 (in-theory (disable member-equal)))

(defstobj rec
  ;; ar stores a mapping of variables to their corresponding history
  ;; of values. This record contains the result of the simulation.
  #-rec-stobj
  (rec-ar :type
          (array #-simple-vectors (satisfies nump) #+simple-vectors t
                 (0))
          :initially 0
          :resizable t)
  #+rec-stobj
  (rec-ar :type
          (array #-simple-vectors double-float #+simple-vectors t
                 (0))
          :initially 0.0d0
          :resizable t)
  :renaming
  ((rec-ar-length arl))
  :inline t
  :non-memoizable t)

(defun-inline ar-index-guard (i cycle nvars)
  (declare (type (unsigned-byte 60) i cycle nvars))
  (< (+ i (* cycle nvars))
     *2^60*))

(defun ar-index-simple (i cycle nvars)

; Warning: Keep this in sync with ar-index-simple.

; Note: We could eliminate this function and just inline its code in function
; ar-index.  But it's only used in the :logic part of an mbe call there, so it
; seems prudent to keep ar-index-simple. around so that we can disable it.  Of
; course, another option is to remove the mbe in ar-index and just use the
; :exec version there, but it seems a bit sad to clutter the body with u60
; calls even though they are likely removed very quickly by the prover (see
; :DOC guard-holders).

  (declare (type rational i cycle nvars))
  (+ i (* cycle nvars)))

(defun-inline ar-index (i cycle nvars)
; Warning: Keep this in sync with ar-index-simple.
  (declare (type (unsigned-byte 60) i cycle nvars)
           (xargs :guard (ar-index-guard i cycle nvars)))
  (mbe :logic (nfix (ar-index-simple i cycle nvars))
       :exec (u60 (+ i (u60 (* cycle nvars))))))

(defthm ar-index-is-ar-index-simple
; This might not be needed if instead we just keep ar-index enabled.
  (equal (ar-index i cycle nvars)
         (nfix (ar-index-simple i cycle nvars))))

(in-theory (disable ar-index))

(defun-inline ari (i cycle nvars rec)
  (declare (type (unsigned-byte 60) i cycle nvars)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec)
           (xargs :stobjs rec
                  :guard (and (< (ar-index-simple i cycle nvars)
                                 (arl rec))
                              (<= (arl rec) *2^60*))))
  (rec-ari (ar-index i cycle nvars) rec))

(defun-inline !ari (i cycle nvars val rec)
  (declare (type (unsigned-byte 60) i cycle nvars)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec)
           (xargs :stobjs rec
                  :guard (and (< (ar-index-simple i cycle nvars)
                                 (arl rec))
                              (<= (arl rec) *2^60*)
                              (rationalp val))))
  (update-rec-ari (ar-index i cycle nvars) val rec))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                resize-ar))

(defun resize-ar (ncycles nvars rec)
  (declare (type (unsigned-byte 60) ncycles nvars)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec)
           (xargs :stobjs rec
                  :guard (< (ar-index-simple 0 ncycles nvars)
                            *2^60*)))
  (resize-rec-ar (u60 (* ncycles nvars)) rec))

;; We prove some theorems about the stv array accessors, updaters, and
;; recognizers and then disable their definitions.

(local
 (defthm rationalp-ari-lemma
   (implies (and (rec-arp ar)
                 (natp k)
                 (< k (len ar)))
            (rationalp (nth k ar)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm rationalp-ari

  ;; We originally make this only a type-prescription rule since we didn't
  ;; expect the rationalp call to match very often.  But since hypotheses of
  ;; type-prescription rules are relieved only with type-set reasoning, we
  ;; force them so that the full prover can deal with them eventually.  We
  ;; force them individually, rather than putting a single force around the
  ;; (and ...), so that if one or two of them is successfully relieved then
  ;; there's no need to reconsider those at a forcing round.

  ;; But we now also make it a rewrite rule, since that was necessary for the
  ;; proofs of recp-xp-rec-updates and st-valsp-init-st-vals (at least).  The
  ;; force calls may not be necessary for the rewrite rule, especially for the
  ;; last hypothesis, but as far as we know they aren't harmful, so we create
  ;; both rules from the same formula.

  (implies (and (recp rec)
                (force (natp i))
                (force (natp cycle))
                (force (natp nvars))
                (force (< (ar-index i cycle nvars)
                          (arl rec))))
           (rationalp (ari i cycle nvars rec)))
  :rule-classes (:type-prescription :rewrite))

(local
 (defthm rec-arp-!nth
   (implies (and (rec-arp a)
                 (<= l (len a))
                 (rationalp v))
            (rec-arp (!nth l v a)))
   :hints
   (("Goal" :in-theory (enable nth-theory-defuns)))))

(defthm recp-!ari
  (implies (and (recp rec)
                (force (natp i))
                (force (natp cycle))
                (force (natp nvars))
                (force ; <=, since array can be extended by one
                 (<= (ar-index i cycle nvars)
                     (arl rec)))
                (force (rationalp v)))
           (recp (!ari i cycle nvars v rec)))
  :hints (("Goal" :in-theory (enable nth-theory-defuns))))

(defthmd ar-index-equality-reduction

; This lemma is not needed for the proof of ari-!ari if we give the indicated
; :cases and :nonlinearp hints with ari-!ari.  But this lemma is helpful for
; !ari-!ari-different-addresses, so we go ahead and prove it here.  It's a nice
; result anyhow about ar-index (or to be more precise, about its expansions).

; It's disabled by default -- maybe not important, but seems reasonable both
; because it's hung on EQUAL and so that we see, via enables, where it's used.

  (implies (and (natp i1)
                (natp cycle1)
                (natp i2)
                (natp cycle2)
                (natp nvars)
                (< i1 nvars)
                (< i2 nvars))
           (equal (equal (+ i1 (* cycle1 nvars))
                         (+ i2 (* cycle2 nvars)))
                  (and (equal i1 i2)
                       (equal cycle1 cycle2))))
  :hints (("Goal"
           :cases ((< cycle1 cycle2)
                   (< cycle2 cycle1))
           :nonlinearp t)))

(defthm ari-!ari
  ;; Similar to NTH-!NTH lemma
  (implies (and (force (natp i1))
                (force (natp cycle1))
                (force (natp nvars))
                (force (natp i2))
                (force (natp cycle2))
                (force (< i1 nvars))
                (force (< i2 nvars)))
           (equal (ari i1 cycle1 nvars
                       (!ari i2 cycle2 nvars val rec))
                  (if (and (equal i1 i2)
                           (equal cycle1 cycle2))
                      val
                    (ari i1 cycle1 nvars rec))))
  :hints
  (("Goal"
    :in-theory (enable nth-theory-lemmas
                       ar-index-equality-reduction))))

(defthm !ari-ari
  (implies (force (< (ar-index i cycle nvars)
                     (arl rec)))
           (equal (!ari i cycle nvars (ari i cycle nvars rec) rec)
                  rec))
  :hints
  ;; By enabling NTH and !NTH, we are able to "dig down"
  ;; to the interior accesses so we can apply !NTH-NTH,
  ;; and thus, we don't need to know (RECP rec).
  (("Goal" :in-theory (enable !nth nth
                              nth-theory-lemmas))))

(defthm !ari-!ari-same-address
  (implies (and (equal i1 i2)
                (equal cycle1 cycle2))
           (equal (!ari i1 cycle1 nvars v
                        (!ari i2 cycle2 nvars v rec))
                  (!ari i1 cycle1 nvars v rec)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm !ari-!ari-different-addresses
  ;; Should we have some SYNTAXP check to order by address?
  (implies (and (force (natp i1))
                (force (natp cycle))
                (force (natp nvars))
                (force (natp i2))
                (force (< i1 nvars))
                (force (< i2 nvars))
                (not (equal i1 i2)))
           (equal (!ari i1 cycle nvars v1
                        (!ari i2 cycle nvars v2 rec))
                  (!ari i2 cycle nvars v2
                        (!ari i1 cycle nvars v1 rec))))
  :hints
  (("Goal"
    :in-theory (enable nth-theory-lemmas
                       ar-index-equality-reduction))))

(defthm arl-!ari
  (implies (and ; (recp rec)
            (force (< (ar-index i cycle nvars) (arl rec))))
           (equal (arl (!ari i cycle nvars v rec))
                  (arl rec)))
  :hints
  ;; By enabling NTH and !NTH, we are able to "dig down"
  ;; to the interior accesses so we can apply !NTH-NTH,
  ;; and thus, we don't need to know (RECP rec).
  (("Goal" :in-theory (enable !nth nth
                              nth-theory-lemmas))))

(defthm ar-length-is-resize
  (implies (and (force (natp ncycles))
                (force (natp nvars)))
           (equal (arl (resize-ar ncycles nvars rec))
                  (* ncycles nvars)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm rec-arp-resize-list
  (implies (and (rec-arp a)
                (rationalp v))
           (rec-arp (resize-list a new-size v))))

(defthm recp-resize-ar
  (implies (recp rec)
           (recp (resize-ar ncycles nvars rec)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(deftheory ar-theory-defuns
  '(ari !ari arl recp resize-ar))

(deftheory ar-theory-lemmas
  '(rationalp-ari
    recp-!ari
    ari-!ari
    !ari-ari
    !ari-!ari-same-address
    !ari-!ari-different-addresses
    arl-!ari
    ar-length-is-resize))

(in-theory (disable ar-theory-defuns ar-theory-lemmas))

(defun all-len  (lst n)
  (declare (xargs :guard (true-list-listp lst)))
  (cond ((endp lst) t)
        (t (and (equal (len (car lst)) n)
                (all-len (cdr lst) n)))))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           t
                           (unsigned-byte 60)
                           (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                init-rec-help-var))

(defun init-rec-help-var (i cycle vals nvars rec)

; This could probably be made more efficient by maintaining the current index
; and adding nvars to it at each recursive call, rather than incrementing cycle
; (which could be omitted from the formals).  But I kind of hate to break the
; !ari abstraction, and this should be plenty efficient as it is, especially
; since it's only used during initialization.

  (declare (type (unsigned-byte 60) i cycle nvars)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec)
           (xargs :guard (and (rational-listp vals)
                              (< i nvars)
                              (< 1 nvars)
                              (equal (* nvars (+ cycle (len vals)))
                                     (arl rec))
                              (<= (arl rec) *2^60*))
                  :guard-hints (("Goal"
                                 :nonlinearp t
                                 :expand ((len vals))
                                 :in-theory (enable ar-theory-lemmas)))
                  :stobjs rec))
  (cond ((endp vals) rec)
        (t (let ((rec (!ari i cycle nvars (car vals) rec)))
             #+(and rec-stobj rec-dcls (not simple-vectors))
             (declare (type (simple-array double-float (*)) rec))
             (init-rec-help-var i (1+ cycle) (cdr vals) nvars rec)))))

(defthm symbol-rational-list-alistp-forward-to-true-list-listp
  (implies (symbol-rational-list-alistp x)
           (true-list-listp x))
  :rule-classes :forward-chaining)

(defthm arl-init-rec-help-var
  (implies (and (force (natp i))
                (force (natp cycle))
                (force (natp nvars))
                (force (< i nvars))
                (force (equal (* nvars (+ cycle (len vals)))
                              (arl rec))))
           (equal (arl (init-rec-help-var i cycle vals nvars rec))
                  (arl rec)))
  :hints (("Goal" :in-theory (enable ar-theory-lemmas))))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function (t
                           (simple-array double-float (*))
                           (unsigned-byte 60)
                           (unsigned-byte 60)
                           (unsigned-byte 60))
                          (values (simple-array double-float (*))))
                init-rec-help))

(encapsulate
()

(local (include-book "arithmetic/top" :dir :system))

(local (defthm len-revappend
         (equal (len (revappend x y))
                (+ (len x) (len y)))))

(local (defthm rational-listp-revappend
         (implies (and (rational-listp x)
                       (rational-listp y))
                  (rational-listp (revappend x y)))))

(defun init-rec-help (a rec i init-cycles nvars)
  (declare (type (unsigned-byte 60) i init-cycles nvars)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec)
           (xargs :guard (and (< 1 nvars)
                              (symbol-rational-list-alistp a)
                              (< 0 init-cycles)
                              (all-len a (1+ init-cycles))
                              (equal (+ i (len a)) nvars)
                              (equal (* init-cycles nvars) (arl rec))
                              (< (arl rec) *2^60*))
                  :guard-hints (("Goal"
                                 :in-theory (enable ar-theory-lemmas))
                                ("Subgoal 5" :nonlinearp nil)
                                '(:nonlinearp t))
                  :stobjs rec))
  (if (atom a)
      rec
    (let* ((pair (car a))
           (rev-vals (cdr pair))
           (rec  (init-rec-help-var i 0 (reverse rev-vals) nvars rec)))
      #+(and rec-stobj rec-dcls (not simple-vectors))
      (declare (type (simple-array double-float (*)) rec))
      (init-rec-help (cdr a) rec (u60 (1+ (u60 i))) init-cycles nvars))))
)

(defun pointwise-<= (x y)
  (declare (xargs :guard (and (rational-listp x)
                              (rational-listp y)
                              (= (len x) (len y)))))
  (cond ((endp x) t)
        ((<= (car x) (car y))
         (pointwise-<= (cdr x) (cdr y)))
        (t nil)))

(defun init-rtime-with-lists (time-list hn-list rtime)
  (declare (xargs :guard (and (rational-listp time-list)
                              (rational-listp hn-list)
                              (consp time-list)
                              (= (len time-list) (len hn-list))
                              (pointwise-<= hn-list time-list))
                  :stobjs rtime))
  (cond ((endp (cdr time-list))
         (if (not (= (car hn-list) 0))
             (prog2$ (er hard? 'init-rtime-with-lists
                         "Expected (car hn-list) to be 0, but it is ~x0."
                         (car hn-list))
                     rtime)
           (init-rtime (car time-list) rtime)))
        (t (let ((rtime (init-rtime-with-lists (cdr time-list) (cdr hn-list) rtime)))
             (update-rtime (car time-list) (car hn-list) rtime)))))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function (t
                           (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                init-rec))

#-raw
(progn
  (defwarrant update-rec-ari)
  (defwarrant nump)
  (defwarrant num-listp))

(defun init-rec (lst rec)
  (declare (xargs :stobjs rec
                  :guard (num-listp lst)
                  :guard-hints (("Goal"
                                 :in-theory (enable nth-!nth arl recp)))))
  (let* ((len (length lst))
         (rec (resize-rec-ar len rec)))
    (loop$ with i of-type (integer 0 *) = 0
           with lst2 of-type (satisfies num-listp) = lst
           with len2 of-type (integer 0 *) = len
           do
           :guard (and (recp rec)
                       (equal len2 (arl rec))
                       (equal (+ i (len lst2)) len2))
           :values (rec)
           :measure (len lst2)
           (if (= i len2)
               (return rec)
             (progn (setq rec (update-rec-ari i (car lst2) rec))
                    (setq i (1+ i))
                    (setq lst2 (cdr lst2)))))))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function (t t (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                clear-rec))

(defun clear-rec (i n rec)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (arl rec)))
                  :guard-hints (("Goal" :in-theory (enable !nth arl)))
                  :stobjs rec)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec))
  (if (zp (- n i))
      rec
    ;; when the record is cleared, every entries in the array is a
    ;; list of one zero.
    (let ((rec (update-rec-ari i (r2f 0) rec)))
      #+(and rec-stobj rec-dcls (not simple-vectors))
      (declare (type (simple-array double-float (*)) rec))
      (clear-rec (1+ i) n rec))))

; Representation 0: full symbolic vw-eval-termp terms in the
; A-sym-uncompressed and b-sym-uncompressed arrays

; Representation 1: constant fold all entries in A-sym-uncompressed
; and b-sym-uncompressed and store in A-sym-folded and b-sym-folded
; respectively. Additionally, we can simplify all terms with $hn$ when
; performing a fixed time-step simulation.

; Representation 2 (""): create a list of all symbolic vw-eval-termps from
; A-sym-folded and b-sym-folded.

; Representation 3 ("all-rec-names"): generate a list of all unique
; symbolic vw-eval-termp subterms from Representation 2, where the
; first entries are the variables in the same order as in the record
; ($time$, $hn$, + all-names).  all-rec-names
; contains all the names, in order, for each position in AR (the
; record).

; AR = array (record), where index
; <!!matt> Redo this comment when *initial-vars* settles down.
;  0 : a list of rationals/floats for $time$
;  1 : a list of rationals/floats for $hn$
;  2 : a list of rationals/floats for <first-variable-in-all-names>
;  ...
; NOTE: all-rec-names does NOT contain the variables for the reference
; node (often 'GND) and its derivative.

; STV = array (evaluated values for each subterm), where index

; Representation 4: generate a list of all unique

; Note: we convert A-sym-folded and b-sym-folded to A-sym-compressed
; and b-sym-compressed by finding and replacing each term with its
; ``pos'' in Representation 3.

; Representation 4: create alist that maps each uncompressed subterm
; into its compressed format.

; Representation 5: initialize an array with all subterms in
; compressed format.

; Representation 6: initiliaze an array of the same length as
; Representation 5 to store the results of evaluation.

; Representation 7: create array "A-prev-vals" that stores the A entry
; evaluation results from the previous time step.

;; We will initialize the list of all subterms ("all-subterms") so
;; that its first n entries are the variables in the same order as in
;; the record.

;; We generate the rest of the unique (non-atom) subterms.

;; Suppose all variables in the record = '(x y z)
;; The list should now look something like:
;; '(x y z (f+ x y))

;; Note: x, y, and z are the variables in the record. The indices
;; corresponding to x (0), y (1), and z (2) will be the same as their
;; position in the record (and all-names).

;; Create a fast-alist where each term in "all-subterms" is converted
;; to its corresponding "compressed" representation. Call it
;; "all-subterms-compressed-alist".

;; ((x . 0)
;;  (y . 1)
;;  ((f+ x y) . (17 0 1)))

;; Create an array ("sts") of length "all-subterms".

;; Initialize "sts" with (strip-cdrs "all-subterms-compressed-alist")

;; Create an array ("A-prev-vals") of length "all-subterms" and
;; initialize with zeros if the term corresponding to that index in
;; sts is in the A matrix; otherwise, nil.  This array is used to
;; check if we need to redo the A decomposition.

;; Create an array ("sts-evaled") of length "all-subterms" and
;; initialize with zeros. This is where the evaluator stores its
;; results.

;; Note: we are currently evaluating ALL subterms, which results in an
;; inside-out evaluation.  Later, we may wish to perform
;; lazy-evaluation on "if" expressions; this will require an
;; outside-in evaluation.

;; For A, compare "A-prev-vals" to new A values. If any change,
;; update dz A and redo the decomposition of A.

;; For b, fetch values from sts-evaled and place in dz b.

#||
An example of the data structures used above:

;; An example of data structures we need

;; A-sym-ucompressed
A-sym-ucompressed[0] = '((0 '2) (1 '5))
A-sym-ucompressed[1] = '((0 (f+ '0 '2)) (1 x))

;; b-sym-uncompressed
b-sym-uncompressed[0] = ''2
b-sym-uncompressed[1] = '(f* x (f+ '0 '2))

;; A-sym-folded
A-sym-folded[0] = '((0 '2) (1 '5))
A-sym-folded[1] = '((0 '2) (1 x))

;; b-sym-folded
b-sym-folded[0] = ''2
b-sym-folded[1] = '(f* x '2)

;; list of all terms from A-sym-folded and b-sym-folded
'('2 '5 '2 x '2 (f* x '2))

;; list of all unique subterms (notice: since x is a simulation
;; variable, it is first)
'(x '2 '5 (f* x '2))

;; convert A-sym-folded and b-sym-folded into A-sym-compressed and
;; b-sym-compressed by looking up the position of each term in the
;; matrix/vector in the list of all unique subterms.

;; A-sym-compressed
A-sym-compressed[0] = '((0 1) (1 2))
A-sym-compressed[1] = '((0 1) (1 0))

;; b-sym-compressed
b-sym-compressed[0] = 1
b-sym-compressed[1] = 3

;; compressed-alist that maps each uncompressed subterm to compressed
;; format
'((x . 0)
  ('2 . 1)
  ('5 . 2)
  (<f*-index> 0 1) . 3)

;; create list that is the (strip-cars compressed-alist)
subs[0] = x       ;; some default value. We will initialize the
                  ;; simulation variables from the record.
subs[1] = '2
subs[2] = '5
subs[3] = (f* 0 1)

;; initialize an array of the same length to store results of
;; evaluation (subs-results). For each simulation step, we seed
;; subs-results with the values of the n simulation variables from the
;; record. We evaluate from subs[n] to the end.
subs-results[0] = 0 ;; stores the value of ``x'' from the record.
subs-results[1] = 0
subs-results[2] = 0
subs-results[3] = 0

;; create array A-pre-vals that stores the A entry evaluation results
;; from the previous time step. I.e. each of the indices stored in
;; A-sym-compressed (ex. 1,2,1,0)

A-pre-vals[0] = 0
A-pre-vals[1] = 0
A-pre-vals[2] = 0
A-pre-vals[3] = nil

||#

(defstobj st-vals
  ;; an array of the same length as the list of all unique subterms,
  ;; which includes all of the simulation variables (all-names). The
  ;; array stores the evaluation of each of the subterms. For each
  ;; simulation step, we seed the first n array entries with the
  ;; values of the simulation variables from the record. We evaluate
  ;; from subs[n] to the end.

  #-stv-stobj
  (stv :type
       (array #-simple-vectors (satisfies nump) #+simple-vectors t
              (0))
       :initially 0
       :resizable t)
  #+stv-stobj
  (stv :type
       (array #-simple-vectors double-float #+simple-vectors t
              (0))
       :initially 0.0d0
       :resizable t)
  :renaming
  ((update-stvi  !stvi)
   (stv-length   stvl))
  :inline t
  :non-memoizable t)

;; We prove some theorems about the stv array accessors, updaters, and
;; recognizers and then disable their definitions.

(local
 (defthm rationalp-nth-l-a
   (implies (and (stvp a)
                 (<= 0 l)
                 (< l (len a)))
            (rationalp (nth l a)))
   :hints
   (("Goal" :in-theory (enable nth nth-theory-defuns)))))

(defthm rationalp-stvi
  ;; We make this a type-prescription rule since we don't expect the
  ;; rationalp call to match very often.  But since hypotheses of
  ;; type-prescription rules are relieved only with type-set
  ;; reasoning, we force them so that the full prover can deal with
  ;; them eventually.  We force them individually, rather than
  ;; putting a single force around the (and ...), so that if one or
  ;; two of them is successfully relieved then there's no need to
  ;; reconsider those at a forcing round.

  ;; We don't force (MEMORYP MEM), because then the proof for
  ;; CONS-IS-SAME-AS-INSERT-WHEN-E-LESS-THAN-M fails (below).
  (implies (and (st-valsp st-vals)
                (force (<= 0 l))
                (force (< l (stvl st-vals))))
           (rationalp (stvi l st-vals)))
  :rule-classes :type-prescription)

(local
 (defthm stvp-!nth
   ;; Note, can extend A by one RATIONAL number
   (implies (and (stvp a)
                 ;; (natp l)
                 (<= l (len a))
                 (rationalp v))
            (stvp (!nth l v a)))
   :hints
   (("Goal" :in-theory (enable nth-theory-defuns)))))

(defthm st-valsp-!stvi
  ;; Can extend field M in STOBJ MEMORY by one RATIONAL number
  (implies (and (force (st-valsp st-vals))
                ;; (natp l)
                (force (<= l (stvl st-vals))) ; Can extend MEMORY at its end
                (force (rationalp v)))
           (st-valsp (!stvi l v st-vals)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm stvi-!stvi
  ;; Similar to NTH-!NTH lemma
  (equal (stvi m (!stvi n val l))
         (if (equal (nfix m) (nfix n))
             val
           (stvi m l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm !stvi-stvi
  (implies (force (< (nfix ma) (stvl st-vals)))
           (equal (!stvi ma (stvi ma st-vals) st-vals)
                  st-vals))
  :hints
  ;; By enabling NTH and !NTH, we are able to "dig down"
  ;; to the interior accesses so we can apply !NTH-NTH,
  ;; and thus, we don't need to know (ST-VALSP st-vals).
  (("Goal" :in-theory (enable !nth nth
                              nth-theory-lemmas))))

(defthm !stvi-!stvi-same-address
  (implies (equal a1 a2)
           (equal (!stvi a1 v (!stvi a2 w st-vals))
                  (!stvi a1 v st-vals)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm !stvi-!stvi-different-addresses
  ;; Should we have some SYNTAXP check to order by address?
  (implies (not (equal (nfix a1) (nfix a2)))
           (equal (!stvi a1 v1 (!stvi a2 v2 st-vals))
                  (!stvi a2 v2 (!stvi a1 v1 st-vals))))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm stvl-!stvi
  (implies (and ; (st-valsp st-vals)
            (force (natp l))
            (force (< l (stvl st-vals))))
           (equal (stvl (!stvi l v st-vals))
                  (stvl st-vals)))
  :hints
  ;; By enabling NTH and !NTH, we are able to "dig down"
  ;; to the interior accesses so we can apply !NTH-NTH,
  ;; and thus, we don't need to know (ST-VALSP st-vals).
  (("Goal" :in-theory (enable !nth nth
                              nth-theory-lemmas))))

(defthm stvl-is-resize
  (equal (stvl (resize-stv n st-vals))
         (nfix n))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm st-valsp-resize-list
  (implies (and (stvp st-vals)
                (nump v))
           (stvp (resize-list st-vals new-size v))))

(defthm st-valsp-resize-stv
  (implies (st-valsp st-vals)
           (st-valsp (resize-stv new-size st-vals)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(deftheory stv-theory-defuns
  '(stvi !stvi stvl st-valsp resize-stv))

(deftheory stv-theory-lemmas
  '(rationalp-stvi
    st-valsp-!stvi
    stvi-!stvi
    !stvi-stvi
    !stvi-!stvi-same-address
    !stvi-!stvi-different-addresses
    stvl-!stvi
    stvl-is-resize))

(in-theory (disable stv-theory-defuns stv-theory-lemmas))

(defun subterm-rational-quotep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (equal (car x) #.*quote-index*)
       (consp (cdr x))
       (rationalp (cadr x))
       (null (cddr x))))

(defun subterm-num-quotep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (equal (car x) #.*quote-index*)
       (consp (cdr x))
       (nump (cadr x))
       (null (cddr x))))

(defthm subterm-num-quotep-is-subterm-rational-quotep
  (implies (subterm-num-quotep x)
           (subterm-rational-quotep x)))

(defun vw-eval-subtermp (x nvars stv-max)
  (declare (type (unsigned-byte 60) nvars stv-max)
           (xargs :guard
                  (and ;; At a minimum, the AR record contains
                       ;; entries for $time$ and $hn$.
                       (<= (len *initial-vars*) nvars)
                       ;; The STV array is at least the length
                       ;; of the AR record.
                       (<= nvars stv-max))))
  (b* (((when (atom x))
        nil)

       ((unless (true-listp x))
        nil)

       (fn-num (car x))
       ((unless (and (natp fn-num)
                     (< fn-num (len *fns*))))
        nil)

       (args (cdr x))
       (arg1 (car args))   ; (u60 (car args)))
       (arg2 (cadr args))  ; (u60 (cadr args)))

       ((unless (if (<= #.*if-index* fn-num)
                    (and (natp arg1)
                         (< arg1 stv-max)
                         ;; This is weird place to require stv-max to
                         ;; be within bounds. It is already in the
                         ;; guard (for. If we want this, then this should
                         ;; be a top-level check
                         ;; (< stv-max *2^60*)
                         )
                  t))
        nil)

       ((unless (if (<= #.*f+-index* fn-num)
                    (and (natp arg2)
                         (< arg2 stv-max)
                         ;; (< stv-max *2^60*)
                         )
                  t))
        nil))

    (case fn-num
      (#.*quote-index*
       (subterm-num-quotep x))

      (#.*back-index*
       (and (nargs args 2)
            (let ((var (car args))
                  (delay (cadr args)))
              (and (natp var)
                   (< var nvars)
                   (subterm-rational-quotep delay)))))

      (#.*$time$<-index*
       (and (nargs args 1)
            (subterm-rational-quotep (car args))
            (<= 0 (unquote (car args)))))

      (#.*$time$-$hn$<-index*
       (and (nargs args 1)
            (subterm-rational-quotep (car args))
            (<= 0 (unquote (car args)))))

      (#.*$time$<mod--index*
       (and (nargs args 3)
            (subterm-rational-quotep (car args))
            (<= 0 (unquote (car args)))
            (subterm-rational-quotep (cadr args))
            (< 0 (unquote (cadr args)))
            (subterm-rational-quotep (caddr args))
            (< 0 (unquote (caddr args)))))

      (#.*$time$-$hn$<mod--index*
       (and (nargs args 3)
            (subterm-rational-quotep (car args))
            (<= 0 (unquote (car args)))
            (subterm-rational-quotep (cadr args))
            (< 0 (unquote (cadr args)))
            (subterm-rational-quotep (caddr args))
            (< 0 (unquote (caddr args)))))

      (#.*if-index*
       (and (nargs args 3)
            (natp (car args))
            (< (car args) stv-max)

            (natp (cadr args))
            (< (cadr args) stv-max)

            (natp (caddr args))
            (< (caddr args) stv-max)))

      (#.*f-not-index*  (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f0--index*    (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-abs-index*  (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-1/x-index*  (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-sqrt-index* (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-sin-index*  (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-cos-index*  (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-tan-index*  (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-tanh-index* (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f-exp-index*  (and (nargs args 1)
                             (natp (car args))
                             (< (car args) stv-max)))
      (#.*f+-index*     (and (nargs args 2)
                             (natp (car args))
                             (< (car args) stv-max)
                             (natp (cadr args))
                             (< (cadr args) stv-max)))
      (#.*f--index*     (and (nargs args 2)
                             (natp (car args))
                             (< (car args) stv-max)
                             (natp (cadr args))
                             (< (cadr args) stv-max)))
      (#.*f*-index*     (and (nargs args 2)
                             (natp (car args))
                             (< (car args) stv-max)
                             (natp (cadr args))
                             (< (cadr args) stv-max)))
      (#.*f/-index*     (and (nargs args 2)
                             (natp (car args))
                             (< (car args) stv-max)
                             (natp (cadr args))
                             (< (cadr args) stv-max)))
      (#.*f<-index*     (and (nargs args 2)
                             (natp (car args))
                             (< (car args) stv-max)
                             (natp (cadr args))
                             (< (cadr args) stv-max)))
      (#.*f=-index*     (and (nargs args 2)
                             (natp (car args))
                             (< (car args) stv-max)
                             (natp (cadr args))
                             (< (cadr args) stv-max)))
      (#.*f-mod-index*  (and (nargs args 2)
                             (natp (car args))
                             (< (car args) stv-max)
                             (natp (cadr args))
                             (< (cadr args) stv-max)))
      (otherwise nil))))

(defun vw-eval-subterm-listp (xs nvars stv-max)
  (declare (type (unsigned-byte 60) nvars stv-max)
           (xargs :guard (and (<= (len *initial-vars*) nvars)
                              (<= nvars stv-max))))
  (if (atom xs)
      (null xs)
    (and (vw-eval-subtermp (car xs) nvars stv-max)
         (vw-eval-subterm-listp (cdr xs) nvars stv-max))))

#+(and rec-stobj rec-dcls stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           (unsigned-byte 60)
                           (simple-array double-float (*))
                           (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                init-st-vals))

(defun init-st-vals (i cycle nvars rec st-vals)
  (declare (type (unsigned-byte 60) i cycle nvars)
           #+(and rec-stobj rec-dcls stv-stobj stv-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec st-vals)
           (xargs :measure (nfix (- nvars i))
                  :guard (and (natp i)
                              (natp cycle)
                              (natp nvars)
                              (<= (* (1+ cycle) nvars) (arl rec))
                              (<= i nvars)
                              (<= nvars (stvl st-vals))
                              (< (stvl st-vals) *2^60*)
                              (<= (arl rec) *2^60*))
                  :guard-hints (("Goal"
                                 :in-theory (enable ar-theory-lemmas
                                                    stv-theory-lemmas)
                                 :nonlinearp t))
                  :stobjs (rec st-vals)))
  (if (mbe :logic (zp (- nvars i))
           :exec  (= i nvars))
      st-vals
    (let* ((val (ari i cycle nvars rec))
           (st-vals (!stvi i val st-vals)))
      #+(and rec-stobj rec-dcls stv-stobj stv-dcls (not simple-vectors))
      (declare (type (simple-array double-float (*)) st-vals))
      (init-st-vals (1+ i) cycle nvars rec st-vals))))

(defthm stvl-init-st-vals
  (implies (and (natp i)
                (<= nvars (stvl st-vals)))
           (equal (stvl (init-st-vals i cycle nvars rec st-vals))
                  (stvl st-vals)))
  :hints
  (("Goal" :in-theory (enable stv-theory-lemmas))))

(defthm indices-below-init-st-vals-unchanged
  (implies (and (natp i)
                (natp j)
                (< j i))
           (equal (stvi j
                        (init-st-vals i
                                      cycle
                                      nvars
                                      rec
                                      st-vals))
                  (stvi j st-vals)))
     :hints
     (("goal" :in-theory (enable stv-theory-lemmas))))

(defthm init-st-vals-is-same-as-rec
  (implies (and (natp i)
                (natp j)
                (natp nvars)
                (<= i j)
                (< j nvars))
           (equal (stvi j (init-st-vals i cycle nvars rec st-vals))
                  (ari j cycle nvars rec)))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas stv-theory-lemmas))))

#+(and rec-stobj rec-dcls stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           t
                           (simple-array double-float (*))
                           (simple-array double-float (*)))
                          (values t))
                vw-eval-subterm-guard))

(defun vw-eval-subterm-guard (cycle nvars rtime rec st-vals)
  (declare (xargs :guard t
                  :stobjs (rtime rec st-vals))
           #+(and rec-stobj rec-dcls stv-stobj stv-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec st-vals))
  (and (natp cycle)
       (natp nvars)
       (<= (* (1+ cycle) nvars) (arl rec))
       (<= (arl rec) *2^60*)
       (<= nvars (stvl st-vals))
       (< (stvl st-vals) *2^60*)
       ;; At a minimum, the AR record and the STV
       ;; array contain entries for $time$ and $hn$.
       (<= (len *initial-vars*) nvars)
       (<= 0 (car (hn-list rtime)))
       (<= (car (hn-list rtime))
           (car (time-list rtime)))

; It might seem weird that we use (+ 2 cycle) below.  But when we call
; vw-eval-subterm-list in simulate-step, we call it on pcycle, the preceding
; cycle, i.e., (1- cycle) -- that's when variable values were more recently
; stored.  So (+ 2 cycle) is just 1 more than the current cycle, which makes
; sense when you consider that at cycle 0 -- when simulation started -- the
; time-list and hn-list of rtime each had length 1.

       (equal (len (time-list rtime))
              (+ 2 cycle))
       (equal (len (hn-list rtime))
              (+ 2 cycle))))

#+rec-dcls
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           (unsigned-byte 60)
                           t
                           t
                           #+(and rec-stobj (not simple-vectors))
                           (simple-array double-float (*))
; Matt K. mod, 7/13/2023: Put in a type for the missing argument in the #-
; case.  There may be a stronger type possible here (haven't really thought
; about it).
                           #-(and rec-stobj (not simple-vectors))
                           t)
                          (values double-float))
                back-ar))

(encapsulate
  ()

(local (include-book "arithmetic/top" :dir :system))

(defun back-ar (k cycle nvars time-list back-time rec)
; This is an updated version of back, which is still defined in vw-eval.lisp.
  (declare (type (unsigned-byte 60) k cycle nvars)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec)
           (xargs :guard (and (natp k)
                              (natp cycle)
                              (natp nvars)
                              (< k nvars)
                              (<= (* (1+ cycle) nvars) (arl rec))
                              (<= (arl rec) *2^60*)
                              (= (len time-list)
                                 (1+ cycle))
                              (rational-listp time-list)
                              (rationalp back-time))
                  :guard-hints (("Goal"
                                 :in-theory (enable ar-theory-lemmas))
                                '(:nonlinearp t)
                                ("Subgoal 6'" :nonlinearp nil)
                                ("[1]Subgoal 3''" :nonlinearp nil))
                  :stobjs rec))
  (b* (((unless (and (mbt (rationalp back-time))
                     (<= 0 back-time)))
        ;; If the ``back'' access reaches back before the simulation
        ;; started, we return a value of 0.
        (r2f 0))
       (i
        ;; Find first time in list of times that is less than or equal
        ;; to back-time.
        ;; We assume the times in time-list are strictly decreasing
        (find-first-index back-time time-list))
       ((unless i) (r2f 0))
       (#-rec-dcls Vi #+rec-dcls (the double-float Vi)
        (ari k (- cycle i) nvars rec)) ;; float expected
       ((when (= i 0)) (mbe :logic (rfix Vi)
                            :exec  Vi))
       (i-1 (1- i))
       (#-rec-dcls Vi-1 #+rec-dcls (the double-float Vi-1)
        (ari k (- cycle i-1) nvars rec))    ;; float expected
       ;; Note: Ti-1 > back-time >= Ti
       (Ti   (nth i   time-list)) ;; rationalp expected
       (Ti   (mbe :logic (rfix Ti)
                  :exec Ti))
       (Ti-1 (nth i-1 time-list)) ;; rationalp expected
       (Ti-1 (mbe :logic (rfix Ti-1)
                  :exec Ti-1))

       ;; We should be able to prove this check away, because i must
       ;; be less than the length of time-list and var-list. The
       ;; lengths of time-list and var-list must be the same.
       ((unless (and Vi
                     Vi-1))
        (r2f 0))
       (#-rec-dcls Vi #+rec-dcls (the double-float Vi)
        (mbe :logic (rfix Vi)
             :exec Vi))
       (#-rec-dcls Vi-1 #+rec-dcls (the double-float Vi-1)
        (mbe :logic (rfix Vi-1)
             :exec Vi-1))
       ;; Consider adding this check to the guard in simulate-step:
       ;; the list of $time$ values in the history must be strictly
       ;; decreasing.
       ((when (< Ti-1 Ti))
        (prog2$ (cw "back: simulator error! Ti: ~p0, Ti-1: ~p1.~%"
                    Ti Ti-1)
                (r2f 0)))
       ;; time values are stored as rationals. We need to
       ;; convert them to floating point when needed.
       (#-rec-dcls T-fp-diff #+rec-dcls (the double-float T-fp-diff)
        (f- (r2f Ti-1) (r2f Ti)))
       ((when (= T-fp-diff (r2f 0)))
        (prog2$ (cw "back: floating-point rounding error! Ti: ~p0, Ti-1: ~p1.~%"
                    Ti Ti-1)
                (r2f 0))))
    ;; we use a linear approximation to calculate the value at
    ;; back-time
    ;; Vi + ((Vi-1 - Vi)/(Ti-1 - Ti)) * (back-time - Ti)
    (f+ Vi (f* (f/ (f- Vi-1 Vi)
                   T-fp-diff)
               (f- (r2f back-time) (r2f Ti))))))
)

(defthm rationalp-back-ar
  (rationalp (back-ar k cycle nvars time-list back-time rec))
  :hints (("Goal" :in-theory (enable back-ar)))
  :rule-classes :type-prescription)

(in-theory (disable back-ar))

(defun-inline vw-eval-subterm (i x cycle nvars rtime rec st-vals)

; We evaluate the term, x, with respect to simulation variable values at the
; end of the given cycle.  Note that rtime is assumed to be extended already to
; include the current time, i.e., the time at cycle+1.

  (declare (type (unsigned-byte 60) i cycle nvars)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type #+simple-vectors simple-vector
                 #-simple-vectors (simple-array double-float (*))
                 rec)
           #+(and stv-stobj stv-dcls)
           (type #+simple-vectors simple-vector
                 #-simple-vectors (simple-array double-float (*)) st-vals)
           (xargs :guard
                  (and (< i (stvl st-vals))
                       (vw-eval-subterm-guard cycle nvars rtime rec st-vals)
                       (vw-eval-subtermp x nvars (stvl st-vals)))
                  :guard-hints (("Goal" :in-theory
                                 (enable ar-theory-lemmas
                                         stv-theory-lemmas)))
                  :stobjs (rtime rec st-vals)))
  (b* ( ;; function number
       ((the (unsigned-byte 60) fn-num)
        (u60 (car x)))

       (args (cdr x))
       (a1 (car args))  ; (u60 (car args)))
       (a2 (cadr args)) ; (u60 (cadr args)))

       ;; We should know that ARG1 and ARG2 are bounded by (STVL ST-VALS)
       #-stv-dcls
       (arg1
        (if (<= #.*if-index* fn-num)
            (mbe :logic (rfix (stvi a1 st-vals))
                 :exec        (stvi a1 st-vals))
          (r2f 0)))
       #+stv-dcls
       ((the double-float arg1)
        (the double-float (if (<= #.*if-index* fn-num)
                              (stvi a1 st-vals)
                            (r2f 0))))
       #-stv-dcls
       (arg2
        (if (<= #.*f+-index* fn-num)
            (mbe :logic (rfix (stvi a2 st-vals))
                 :exec        (stvi a2 st-vals))
          (r2f 0)))
       #+stv-dcls
       ((the double-float arg2)
        (the double-float (if (<= #.*f+-index* fn-num)
                              (stvi a2 st-vals)
                            (r2f 0)))))

    (case fn-num
      (#.*quote-index*
       (!stvi i
              #-stv-dcls
              (mbe :logic (rfix (car args))
                   :exec        (car args))
              #+stv-dcls
              (the double-float (car args))
              st-vals))

      (#.*back-index*
       ;; Example symbolic call: (back var delay)
       (let* ((var (car args))
              (delay (unquote (cadr args)))
              (r-time-list (cdr (time-list rtime)))
              (r-time ; simulation time when variables received their values
               (car r-time-list))
              (r-back-time (- r-time delay))
              (val

;;; We may be able to eliminate all uses of *$time$-index* and
;;; *$hn$-index* if we give special treatment to them as shown in the
;;; form as follows:

;              (if (or (= var *$time$-index*) (= var *$hn$-index*))
;                  (stvi var st-vals)

;;; In that case, though, either we need to add hypotheses to
;;; rationalp-vw-eval-subterm, namely (force (st-valsp st-vals)) and
;;; (< (len *initial-vars*) (stvl st-vals)), or else we need to do
;;; some work to avoiid those (seems possible).

               (back-ar var cycle nvars r-time-list r-back-time rec)))
         #+(and rec-dcls stv-dcls) ; test mechanism for array accesses
         (declare (type double-float val))
         (!stvi i
                #-(and rec-dcls stv-dcls) val
                #+(and rec-dcls stv-dcls) (the double-float val)
                st-vals)))

      (#.*$time$<-index*
       (let* ((r-time-list (time-list rtime))
              (r-time (car r-time-list)))
         (!stvi i ($time$< r-time (unquote (car args))) st-vals)))

      (#.*$time$-$hn$<-index*
       (b* ((r-time-list (time-list rtime))
            (r-time (car r-time-list))
            (r-hn-list (hn-list rtime))
            (r-hn (car r-hn-list))
            (compare-value (unquote (car args))))
         (!stvi i ($time$-$hn$< r-hn r-time compare-value) st-vals)))
      (#.*$time$<mod--index*
       (b* ((r-time-list (time-list rtime))
            (r-time (car r-time-list))
            (a0 (unquote (car args)))
            (a1 (unquote (cadr args)))
            (a2 (unquote (caddr args))))
         (!stvi i ($time$<mod- r-time a0 a1 a2) st-vals)))
      (#.*$time$-$hn$<mod--index*
       (b* ((r-time-list (time-list rtime))
            (r-time (car r-time-list))
            (r-hn-list (hn-list rtime))
            (r-hn (car r-hn-list))
            (a0 (unquote (car args)))
            (a1 (unquote (cadr args)))
            (a2 (unquote (caddr args))))
         (!stvi i ($time$<mod- (- r-time r-hn) a0 a1 a2) st-vals)))
      (#.*if-index*
       (if (not (= arg1 (r2f 0)))
           (!stvi i
                  (mbe :logic (rfix (stvi (cadr args) st-vals))
                       :exec (stvi (cadr args) st-vals))
                  st-vals)
         (!stvi i
                (mbe :logic (rfix (stvi (caddr args) st-vals))
                     :exec (stvi (caddr args) st-vals))
                st-vals)))

      (#.*f-not-index*   (!stvi i (f-not arg1) st-vals))
      (#.*f0--index*     (!stvi i (f0- arg1) st-vals))
      (#.*f-abs-index*   (!stvi i (f-abs arg1) st-vals))
      (#.*f-1/x-index*   (if (= arg1 (r2f 0))
                             (prog2$ (cw "vw-eval: f-1/x dividing by 0.~%")
                                     (!stvi i (r2f 0) st-vals))
                           (!stvi i (f-1/x arg1) st-vals)))
      (#.*f-sqrt-index*  (if (< arg1 (r2f 0))
                             (prog2$ (cw "vw-eval: f-sqrt of negative number.~%")
                                     (!stvi i (r2f 0) st-vals))
                           (!stvi i (f-sqrt arg1) st-vals)))
      (#.*f-sin-index*   (!stvi i (f-sin  arg1) st-vals))
      (#.*f-cos-index*   (!stvi i (f-cos  arg1) st-vals))
      (#.*f-tan-index*   (!stvi i (f-tan  arg1) st-vals))
      (#.*f-tanh-index*  (!stvi i (f-tanh arg1) st-vals))
      (#.*f-exp-index*   (!stvi i (f-exp  arg1) st-vals))
      (#.*f+-index*      (!stvi i (f+ arg1 arg2) st-vals)) ;; 17
      (#.*f--index*      (!stvi i (f- arg1 arg2) st-vals)) ;; 18
      (#.*f*-index*      (!stvi i (f* arg1 arg2) st-vals)) ;; 19
      (#.*f/-index*      (if (= arg2 (r2f 0))                ;; 20
                             (prog2$ (cw "vw-eval: f/ dividing by 0.~%")
                                     (!stvi i (r2f 0) st-vals))
                           (!stvi i (f/ arg1 arg2) st-vals)))
      (#.*f<-index*      (!stvi i (f< arg1 arg2) st-vals))
      (#.*f=-index*      (!stvi i (f= arg1 arg2) st-vals))
      (#.*f-mod-index*   (if (= arg2 (r2f 0))
                             (prog2$ (cw "vw-eval: f-mod using 0 divisor")
                                     (!stvi i (r2f 0) st-vals))
                           (!stvi i (f-mod arg1 arg2) st-vals)))
      (otherwise (prog2$ (er hard 'vw-eval-subterm
                             "Impossible case, fn-num = ~x0"
                             fn-num)
                         (!stvi i (r2f 0) st-vals)))
      )))

(in-theory (disable vw-eval-subterm))

#+(and rec-stobj rec-dcls stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function (t
                           (unsigned-byte 60)
                           (unsigned-byte 60)
                           (unsigned-byte 60)
                           t
                           #+(and rec-stobj rec-dcls stv-stobj stv-dcls
                                  simple-vectors)
                           simple-vector
                           #+(and rec-stobj rec-dcls stv-stobj stv-dcls
                                  (not simple-vectors))
                           (simple-array double-float (*))
                           #+(and rec-stobj rec-dcls stv-stobj stv-dcls
                                  simple-vectors)
                           simple-vector
                           #+(and rec-stobj rec-dcls stv-stobj stv-dcls
                                  (not simple-vectors))
                           (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                vw-eval-subterm-list))

(defthm stvl-vw-eval-subterm
  (implies (and (natp i)
                (consp xs)
                (= (+ (len xs) i) (stvl st-vals)))
           (equal (stvl (vw-eval-subterm i x cycle nvars rtime rec st-vals))
                  (stvl st-vals)))
  :hints
  (("Goal" :in-theory (enable stv-theory-lemmas vw-eval-subterm))))

(defun vw-eval-subterm-list (xs i cycle nvars rtime rec st-vals)
  (declare (type (unsigned-byte 60) i cycle nvars)
           #+(and rec-stobj rec-dcls stv-stobj stv-dcls)
           (type #+simple-vectors simple-vector
                 #-simple-vectors (simple-array double-float (*))
                 rec st-vals)
           (xargs :guard
                  (and (vw-eval-subterm-guard cycle nvars rtime rec st-vals)
                       (= (+ (len xs) i) (stvl st-vals))
                       (<= nvars i)
                       (vw-eval-subterm-listp xs nvars
                                              (stvl st-vals)))
                  :guard-hints (("Goal" :in-theory (enable stv-theory-lemmas)))
                  :stobjs (rtime rec st-vals)))
  (if (atom xs)
      st-vals
    (b* (((the (unsigned-byte 60) i)
          (u60 i))
         (x (car xs))
         ;; (- (cw "~p0.~%" x))
         #-(and rec-stobj rec-dcls stv-stobj stv-dcls)
         (st-vals
          (vw-eval-subterm i x cycle nvars rtime rec st-vals))
         #+(and rec-stobj rec-dcls stv-stobj stv-dcls)
         ((the #+simple-vectors simple-vector
               #-simple-vectors (simple-array double-float (*))
               st-vals)
          (the #+simple-vectors simple-vector
               #-simple-vectors (simple-array double-float (*))
               (vw-eval-subterm i x cycle nvars rtime rec st-vals))))
      (vw-eval-subterm-list (cdr xs) (1+ i) cycle nvars rtime rec st-vals))))

(defthm stvl-vw-eval-subterm-list
  (implies (and (natp i)
                (= (+ (len xs) i) (stvl st-vals)))
           (equal (stvl (vw-eval-subterm-list xs i cycle nvars rtime rec
                                              st-vals))
                  (stvl st-vals)))
  :hints
  (("Goal" :in-theory (enable stv-theory-lemmas))))

(defthm st-valsp-vw-eval-subterm
  (implies (and (st-valsp st-vals)
                (<= (len *initial-vars*) (stvl st-vals))
                (natp i)
                (< i (stvl st-vals)))
           (st-valsp (vw-eval-subterm i x cycle nvars rtime rec st-vals)))
  :hints
  (("Goal" :in-theory (e/d (stv-theory-lemmas vw-eval-subterm)
                           ((:e force))))))

(defthm st-valsp-vw-eval-subterm-list
  (implies (and (st-valsp st-vals)
                (<= (len *initial-vars*) (stvl st-vals))
                (natp i)
                (= (+ (len xs) i) (stvl st-vals)))
           (st-valsp (vw-eval-subterm-list xs i cycle nvars rtime rec
                                           st-vals)))
  :hints
  (("Goal" :in-theory (enable stv-theory-lemmas))))

(defthm indices-below-unchanged-by-vw-eval-subterm-list
  (implies (and (natp i)
                (= (+ (len xs) i) (stvl st-vals))
                (natp j)
                (< j i))
           (equal (stvi j (vw-eval-subterm-list xs i cycle nvars rtime rec
                                                st-vals))
                  (stvi j st-vals)))
  :hints
  (("Goal" :in-theory (enable stv-theory-lemmas vw-eval-subterm))))

(defun vw-eval-term-nat-alistp (a)
  (declare (xargs :guard t))
  (if (atom a)
      (null a)
    (let ((pair (car a)))
      (and (consp pair)
           (vw-eval-termp (car pair))
           (natp (cdr pair))
           (vw-eval-term-nat-alistp (cdr a))))))

(defthm vw-eval-term-nat-alistp-foward-to-alistp
  (implies (vw-eval-term-nat-alistp a)
           (alistp a))
  :rule-classes :forward-chaining)

(defthm hons-acons-vw-eval-term-nat-alistp
  (implies (and (vw-eval-term-nat-alistp a)
                (hons-assoc-equal key a))
           (natp (cdr (hons-assoc-equal key a))))
  :hints (("Goal" :induct t))
  :rule-classes :type-prescription)

(defthm strip-cars-vw-eval-term-nat-alistp
  (implies (vw-eval-term-nat-alistp a)
           (vw-eval-term-listp (strip-cars a))))

(defun all-subterms (x a)
  (declare (xargs :guard (and (vw-eval-termp x)
                              (vw-eval-term-nat-alistp a))
                  :verify-guards nil))
  ;; we assume that all symbol (variable) names will be added later to
  ;; the list of subterms in the top-level call of ``all-subterms''.
  (b* (((when (atom x))
        a)

       (fn (car x))
       (fn-num (pos fn *fns*))
       (args (cdr x))

       ;; we always evaluate the first argument of an if.  This
       ;; suggests that maybe evaluation should be done top-down.

       (arg1 (if (<= *if-index* fn-num)
                 (if (< *if-index* fn-num)
                     (all-subterms (car args) a)
                   ;; we do not perform lazy evaluation of if.
                   (all-subterms
                    (caddr args)
                    (all-subterms (cadr args)
                                  (all-subterms (car args)
                                                a))))
               a))

       (arg2 (if (<= *f+-index* fn-num)
                 (all-subterms (cadr args) arg1)
               arg1))

       ;; this is when we add the function
       (final-a (let ((pair (hons-get x arg2)))
                  (if pair
                      arg2
                    (hons-acons x 0 arg2)))))
    final-a))

(defthm vw-eval-term-nat-alistp-all-subterms
  (implies (and (vw-eval-termp x)
                (vw-eval-term-nat-alistp a))
           (vw-eval-term-nat-alistp (all-subterms x a)))
  :rule-classes :type-prescription)

(encapsulate
  ()
  (local
   (defthm vw-eval-termp-first-arg
     (implies (and (vw-eval-termp x)
                   (<= *if-index* (pos (car x) *fns*)))
              (vw-eval-termp (cadr x)))
     :rule-classes :forward-chaining))

  (local
   (defthm vw-eval-termp-second-arg
     (implies (and (vw-eval-termp x)
                   (<= *f+-index* (pos (car x) *fns*)))
              (vw-eval-termp (caddr x)))
     :rule-classes :forward-chaining))

  (verify-guards all-subterms))

(defun all-subterms-list-help (xs a)
  (declare (xargs :guard (and (vw-eval-term-listp xs)
                              (vw-eval-term-nat-alistp a))))
  (if (atom xs)
      a
    (all-subterms-list-help
     (cdr xs)
     (all-subterms (car xs) a))))

(defthm true-listp-vw-eval-term-nat-alistp
  (implies (vw-eval-term-nat-alistp a)
           (true-listp a))
  :rule-classes :forward-chaining)

(defthm vw-eval-term-nat-alistp-all-subterms-list-help
  (implies (and (vw-eval-term-listp xs)
                (vw-eval-term-nat-alistp a))
           (vw-eval-term-nat-alistp (all-subterms-list-help xs a)))
  :rule-classes :type-prescription)

(defthm vw-eval-term-listp-revappend
  (implies (and (vw-eval-term-listp xs1)
                (vw-eval-term-listp xs2))
           (vw-eval-term-listp (revappend xs1 xs2))))

(defthm vw-eval-term-listp-reverse
  (implies (vw-eval-term-listp xs)
           (vw-eval-term-listp (reverse xs))))

(defun all-subterms-list (xs)
  ;; Generates a list of unique subterms from a list of terms.
  (declare (xargs :guard (vw-eval-term-listp xs)))
  (let* ((subterms-alist
          (fast-alist-free
           (all-subterms-list-help xs nil)))
         (list-of-subterms (strip-cars subterms-alist)))
    (reverse list-of-subterms)))


(defthm vw-eval-term-listp-symbol-listp-append
  (implies (and (symbol-listp all-names)
                (vw-eval-term-listp xs))
           (vw-eval-term-listp (append all-names xs))))

(defthm vw-eval-term-listp-all-subterms-list
  (implies (and (vw-eval-term-listp xs)
                ;; (symbol-listp all-names)
                )
           (vw-eval-term-listp (all-subterms-list xs ;; all-names
                                                  ))))

(defun vw-eval-subterm-lookup-okp (x a nvars stv-max)
  (declare (type (unsigned-byte 60) nvars stv-max)
           (xargs :guard (and (vw-eval-termp x)
                              ;; ``a'' is an alist where the keys are
                              ;; terms and the values are their
                              ;; positions in the STV array. We assume
                              ;; that all the subterms of ``x'' are
                              ;; keys in ``a''.
                              (vw-eval-term-nat-alistp a)
                              (<= nvars stv-max))
                  :guard-hints (("Goal" :in-theory (enable pos)))))
  (b* (((if (atom x))
        nil)

       (fn (car x))
       (fn-num (pos fn *fns*))
       (args (cdr x))

       ;; we always evaluate the first argument of an if.  This
       ;; suggests that maybe evaluation should be done top-down.
       (arg1 (if (<= *if-index* fn-num)
                 (let ((arg1-num (cdr (hons-get (car args) a))))
                   (and (natp arg1-num)
                        (< arg1-num stv-max)))
               ;; default value
               nil))

       (arg2 (if (<= *f+-index* fn-num)
                 (let ((arg2-num (cdr (hons-get (cadr args) a))))
                   (and (natp arg2-num)
                        (< arg2-num stv-max)))
               ;; default value
               nil)))

    (case fn-num
      (#.*quote-index* t)

      (#.*back-index*
       ;; (back x ''5) -> (1 <x-index> (0 5))
       (b* ((name (car args))
            (index (cdr (hons-get name a))))
         (and (natp index)
              (< index nvars))))

      ((#.*$time$<-index*
        #.*$time$-$hn$<-index*
        #.*$time$<mod--index*
        #.*$time$-$hn$<mod--index*)
       t)

      (#.*if-index*
       (b* ((if-arg2 (cdr (hons-get (cadr args) a)))
            (if-arg3 (cdr (hons-get (caddr args) a))))
         (and arg1
              (natp if-arg2)
              (natp if-arg3)
              (< if-arg2 stv-max)
              (< if-arg3 stv-max))))

      (#.*f-not-index*   arg1)

      (#.*f0--index*     arg1)
      (#.*f-abs-index*   arg1)
      (#.*f-1/x-index*   arg1)
      (#.*f-sqrt-index*  arg1)
      (#.*f-sin-index*   arg1)
      (#.*f-cos-index*   arg1)
      (#.*f-tan-index*   arg1)
      (#.*f-tanh-index*  arg1)
      (#.*f-exp-index*   arg1)
      (#.*f+-index*      (and arg1 arg2))
      (#.*f--index*      (and arg1 arg2))
      (#.*f*-index*      (and arg1 arg2))
      (#.*f/-index*      (and arg1 arg2))
      (#.*f<-index*      (and arg1 arg2))
      (#.*f=-index*      (and arg1 arg2))
      (#.*f-mod-index*   (and arg1 arg2))
      (otherwise nil))))

(defun vw-eval-term-to-subterm (x a nvars stv-max)
  (declare (type (unsigned-byte 60) nvars stv-max))
  (declare (xargs :guard (and (vw-eval-termp x)
                              (vw-eval-term-nat-alistp a)
                              (<= nvars stv-max)
                              (vw-eval-subterm-lookup-okp
                               x a nvars stv-max)
                              ;; ``a'' is an alist where the keys are
                              ;; terms and the values are their
                              ;; positions in the STV array. We assume
                              ;; that all the subterms of ``x'' are
                              ;; keys in ``a''.
                              )
                  :guard-hints (("Goal" :in-theory (enable pos)))))
  (declare (ignore nvars stv-max))
  (b* (((if (atom x))
        (prog2$ (cw "vw-eval-term-to-subterm: cannot convert a ~
        raw variable.~%")
                0))
       (fn (car x))
       (fn-num (pos fn *fns*))
       (args (cdr x))

       ;; we always evaluate the first argument of an if.  This
       ;; suggests that maybe evaluation should be done top-down.
       (arg1 (if (<= *if-index* fn-num)
                 (cdr (hons-get (car args) a))
               ;; default value
               0))

       (arg2 (if (<= *f+-index* fn-num)
                 (cdr (hons-get (cadr args) a))
               ;; default value
               0)))
    (case fn-num
      (#.*quote-index* (mbe :logic (list fn-num (rfix (car args)))
                            :exec  (list fn-num       (car args))))

      (#.*back-index*
       ;; (back x ''5) -> (1 <x-index> (0 5))
       (b* ((name (car args))
            (index (cdr (hons-get name a)))
            (rational-back-time (unquote (cadr args)))
            (quoted-back-time  (list #.*quote-index* rational-back-time)))
         (list fn-num
               index
               quoted-back-time)))

      (#.*$time$<-index*
       (let (($time$<-arg1 (car args)))
         (list fn-num (list #.*quote-index* (unquote $time$<-arg1)))))

      (#.*$time$-$hn$<-index*
       (let (($time$-$hn$<-arg1 (car args)))
         (list fn-num
               (list #.*quote-index* (unquote $time$-$hn$<-arg1)))))

      (#.*$time$<mod--index*
       (let (($time$<mod--arg1 (car args))
             ($time$<mod--arg2 (cadr args))
             ($time$<mod--arg3 (caddr args)))
         (list fn-num
               (list #.*quote-index* (unquote $time$<mod--arg1))
               (list #.*quote-index* (unquote $time$<mod--arg2))
               (list #.*quote-index* (unquote $time$<mod--arg3)))))

      (#.*$time$-$hn$<mod--index*
       (let (($time$-$hn$<mod--arg1 (car args))
             ($time$-$hn$<mod--arg2 (cadr args))
             ($time$-$hn$<mod--arg3 (caddr args)))
         (list fn-num
               (list #.*quote-index* (unquote $time$-$hn$<mod--arg1))
               (list #.*quote-index* (unquote $time$-$hn$<mod--arg2))
               (list #.*quote-index* (unquote $time$-$hn$<mod--arg3)))))

      (#.*if-index*
       (b* ((if-arg2 (cdr (hons-get (cadr args) a)))
            (if-arg3 (cdr (hons-get (caddr args) a))))
         (list fn-num
               arg1
               if-arg2
               if-arg3)))

      (#.*f-not-index*   (list fn-num arg1))

      (#.*f0--index*     (list fn-num arg1))
      (#.*f-abs-index*   (list fn-num arg1))
      (#.*f-1/x-index*   (list fn-num arg1))
      (#.*f-sqrt-index*  (list fn-num arg1))
      (#.*f-sin-index*   (list fn-num arg1))
      (#.*f-cos-index*   (list fn-num arg1))
      (#.*f-tan-index*   (list fn-num arg1))
      (#.*f-tanh-index*  (list fn-num arg1))
      (#.*f-exp-index*   (list fn-num arg1))
      (#.*f+-index*      (list fn-num arg1 arg2))
      (#.*f--index*      (list fn-num arg1 arg2))
      (#.*f*-index*      (list fn-num arg1 arg2))
      (#.*f/-index*      (list fn-num arg1 arg2))
      (#.*f<-index*      (list fn-num arg1 arg2))
      (#.*f=-index*      (list fn-num arg1 arg2))
      (#.*f-mod-index*   (list fn-num arg1 arg2))
      (otherwise (cw "vw-eval-term-to-subterm: ~p0 is not a vw-eval-termp!~%"
                     x)))))

#||
Examples:
(vw-eval-term-to-subterm '(f+ '2 '3)
 (make-fast-alist '(('2 . 0) ('3 . 1) ((f+ '2 '3) . 2))) 0 3)

(vw-eval-term-to-subterm '(f* (f+ x y) '5)
 (make-fast-alist '((x . 0) (y . 1) ('5 . 2) ((f+ x y) . 3))) 2 4)

||#

(defthm vw-eval-subtermp-vw-eval-term-to-subterm
  (implies (and (vw-eval-termp x)
                (vw-eval-subterm-lookup-okp
                 x a nvars stv-max))
           (vw-eval-subtermp (vw-eval-term-to-subterm x a nvars stv-max)
                             nvars
                             stv-max))
  :hints (("Goal" :in-theory (enable pos))))

(defun vw-eval-subterm-list-lookup-okp (xs a nvars stv-max)
  (declare (type (unsigned-byte 60) nvars stv-max)
           (xargs :guard (and (vw-eval-term-listp xs)
                              ;; ``a'' is an alist where the keys are
                              ;; terms and the values are their
                              ;; positions in the STV array. We assume
                              ;; that all the subterms of ``x'' are
                              ;; keys in ``a''.
                              (vw-eval-term-nat-alistp a)
                              (<= nvars stv-max))))
  (if (atom xs)
      t
    (let ((x (car xs)))
      (and (vw-eval-subterm-lookup-okp x a nvars stv-max)
           (vw-eval-subterm-list-lookup-okp (cdr xs) a nvars stv-max)))))

(defun vw-eval-term-list-to-subterm-list (xs a nvars stv-max)
  (declare (type (unsigned-byte 60) nvars stv-max)
           (xargs :guard (and (vw-eval-term-listp xs)
                              ;; ``a'' is an alist where the keys are
                              ;; terms and the values are their
                              ;; positions in the STV array. We assume
                              ;; that all the subterms of ``x'' are
                              ;; keys in ``a''.
                              (vw-eval-term-nat-alistp a)
                              (<= nvars stv-max)
                              (vw-eval-subterm-list-lookup-okp
                               xs a nvars stv-max))))
  (if (atom xs)
      nil
    (let ((x (car xs)))
      (cons (vw-eval-term-to-subterm x a nvars stv-max)
            (vw-eval-term-list-to-subterm-list (cdr xs) a nvars stv-max)))))

(defun number-list (l i)
  (declare (xargs :guard (natp i)))
  (if (atom l)
      nil
    (cons (cons (car l) i)
          (number-list (cdr l) (1+ i)))))

#+(and stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function (t t (simple-array double-float (*)))
                          (values t))
                stv-help))

(defun stv-help (i n st-vals)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (stvl st-vals)))
                  :stobjs st-vals)
           #+(and stv-stobj stv-dcls (not simple-vectors))
           (type (simple-array double-float (*)) st-vals))
  (if (zp (- n i))
      nil
    (cons (stvi i st-vals)
          (stv-help (1+ i) n st-vals))))

#+(and stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function ((simple-array double-float (*)))
                          (values t))
                stv))

(defun stv (st-vals)
  (declare (xargs :guard t
                  :stobjs st-vals)
           #+(and stv-stobj stv-dcls (not simple-vectors))
           (type (simple-array double-float (*)) st-vals))
  (stv-help 0 (stvl st-vals) st-vals))

#+(and stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function (t t (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                !stv-help))

(defun !stv-help (i l st-vals)
  (declare (xargs :stobjs st-vals
                  :guard (and (num-listp l)
                              (natp i)
                              (<= (+ i (len l)) (stvl st-vals)))
                  :hints (("Goal" :in-theory (enable stv-theory-lemmas)))
                  :guard-hints (("Goal" :in-theory (enable stv-theory-lemmas)))
                  :measure (nfix (- (stvl st-vals) i)))
           #+(and stv-stobj stv-dcls (not simple-vectors))
           (type (simple-array double-float (*)) st-vals))
  (cond
   ((not (mbt (and (true-listp l)
                   (natp i)
                   (<= (+ i (len l)) (stvl st-vals))))) ; impossible
    st-vals)
   ((endp l) st-vals)
   (t (let ((st-vals (!stvi i (car l) st-vals)))
        #+(and stv-stobj stv-dcls (not simple-vectors))
        (declare (type (simple-array double-float (*)) st-vals))
        (!stv-help (1+ i) (cdr l) st-vals)))))

#+(and stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function (t (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                !stv))

(defun !stv (l st-vals)
  ;; update stv field in st-vals with a list of terms
  (declare (xargs :guard (num-listp l)
                  :guard-hints (("Goal" :in-theory (enable stv-theory-lemmas)))
                  :stobjs st-vals)
           #+(and stv-stobj stv-dcls (not simple-vectors))
           (type (simple-array double-float (*)) st-vals))
  (let* ((len (len l))
         (st-vals (if (= len (stvl st-vals))
                      st-vals
                    (resize-stv len st-vals))))
    #+(and stv-stobj stv-dcls (not simple-vectors))
    (declare (type (simple-array double-float (*)) st-vals))
    (!stv-help 0 l st-vals)))

#||

;; assume all constants are already folded away.
(! all-names '($r-time$ $r-hn$ $time$ $hn$ x y z))
(! all-terms '((f* (f+ x y) '5)
               (f/ (f0- z) '25)))
(! all-subs-without-all-names
   (all-subterms-list (@ all-terms)))
(! all-subs-with-all-names (append (@ all-names) (@ all-subs-without-all-names)))
(! terms-to-nats-alist (make-fast-alist (number-list (@ all-subs-with-all-names) 0)))

(vw-eval-term-list-to-subterm-list (@ all-subs-without-all-names)
                                   (@ terms-to-nats-alist)
                                   (len (@ all-names))
                                   (len (@ all-subs-with-all-names)))

||#

