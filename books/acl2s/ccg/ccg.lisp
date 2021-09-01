#|$ACL2s-Preamble$;

(begin-book t :ttags ((:ccg)));$ACL2s-Preamble$|#

(in-package "ACL2")

(defttag :ccg)

; load in the expander book.

(include-book "misc/expander" :dir :system)
(include-book "acl2s/acl2s-size" :dir :system)

; load in Peter's hacker stuff.  we use at least three things from this:
; - add several keys to the acl2-defaults-table
; - make raw Lisp definitions from an acl2 book, i.e. defstruct-raw,
;   defmacro-raw, and defun-raw
; - bridge raw lisp and ACL2 so that we can access the raw Lisp code
;
(include-book "hacking/hacker" :dir :system)
(progn+all-ttags-allowed
 (include-book "hacking/all" :dir :system :ttags :all))
(subsume-ttags-since-defttag)

; From ACL2 source file defthm.lisp, utilities.lisp
; Matt K. mod: now in logic mode, guard-verified.
#|
(defun fix-pkg (pkg)
  (declare (xargs :guard (and (or (null pkg) (stringp pkg))
                              (not (equal pkg "")))))
  (if (and pkg (not (equal pkg *main-lisp-package-name*)))
      pkg
    "ACL2"))
|#

(defmacro fix-intern$ (name pkg)
  `(intern$ ,name (fix-pkg ,pkg)))

;;; Legacy doc strings replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.


; BEGIN public configuration interface

; add :termination-method key to acl2-defaults-table
;
; add-acl2-defaults-table-key is provided by my hacker stuff. -Peter

(add-acl2-defaults-table-key :termination-method
                             (member-eq val '(:measure :ccg)))



(defun get-termination-method (wrld)
  ;; ":Doc-Section CCG

  ;; Returns the current default termination method.~/

  ;; ~bv[]
  ;; Examples:
  ;; (get-termination-method (w state))
  ;; ~ev[]

  ;; This will return the termination-method as specified by the current world. ~/

  ;; ~bv[]
  ;; General Form:
  ;; (get-termination-method wrld)
  ;; ~ev[]

  ;; where ~c[wrld] is a ~il[world]. For information on the settings and
  ;; their meaning, ~pl[set-termination-method].~/"

  (declare (xargs :guard (and (plist-worldp wrld)
                              (alistp (table-alist 'acl2-defaults-table wrld)))))
  (let ((entry (assoc :termination-method (table-alist 'acl2-defaults-table wrld))))
    (or (and entry (cdr entry)) :measure)))

(verify-guards get-termination-method)

(defmacro hlevel-proof-technique (hlevel)
  `(car ,hlevel))

(defmacro hlevel-ccm-comparison-scheme (hlevel)
  `(cadr ,hlevel))

(defmacro hlevel-ccmfs-per-nodep (hlevel)
  `(caddr ,hlevel))

(defmacro make-hlevel (pt ccm-cs cpn)
  `(list ,pt ,ccm-cs ,cpn))

(defun proof-techniquep (pt)

; checks whether pt is a valid "proof technique" as described in the
; documentation for the set-ccg-hierarchy. That is, this function returns true
; if pt is :built-in-clauses or of the form (:induction-depth n) for some
; natural number n.

  (declare (xargs :guard t))
  (or (and (keywordp pt)
           (eq pt :built-in-clauses))
      (and (consp pt)
           (keywordp (car pt))
           (eq (car pt) :induction-depth)
           (consp (cdr pt))
           (natp (cadr pt))
           (null (cddr pt)))))

(defun hlevelp (hlevel)
  (declare (xargs :guard t))

; returns non-nil if hlevel is a valid level of a CCG hierarchy. That is,
; the result is non-nil if it is of the form (:measure pt) or (pt ccm-cs cpn)
; where pt satisfies proof-techniquep, ccm-cs is one of :EQUAL, :ALL, :SOME, or
; :NONE, and cpn is a boolean.

  (and (consp hlevel)
       (or (and (keywordp (car hlevel))
                (eq (car hlevel) :measure)
                (consp (cdr hlevel))
                (proof-techniquep (cadr hlevel))
                (null (cddr hlevel)))
           (and (proof-techniquep (car hlevel))
                (consp (cdr hlevel))
                (member-eq (cadr hlevel) '(:EQUAL :ALL :SOME :NONE))
                (consp (cddr hlevel))
                (booleanp (caddr hlevel))
                (null (cdddr hlevel))))))

(defun hlevel-listp (lst)
  (declare (xargs :guard t))

; returns non-nil iff lst is a true-list of elements satisfying hlevelp.

  (if (consp lst)
      (and (hlevelp (car lst))
           (hlevel-listp (cdr lst)))
    (null lst)))

(defun non-empty-hlevel-listp (lst)
  (declare (xargs :guard t))
  (and (consp lst)
       (hlevel-listp lst)))

(defun hlevel< (hlevel0 hlevel1)

; a non-transitive comparison function for arguments that are non-measure
; levels of a CCG hierarchy. The definition is designed to return t if the CCG
; analysis, using the techniques described in hlevel1 could possibly further
; refine an annotated CCG that had already been refined using the techniques
; described in hlevel0. That is, hlevel< returns t if hlevel0 does *not*
; subsume hlevel1.

  (declare (xargs :guard (and (hlevelp hlevel0)
                              (not (equal (car hlevel0)
                                          :measure))
                              (hlevelp hlevel1)
                              (not (equal (car hlevel1)
                                          :measure)))))
  (let ((pt0 (hlevel-proof-technique hlevel0))
        (ccm-cs0 (hlevel-ccm-comparison-scheme hlevel0))
        (cpn0 (hlevel-ccmfs-per-nodep hlevel0))
        (pt1 (hlevel-proof-technique hlevel1))
        (ccm-cs1 (hlevel-ccm-comparison-scheme hlevel1))
        (cpn1 (hlevel-ccmfs-per-nodep hlevel1)))

; if cpn0 is t and cpn1 is nil (hlevel0 calculates CCMFs on a per-node basis,
; and hlevel1 on a per-edge basis), then we return t.

    (or (and cpn0 (not cpn1))

; if hlevel1 has a stronger proof technique than hlevel0, then return t.

        (and (not (equal pt1 :built-in-clauses))
             (or (equal pt0 :built-in-clauses)
                 (< (cadr pt0) (cadr pt1))))

; if hlevel1 has a more comprehensive CCM comparison scheme, then return t.

        (let ((ccm-cs-vals '((:EQUAL . 0)
                             (:ALL . 1)
                             (:SOME . 2)
                             (:NONE . 3))))
          (< (cdr (assoc ccm-cs0 ccm-cs-vals))
             (cdr (assoc ccm-cs1 ccm-cs-vals)))))))

(rewrite-table-guard
 acl2-defaults-table
 (:carpat %body%
  :vars %body%
  :repl (if (eq key :ccg-hierarchy)
            (non-empty-hlevel-listp val)
          %body%)))


(defun fix-ccg-hierarchy (hierarchy)
  (declare (xargs :guard (or (consp hierarchy)
                             (and (symbolp hierarchy)
                                  (member-eq hierarchy
                                             '(:CCG-ONLY
                                               :CCG-ONLY-CPN
                                               :HYBRID
                                               :HYBRID-CPN))))))


; if hierarchy is a symbol designating one of the pre-defined hierarchies,
; return the hierarchy that it represents. Otherwise, return hierarchy.

  (if (consp hierarchy)
      hierarchy
    (case hierarchy
      (:CCG-ONLY
       '((:built-in-clauses :equal t)
         ((:induction-depth 0) :EQUAL t)
         ((:induction-depth 1) :EQUAL t)
         ((:induction-depth 1) :ALL   t)
         ((:induction-depth 1) :SOME  t)
         ((:induction-depth 1) :NONE  t)
         ((:induction-depth 1) :EQUAL nil)
         ((:induction-depth 1) :ALL   nil)
         ((:induction-depth 1) :SOME  nil)
         ((:induction-depth 1) :NONE  nil)))
        (:CCG-ONLY-CPN
         '((:built-in-clauses :equal t)
           ((:induction-depth 0) :EQUAL t)
           ((:induction-depth 1) :EQUAL t)
           ((:induction-depth 1) :ALL   t)
           ((:induction-depth 1) :SOME  t)
           ((:induction-depth 1) :NONE  t)))
        (:HYBRID
         '((:built-in-clauses :equal t)
           (:measure (:induction-depth 1))
           ((:induction-depth 0) :EQUAL t)
           ((:induction-depth 1) :EQUAL t)
           ((:induction-depth 1) :ALL   t)
           ((:induction-depth 1) :SOME  t)
           ((:induction-depth 1) :NONE  t)
           ((:induction-depth 1) :EQUAL nil)
           ((:induction-depth 1) :ALL   nil)
           ((:induction-depth 1) :SOME  nil)
           ((:induction-depth 1) :NONE  nil)))
        (:HYBRID-CPN
         '((:built-in-clauses :equal t)
           (:measure (:induction-depth 1))
           ((:induction-depth 0) :EQUAL t)
           ((:induction-depth 1) :EQUAL t)
           ((:induction-depth 1) :ALL   t)
           ((:induction-depth 1) :SOME  t)
           ((:induction-depth 1) :NONE  t)))
        (otherwise
         nil))))

(defun get-ccg-hierarchy (wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (alistp (table-alist 'acl2-defaults-table
                                                   wrld)))))

; gets the default ccg hierarchy from the acl2-defaults-table. the default is
; :CCG-ONLY.

  (let ((entry (assoc :ccg-hierarchy (table-alist 'acl2-defaults-table wrld))))
    (if (null entry)
        (fix-ccg-hierarchy :CCG-ONLY)
      (cdr entry))))

(set-state-ok t)
(program)

(defun chk-ccg-hierarchy1 (hierarchy cpn ctx state)

; checks the given hierarchy to assure that it conforms to the proper form.
; if cpn is nil, all levels of the hierarchy must have a cpn of nil. Otherwise,
; this function checks that there are no levels of the hierarchy with cpn t
; that come after levels with a cpn of nil (once you switch from CCMFs per-node
; to CCMFs per-edge, you cannot go back). The ctx and state are there to enable
; error reporting. This function returns an error triple whose value is nil if
; everything checks out.

  (cond ((endp hierarchy)
         (value nil))
        ((not (hlevelp (car hierarchy)))
         (er soft ctx
             "Each element of a CCG-HIERARCHY must either have the form (PT ~
              CCM-CS CPN) or (:MEASURE PT), where PT is either ~
              :BUILT-IN-CLAUSES or (:INDUCTION-DEPTH N) for some natural ~
              number, N, CCM-CS is one of :EQUAL, :ALL, :SOME, :NONE, and CPN ~
              is either T or NIL. ~x0 does not match this form."
             (car hierarchy)))
        ((and (not cpn)
              (not (equal (caar hierarchy) :MEASURE))
              (hlevel-ccmfs-per-nodep (car hierarchy)))
         (er soft ctx
             "It is not permitted that a level of a CCG-HIERARCHY have a ~
              CCCMFs-per-nodep of T when a previous level had a ~
              CCMFs-per-nodep of NIL. But this is the case with level ~x0."
             (car hierarchy)))
        (t
         (chk-ccg-hierarchy1 (cdr hierarchy)
                             (if (equal (caar hierarchy) :measure)
                                 cpn
                               (hlevel-ccmfs-per-nodep (car hierarchy)))
                             ctx state))))

(defun chk-measure-hlevel<-all (hlevel0 hierarchy ctx state)

; ensures that none of the measure levels of hierarchy are subsumed by hlevel0.

  (cond ((endp hierarchy)
         (value nil))
        ((or (not (equal (caar hierarchy) :measure))
             (and (consp (cadar hierarchy))
                  (or (atom (cadr hlevel0))
                      (< (cadadr hlevel0) (cadadr (car hierarchy))))))
         (chk-measure-hlevel<-all hlevel0 (cdr hierarchy) ctx state))
        (t
         (er soft ctx
             "Each :MEASURE level of a CCG-HIERARCHY should use strictly more ~
              powerful proof techniques than all those that come before it. ~
              However, the ~x0 level is subsumed by the earlier level, ~x1."
             (car hierarchy)
             hlevel0))))

(defun chk-hlevel<-all (hlevel0 hierarchy ctx state)

; insures that none of the CCG levels of the hierarchy are subsumed by
; hlevel0.

  (cond ((endp hierarchy)
         (value nil))
        ((or (equal (caar hierarchy) :MEASURE)
             (hlevel< hlevel0 (car hierarchy)))
         (chk-hlevel<-all hlevel0 (cdr hierarchy) ctx state))
        (t
         (er soft ctx
             "Each level of a CCG-HIERARCHY should be strictly more powerful ~
              than all the previous levels. That is, it should always be ~
              possible to refine the CCG or CCMF information at each step in ~
              the hierarchy. However, the ~x0 level is subsumed by the ~
              earlier level, ~x1."
             (car hierarchy)
             hlevel0))))

(defun chk-hierarchy-strictly-increasing (hierarchy ctx state)

; ensures that no level of hierarchy is subsumed by a later level.

  (if (endp hierarchy)
      (value nil)
    (er-progn
     (cond ((equal (caar hierarchy) :MEASURE)
            (chk-measure-hlevel<-all (car hierarchy) (cdr hierarchy)
                                     ctx state))
           (t
            (chk-hlevel<-all (car hierarchy) (cdr hierarchy)
                             ctx state)))
     (chk-hierarchy-strictly-increasing (cdr hierarchy) ctx state))))

(defun chk-ccg-hierarchy (hierarchy ctx state)

; checks a proposed CCG hierarchy.

  (cond ((and (symbolp hierarchy)
              (member-eq hierarchy '(:CCG-ONLY
                                     :CCG-ONLY-CPN
                                     :HYBRID
                                     :HYBRID-CPN)))
         (value nil))
        ((and (consp hierarchy)
              (true-listp hierarchy))
         (er-progn
          (chk-ccg-hierarchy1 hierarchy t ctx state)
          (chk-hierarchy-strictly-increasing hierarchy ctx state)))
        (t
         (er soft ctx
             "A CCG-HIERARCHY must be :CCG-ONLY, :CCG-ONLY-CPN, :HYBRID, ~
              :HYBRID-CPN, or a non-empty true-list. ~x0 does not have ~
              this form."
             hierarchy))))

(defmacro set-ccg-hierarchy (v)
    ;; ":Doc-Section CCG

    ;;  Set the default hierarchy of techniques for CCG-based termination
    ;;  analysis. ~/
    ;;  ~bv[]
    ;;  (set-ccg-hierarchy ((:built-in-clauses :equal t)
    ;;                      (:measure (:induction-depth 1))
    ;;                      ((:induction-depth 0) :EQUAL t)
    ;;                      ((:induction-depth 1) :EQUAL t)
    ;;                      ((:induction-depth 1) :ALL   t)
    ;;                      ((:induction-depth 1) :SOME  t)
    ;;                      ((:induction-depth 1) :NONE  t)
    ;;                      ((:induction-depth 1) :EQUAL nil)
    ;;                      ((:induction-depth 1) :ALL   nil)
    ;;                      ((:induction-depth 1) :SOME  nil)
    ;;                      ((:induction-depth 1) :NONE  nil)))
    ;;  :set-ccg-hierarchy ((:built-in-clauses :equal t)
    ;;                      ((:induction-depth 0) :EQUAL t)
    ;;                      ((:induction-depth 1) :EQUAL t)
    ;;                      ((:induction-depth 1) :ALL   t)
    ;;                      ((:induction-depth 1) :SOME  t)
    ;;                      ((:induction-depth 1) :NONE  t))~/

    ;;  General Form:
    ;;  (set-ccg-hierarchy v)
    ;;  ~ev[]
    ;;  where ~c[v] is ~c[:CCG-ONLY], ~c[:CCG-ONLY-CPN], ~c[:HYBRID],
    ;;  ~c[:HYBRID-CPN], or a non-empty list of hierarchy levels, which either
    ;;  have the form ~c[(pt ccm-cs cpn)] or the form ~c[(:measure pt)], where
    ;;  ~c[pt] is either ~c[:built-in-clauses] or ~c[(:induction-depth n)] for
    ;;  some natural number ~c[n], ~c[ccm-cs] is one of ~c[:EQUAL], ~c[:ALL],
    ;;  ~c[:SOME], or ~c[:NONE], and ~c[cpn] is ~c[t] or ~c[nil].

    ;;  Each level of the hierarchy describes techniques used to prove
    ;;  termination. Termination proofs performed after admitting this event will
    ;;  use the specified techniques in the order in which they are listed.

    ;;  Basically, the CCG analysis as described and illustrated at a high level
    ;;  in the documentation for ~il[CCG] can potentially be very expensive. In
    ;;  order to make the analysis as efficient as possible, we use less expensive
    ;;  (and less powerful) techniques first, and resort to more powerful and
    ;;  expensive techniques only when these fail.

    ;;  There are three ways of varying the CCG analysis, which are represented by
    ;;  each of the three elements in a hierarchy level (levels of the form
    ;;  ~c[(:measure pt)] will be explained later).

    ;;  ~c[Pt] tells the CCG analysis how to limit proof attempts. The idea behind
    ;;  this is that ACL2 is designed to prove statements that the user thinks are
    ;;  true. It therefore does everything it can to prove the conjecture. As ACL2
    ;;  useres already know, this can lead to very long, or even non-terminating
    ;;  proof attempts. The CCG analysis, on the other hand, sends multiple
    ;;  queries to the theorem prover that may or may not be true, in order to
    ;;  improve the accuracy of the analysis. It is therefore necessary to reign
    ;;  in ACL2's proof attempts to keep them from taking too long. Of course, the
    ;;  trade-off is that, the more we limit ACL2's prover, the less powerful it
    ;;  becomes.

    ;;  ~c[Pt] can be ~c[:built-in-clauses], which tells ACL2 to use only
    ;;  ~il[built-in-clauses] analysis. This is a very fast, and surprisingly
    ;;  powerful proof technique. For example, the definition of Ackermann's
    ;;  function given in the documentation for ~il[CCG] is solved using only this
    ;;  proof technique.

    ;;  ~c[Pt] can also be of the form ~c[(:induction-depth n)], where ~c[n] is a
    ;;  natural number. This uses the full theorem prover, but limits it in two
    ;;  ways. First, it stops proof attempts if ACL2 has been working on a subgoal
    ;;  with no case splitting or induction for 20 steps (that is, at a goal of
    ;;  the form 1.5'20'). It also limits the ~em[induction depth], which
    ;;  describes how many times we allow induction goals to lead to further
    ;;  induction goals. For example, ~c[(:induction-depth 0)] allows no
    ;;  induction, while ~c[(:induction-depth 1)] allows goals of the form ~c[*1]
    ;;  or ~c[*2], but stops if it creates a goal such as ~c[*1.1] or ~c[*2.1].

    ;;  ~c[Ccm-cs] limits which CCMs are compared using the theorem
    ;;  prover. Consider again the ~c[ack] example in the documentation for
    ;;  ~il[CCG]. All we needed was to compare the value of ~c[(acl2s-size x)]
    ;;  before and after the recursive call and the value of ~c[(acl2s-size y)]
    ;;  before and after the recursive call. We would learn nothing, and waste
    ;;  time with the theorem prover if we compared ~c[(acl2s-size x)] to
    ;;  ~c[(acl2s-size y)]. However, other times, it is important to compare CCMs
    ;;  with each other, for example, when arguments are permuted, or we are
    ;;  dealing with a mutual recursion.

    ;;  ~c[Ccm-cs] can be one of ~c[:EQUAL], ~c[:ALL], ~c[:SOME], or
    ;;  ~c[:NONE]. These limit which CCMs we compare based on the variables they
    ;;  mention. Let ~c[c] be a recursive call in the body of function ~c[f] that
    ;;  calls function ~c[g]. Let ~c[m1] be a CCM for ~c[f] and ~c[m2] be a CCM
    ;;  for ~c[g]. Let ~c[v1] be the formals mentioned in ~c[m1] and ~c[v2] be the
    ;;  formals mentioned in ~c[m2'] where ~c[m2'] is derived from ~c[m2] by
    ;;  substituting the formals of ~c[g] with the actuals of ~c[c]. For example,
    ;;  consider following function:
    ;;  ~bv[]
    ;;  (defun f (x)
    ;;    (if (endp x)
    ;;        0
    ;;      (1+ (f (cdr x)))))
    ;;  ~ev[]
    ;;  Now consider the case where ~c[m1] and ~c[m2] are both the measure
    ;;  ~c[(acl2s-size x)]. Then if we look at the recursive call ~c[(f (cdr x))]
    ;;  in the body of ~c[f], then ~c[m2'] is the result of replacing ~c[x] with
    ;;  ~c[(cdr x)] in ~c[m2], i.e., ~c[(acl2s-size (cdr x))].

    ;;  If ~c[ccm-cs] is ~c[:EQUAL] we will compare ~c[m1] to
    ;;  ~c[m2] if ~c[v1] and ~c[v2] are equal. If ~c[value] is ~c[:ALL] we will
    ;;  compare ~c[m1] to ~c[m2'] if ~c[v2] is a subset of ~c[v1]. If ~c[value] is
    ;;  ~c[:SOME] we will compare ~c[m1] to ~c[m2'] if ~c[v1] and ~c[v2]
    ;;  intersect. If ~c[value] is ~c[:NONE] we will compare ~c[m1] to ~c[m2] no
    ;;  matter what.

    ;;  There is one caveat to what was just said: if ~c[m1] and ~c[m2] are
    ;;  syntactically equal, then regardless of the value of ~c[ccm-cs] we will
    ;;  construct a CCMF that will indicate that ~c[(o>= m1 m2)].


    ;;  ~c[Cpn] tells us how much ruler information we will use to compare CCMs.
    ;;  Unlike ACL2's measure-based termination analysis, CCG has the ability to
    ;;  use the rulers from both the current recursive call the next recursive
    ;;  call when constructing the CCMFs. That is, instead of asking ``What
    ;;  happens when I make recursive call A?'', we can ask, ``What happens when
    ;;  execution moves from recursive call A to recursive call B?''. Using this
    ;;  information potentially strengthens the termination analysis. For a brief
    ;;  example, consider the following code:
    ;;  ~bv[]
    ;;  (defun half (x)
    ;;     (if (zp x)
    ;;         0
    ;;       (1+ (half (- x 2)))))
    ;;  ~ev[]

    ;;  Clearly this is terminating. If we choose a measure of ~c[(nfix x)] we
    ;;  know that if ~c[x] is a positive integer, ~c[(nfix (- x 2))] is less than
    ;;  ~c[(nfix x)]. But consider the measure ~c[(acl2s-size x)]. The strange
    ;;  thing here is that if ~c[x] is 1, then ~c[(acl2s-size (- x 2))] is
    ;;  ~c[(acl2s-size -1)], which is 1, i.e. the ~c[acl2s-size] of ~c[x]. So, the
    ;;  fact that we know that ~c[x] is a positive integer is not enough to show
    ;;  that this measure decreases. But notice that if ~c[x] is 1, we will recur
    ;;  just one more time. So, if we consider what happens when we move from the
    ;;  recursive call back to itself. In this case we know
    ;; ~c[(and (not (zp x)) (not (zp (- x 2))))].
    ;;  Under these conditions, it is trivial for ACL2 to prove that
    ;;  ~c[(acl2s-size (- x 2))] is always less than ~c[(acl2s-size x)].

    ;;  However, this can make the CCG analysis much more expensive, since
    ;;  information about how values change from step to step are done on a
    ;;  per-edge, rather than a per-node basis in the CCG (where the nodes are the
    ;;  recursive calls and the edges indicate that execution can move from one
    ;;  call to another in one step). Thus, calculating CCMFs (how values change
    ;;  across recursive calls) on a per-edge basis rather than a per-node basis
    ;;  can require n^2 instead of n prover queries.

    ;;  If ~c[cpn] is ~c[t], we will use only the ruler of the current recursive
    ;;  call to compute our CCMFs. If it is ~c[nil], we will use the much more
    ;;  expensive technique of using the rulers of the current and next call.

    ;;  Levels of the hierarchy of the form ~c[(:measure pt)] specify that the CCG
    ;;  analysis is to be set aside for a step, and the traditional measure-based
    ;;  termination proof is to be attempted. Here, ~c[pt] has the same meaning as
    ;;  it does in a CCG hierarchy level. That is, it limits the measure proof in
    ;;  order to avoid prohibitively long termination analyses.

    ;;  The user may specify their own hierarchy in the form given above. The main
    ;;  restriction is that no level may be subsumed by an earlier level. That is,
    ;;  it should be the case at each level of the hierarchy, that it is possible
    ;;  to discover new information about the CCG that could help lead to a
    ;;  termination proof.

    ;;  In addition to constructing his or her own CCG hierarchy, the user may use
    ;;  several preset hierarchies:

    ;;  ~bv[]
    ;;  :CCG-ONLY
    ;;  ((:built-in-clauses :equal t)
    ;;   ((:induction-depth 0) :EQUAL t)
    ;;   ((:induction-depth 1) :EQUAL t)
    ;;   ((:induction-depth 1) :ALL   t)
    ;;   ((:induction-depth 1) :SOME  t)
    ;;   ((:induction-depth 1) :NONE  t)
    ;;   ((:induction-depth 1) :EQUAL nil)
    ;;   ((:induction-depth 1) :ALL   nil)
    ;;   ((:induction-depth 1) :SOME  nil)
    ;;   ((:induction-depth 1) :NONE  nil))

    ;;  :CCG-ONLY-CPN
    ;;  ((:built-in-clauses :equal t)
    ;;   ((:induction-depth 0) :EQUAL t)
    ;;   ((:induction-depth 1) :EQUAL t)
    ;;   ((:induction-depth 1) :ALL   t)
    ;;   ((:induction-depth 1) :SOME  t)
    ;;   ((:induction-depth 1) :NONE  t))

    ;;  :HYBRID
    ;;  ((:built-in-clauses :equal t)
    ;;   (:measure (:induction-depth 1))
    ;;   ((:induction-depth 0) :EQUAL t)
    ;;   ((:induction-depth 1) :EQUAL t)
    ;;   ((:induction-depth 1) :ALL   t)
    ;;   ((:induction-depth 1) :SOME  t)
    ;;   ((:induction-depth 1) :NONE  t)
    ;;   ((:induction-depth 1) :EQUAL nil)
    ;;   ((:induction-depth 1) :ALL   nil)
    ;;   ((:induction-depth 1) :SOME  nil)
    ;;   ((:induction-depth 1) :NONE  nil))

    ;;  :HYBRID-CPN
    ;;  ((:built-in-clauses :equal t)
    ;;   (:measure (:induction-depth 1))
    ;;   ((:induction-depth 0) :EQUAL t)
    ;;   ((:induction-depth 1) :EQUAL t)
    ;;   ((:induction-depth 1) :ALL   t)
    ;;   ((:induction-depth 1) :SOME  t)
    ;;   ((:induction-depth 1) :NONE  t))
    ;;  ~ev[]

    ;;  The default hierarchy for CCG termination analysis is :CCG-ONLY.~/"

  `(er-progn
    (chk-ccg-hierarchy ',v "SET-CCG-HIERARCHY" state)
    (with-output :off summary
     (progn (table acl2-defaults-table ':ccg-hierarchy ',(fix-ccg-hierarchy v))
            (table acl2-defaults-table ':ccg-hierarchy)))))

;; adds :ccg-time-limit to the acl2-global-table.

(add-acl2-defaults-table-key :ccg-time-limit
                             (or (null val)
                                 (and (rationalp val)
                                      (< 0 val))))

(logic)
(set-state-ok nil)



(defun get-ccg-time-limit (wrld)
  ;; ":Doc-Section CCG

  ;; Returns the current default ccg-time-limit setting.~/

  ;; ~bv[]
  ;; Examples:
  ;; (get-ccg-time-limit (w state))
  ;; ~ev[]

  ;; This will return the time-limit as specified by the current world. ~/

  ;; ~bv[]
  ;; General Form:
  ;; (get-time-limit wrld)
  ;; ~ev[]

  ;; where ~c[wrld] is a ~il[world]. For information on the settings and
  ;; their meaning, ~pl[set-termination-method].~/"

  (declare (xargs :guard (and (plist-worldp wrld)
                              (alistp (table-alist 'acl2-defaults-table wrld)))))
  (let ((entry (assoc :ccg-time-limit (table-alist 'acl2-defaults-table wrld))))
    (or (and entry (cdr entry)) nil)))

(verify-guards get-ccg-time-limit)

(defmacro set-ccg-print-proofs (v)
  ;; ":Doc-Section CCG

  ;;  controls whether proof attempts are printed during CCG analysis~/

  ;;  ~bv[]
  ;;  Examples:
  ;;  (set-ccg-print-proofs t)
  ;;  (set-ccg-print-proofs nil)
  ;;  :set-ccg-print-proofs t~/

  ;;  General Form:
  ;;  (set-ccg-print-proofs v)
  ;;  ~ev[]
  ;;  If ~c[v] is ~c[nil], no proof attempts will be printed during CCG
  ;;  analysis. This is the default. If ~c[v] is anything but ~c[nil], proofs will
  ;;  be displayed. Fair warning: there is potentially a large amount of prover
  ;;  output that might be displayed. It is probably better to use
  ;;  ~l[set-ccg-inhibit-output-lst] to un-inhibit ~c['query] output to figure out
  ;;  what lemmas might be needed to get a given query to go through."

 `(assign ccg-print-proofs ,v))

(defmacro get-ccg-print-proofs ()
  ;; ":Doc-Section CCG

  ;; returns the setting that controls whether proof attempts are printed during
  ;; CCG analysis~/

  ;; ~bv[]
  ;; Examples:
  ;; (get-ccg-print-proofs)
  ;; :get-ccg-print-proofs
  ;; ~ev[]~/

  ;; See ~l[set-ccg-print-proofs] for details."
 '(and (f-boundp-global 'ccg-print-proofs state)
       (f-get-global 'ccg-print-proofs state)))

;; The following code is used to implement a parallel to io? as defined in
;; basis.lisp. Make sure this all stays in sync with the parallel definitions
;; in that file. To find out more, see the "Essay on Inhibited Output and the
;; Illusion of Windows" in the comments of basis.lisp.

;; *ccg-window-descriptions* parallels *window-descriptions* as defined in
;; basis.lisp. See the comments there for details.

(defconst *ccg-window-descriptions*
;                    str clr top pop
  '((query           "4" nil nil nil)
    (basics          "4" nil nil nil)
    (performance     "4" nil nil nil)
    (build/refine    "4" nil nil nil)
    (size-change     "4" nil nil nil)
    (counter-example "4" nil nil nil)))

;; The following mirrors *valid-output-names* as defined in axioms.lisp. This
;; is the list of valid io "kinds" that can be inhibited.

(defconst *ccg-valid-output-names*
  '(query basics performance build/refine size-change counter-example))

(defmacro set-ccg-inhibit-output-lst (lst)
 ;; ":Doc-Section CCG

 ;;  control output during CCG termination analysis~/
 ;;  ~bv[]
 ;;  Examples:
 ;;  (set-ccg-inhibit-output-lst '(query))
 ;;  (set-ccg-inhibit-output-lst '(build/refine size-change))
 ;;  (set-ccg-inhibit-output-lst *ccg-valid-output-names*) ; inhibit all ccg output
 ;;  :set-ccg-inhibit-output-lst (build/refine size-change)~/

 ;;  General Form:
 ;;  (set-ccg-inhibit-output-lst lst)
 ;;  ~ev[]
 ;;  where ~c[lst] is a form (which may mention ~ilc[state]) that evaluates
 ;;  to a list of names, each of which is the name of one of the
 ;;  following ``kinds'' of output produced by the CCG termination analysis.
 ;;  ~bv[]
 ;;    query            prints the goal, restrictions, and results of each prover
 ;;                     query (for a discussion on displaying actual proofs,
 ;;                     see ~c[set-ccg-display-proofs](yet to be documented).
 ;;    basics           the basic CCG output, enough to follow along, but concise
 ;;                     enough to keep from drowning in output
 ;;    performance      performance information for the size change analysis
 ;;    build/refine     the details of CCG construction and refinement
 ;;    size-change      the details of size change analysis
 ;;    counter-example  prints out a counter-example that can be useful for
 ;;                     debugging failed termination proof attempts.
 ;;  ~ev[]
 ;;  It is possible to inhibit each kind of output by putting the corresponding
 ;;  name into ~c[lst].  For example, if ~c['query] is included in (the value of)
 ;;  ~c[lst], then no information about individual queries is printed during CCG
 ;;  analysis.

 ;;  The default setting is ~c['(query performance build/refine size-change)].
 ;;  That is, by default only the basic CCG information and counter-example (in
 ;;  the case of a failed proof attempt) are printed. This should hopefully be
 ;;  adequate for most users."

  `(let ((lst ,lst))
     (cond ((not (true-listp lst))
            (er soft 'set-ccg-inhibit-output-lst
                "The argument to set-ccg-inhibit-output-lst must evaluate to a ~
                 true-listp, unlike ~x0."
                lst))
           ((not (subsetp-eq lst *ccg-valid-output-names*))
            (er soft 'set-ccg-inhibit-output-lst
                "The argument to set-ccg-inhibit-output-lst must evalutate to a ~
                 subset of the list ~X01, but ~x2 contains ~&3."
                *ccg-valid-output-names*
                nil
                ',lst
                (set-difference-eq lst *ccg-valid-output-names*)))
           (t (pprogn
               (f-put-global 'ccg-inhibit-output-lst lst state)
               (value lst))))))

(defmacro get-ccg-inhibit-output-lst ()
  ;; ":Doc-Section CCG

  ;; returns the list of ``kinds'' of output that will be inhibited during CCG
  ;; analysis~/


  ;; ~bv[]
  ;; Examples:
  ;; (get-ccg-inhibit-output-lst)
  ;; :get-ccg-inhibit-output-lst
  ;; ~bv[]~/

  ;; See ~l[set-ccg-inhibit-output-lst]."
  '(if (f-boundp-global 'ccg-inhibit-output-lst state)
       (f-get-global 'ccg-inhibit-output-lst state)
     '(query performance build/refine size-change)))

(program)
(set-state-ok t)

(defmacro ccg-io? (token commentp shape vars body
                     &key
                     (clear 'nil clear-argp)
                     (cursor-at-top 'nil cursor-at-top-argp)
                     (pop-up 'nil pop-up-argp)
                     (default-bindings 'nil)
                     (chk-translatable 't))

; NOTE: Keep this in sync with io? as defined in basis.lisp. This definition is
; almost identical to that one, except we use *ccg-window-descriptions* and
; *ccg-valid-output-names* instead of *window-descriptions* and
; *valid-output-names*, and we store our inhibited-lst in the global table
; under the symbol 'ccg-inhibit-output-lst instead of 'inhibit-output-lst. The
; remaining comments in this definition are from the original io? definition:

; Typical use (io? error nil (mv col state) (x y) (fmt ...)), meaning execute
; the fmt statement unless 'error is on 'inhibit-output-lst.  The mv expression
; is the shape of the output produced by the fmt expression, and the list (x y)
; for vars indicates the variables other than state that occur free in that
; expression.  See the comment above, and see the Essay on Saved-output for a
; comment that gives a convenient macro for obtaining the free variables other
; than state that occur free in body.

; Default-bindings is a list of doublets (symbol value).  It is used in order
; to supply a non-nil return value for other than state when io is suppressed.
; For example, fmt returns col and state, as suggested by the third (shape)
; argument below.  Without the :default-bindings, this form would evaluate to
; (mv nil state) if event IO is inhibited.  But there are fixnum declarations
; that require the first return value of fmt to be an integer, and we can
; specify the result in the inhibited case to be (mv 0 state) with the
; following :default-bindings:

; (io? event nil (mv col state) nil (fmt ...) :default-bindings ((col 0)))

; The values in :default-bindings are evaluated, so it would be equivalent to
; replace 0 with (- 4 4), for example.

    (declare (xargs :guard (and (symbolp token)
                              (symbol-listp vars)
                              (no-duplicatesp vars)
                              (not (member-eq 'state vars))
                              (assoc-eq token *ccg-window-descriptions*))))
  (let* ((associated-window (assoc-eq token *ccg-window-descriptions*))
         (expansion
          `(let* ((io?-output-inhibitedp
                   (member-eq ',token
                              (get-ccg-inhibit-output-lst)))
                  (io?-alist
                   (and (not io?-output-inhibitedp)
                        (list
                         (cons #\w ,(cadr associated-window))
                         (cons #\c ,(if clear-argp
                                        clear
                                      (caddr associated-window)))
                         (cons #\t ,(if cursor-at-top-argp
                                        cursor-at-top
                                      (cadddr associated-window)))
                         (cons #\p ,(if pop-up-argp
                                        pop-up
                                      (car (cddddr associated-window))))

; Peter Dillinger requested the following binding, so that he could specify a
; window prelude string that distinguishes between, for example, "prove",
; "event", and "summary" output, which with the default string would all just
; show up as window 4.

                         (cons #\k ,(symbol-name token))))))
             (pprogn
              (if (or io?-output-inhibitedp
                      (null (f-get-global 'window-interfacep state)))
                  state
                (mv-let (io?-col state)
                        (fmt1! (f-get-global 'window-interface-prelude state)
                               io?-alist 0 *standard-co* state nil)
                        (declare (ignore io?-col))
                        state))
              ,(let ((body
                      `(check-vars-not-free
                        (io?-output-inhibitedp io?-alist)
                        (check-exact-free-vars io? (state ,@vars) ,body)))
                     (nil-output (if (eq shape 'state)
                                     'state
                                   (cons 'mv (io?-nil-output (cdr shape)
                                                             default-bindings))))
                     (postlude
                      `(mv-let
                        (io?-col state)
                        (if (or io?-output-inhibitedp
                                (null (f-get-global 'window-interfacep state)))
                            (mv 0 state)
                          (fmt1! (f-get-global 'window-interface-postlude state)
                                 io?-alist 0 *standard-co* state nil))
                        (declare (ignore io?-col))
                        (check-vars-not-free
                         (io?-output-inhibitedp io?-alist io?-col)
                         ,shape))))
                 (let ((body (if commentp
                                 `(let ,(io?-wormhole-bindings 0 vars)
                                    ,body)
                               body)))
                   (cond
                    ((eq shape 'state)
                     `(pprogn
                       (if io?-output-inhibitedp state ,body)
                       ,postlude))
                    (t `(mv-let ,(cdr shape)
                                (if io?-output-inhibitedp
                                    ,nil-output
                                  ,body)
                                ,postlude)))))))))
    (cond
     (commentp
      (let ((form
             (cond
              ((eq shape 'state)
               `(pprogn ,expansion (value :q)))
              (t
               `(mv-let ,(cdr shape)
                        ,expansion
                        (declare
                         (ignore ,@(remove1-eq 'state (cdr shape))))
                        (value :q))))))
        `(prog2$
          ,(if chk-translatable
               `(chk-translatable ,body ,shape)
             nil)
          (wormhole 'comment-window-io
                    '(lambda (whs)
                       (set-wormhole-entry-code whs :ENTER))
                    (list ,@vars)
                    ',form
                    :ld-error-action :return!
                    :ld-verbose nil
                    :ld-pre-eval-print nil
                    :ld-prompt nil))))
     (t `(pprogn
          (cond ((saved-output-token-p ',token state)
                 (push-io-record nil ; io-marker
                                 (list 'let
                                       (list ,@(formal-bindings vars))
                                       ',expansion)
                                 state))
                (t state))
          ,expansion)))))


; END public configuration interface

; BEGIN mostly raw definitions for the CCG analysis

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; STRUCT DEFINITIONS                                            ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct-raw funct

  ;; The funct defstruct represents the relevant information about the function
  ;; definitions provided by the user.
  ;;
  ;;  * fn: the function name

  (fn nil :type symbol)

  ;;  * formals: the formals of the function

  (formals nil :type list)

  ;;  * ccms: the ccms associated with the function. This will be a vector of
  ;;    terms, whose value will always be natural numbers.

  (ccms nil :type sequence))

(defstruct-raw context

;; The context defstruct is used to represent a calling context. The
;; individual fields are as follows:
;;
;; * ruler: the ruler of the context.

  (ruler nil)

;; * call: the actual recursive call of the context.

  (call nil)

;; * parent-funct: the funct representing the function containing the context.

  (parent-funct (make-funct) :type funct)

;; * call-funct: the funct representing the function called by the call of the
;;   context.

  (call-funct (make-funct) :type funct)

;; * num: a unique ID number assigned to each context. Also indicates
;;   its index in the context-array.

  num)

;; The following macros make it easy to get and set the fields of the functs of
;; a given context.

(defmacro-raw context-fn (c)
  `(funct-fn (context-parent-funct ,c)))

(defmacro-raw context-formals (c)
  `(funct-formals (context-parent-funct ,c)))

(defmacro-raw context-callfn (c)
  `(funct-fn (context-call-funct ,c)))

(defmacro-raw context-callformals (c)
  `(funct-formals (context-call-funct ,c)))

(defmacro-raw context-ccms (c)
  `(funct-ccms (context-parent-funct ,c)))

(defstruct-raw ccmf-node

  ;; The ccmf-node struct represents nodes in the graph representation
  ;; of a CCMF (see the comments for the struct ccmf). It contains two
  ;; lists of edges: >-edges is a list of the indices of the CCMs that
  ;; are always < the current one, and likewise >=-edges is a list of
  ;; the indeces of the CCMs that are always <= the current one.

  (>-edges nil :type list)
  (>=-edges nil :type list))

(defstruct-raw ccmf

  ;; The ccmf struct represents CCMFs as a graph with edges labeled by
  ;; > or >=. The fields are as follows:
  ;;
  ;; * firstsite: the index of the "tail" context of the CCMF.

  (firstsite 0 :type fixnum)

  ;; * lastsite: the index of the "head" context of the CCMF.

  (lastsite 0 :type fixnum)

  ;; * fc-num: the original index of the "tail" context. This is needed
  ;;   because CCGs get separated into SCCs, so the index of the head
  ;;   and tail contexts in the current SCC (firstsite and lastsite)
  ;;   and the context in the original context array may be
  ;;   different. Also, this item is actually a list of indices because
  ;;   of the possibility of context merging. The list keeps track of
  ;;   the original indices of all the contexts that were merged to
  ;;   make the current head or tail context. Currently, absorption and
  ;;   merging are not used, so we tend to just refer to the first item
  ;;   in the list.

  (fc-num (list 0) :type (cons fixnum list))

  ;; * lc-num: the original index of the "head" context (see note for
  ;;   fc-num).

  (lc-num (list 0) :type (cons fixnum list))

  ;; * graph: the graph representing the CCMF. This is an array of
  ;;   ccmf-nodes.

  (graph nil :type (array ccmf-node))

  ;; * in-sizes: the number of CCMFs for the "tail" context.

  (in-sizes 0 :type fixnum)

  ;; * out-sizes: the number of CCMFs for the "head" context.

  (out-sizes 0 :type fixnum)

  ;; * steps: the number of steps in the CCG represented by the
  ;;   CCMF. This is used in the sct algorithm.

  (steps 1 :type fixnum))


(defstruct-raw accg-edge
  ;; The accg-edge struct represents edges in the annotated CCG (ACCG).

  ;; * tail: the index of the tail ACCG node of the edge.

  (tail -1 :type fixnum)

  ;; * head: the index of the head ACCG node of the edge.

  (head -1 :type fixnum)

  ;; * ccmf: the CCMF associated with the edge in the ACCG.

  (ccmf nil :type (or null ccmf)))


(defstruct-raw accg-node
;; The accg-node struct represents nodes in the ACCG. An ACCG is an
;; array of these.

  ;; * context: the context associated with the node.

  (context (make-context) :type context)

  ;; * fwd-edges: edges for which the current node is the tail.

  (fwd-edges nil :type list)

  ;; * bwd-edges: edges for which the current node is the head.

  (bwd-edges nil :type list)

  ;; * num: the index of the node in the array of nodes of the ACCG.

  (num 0 :type fixnum))


;; The following macros are self-explanitory. They allow us to refer
;; to fields of a substruct of a given struct as if it were a field in
;; the struct.

(defmacro-raw accg-node-ruler (accg)
  `(context-ruler (accg-node-context ,accg)))

(defmacro-raw accg-node-call (accg)
  `(context-call (accg-node-context ,accg)))

(defmacro-raw accg-node-parent-funct (accg)
  `(context-parent-funct (accg-node-context ,accg)))

(defmacro-raw accg-node-call-funct (accg)
  `(context-call-funct (accg-node-context ,accg)))

(defmacro-raw accg-node-fn (accg)
  `(context-fn (accg-node-context ,accg)))

(defmacro-raw accg-node-formals (accg)
  `(context-formals (accg-node-context ,accg)))

(defmacro-raw accg-node-callformals (accg)
  `(context-callformals (accg-node-context ,accg)))

(defmacro-raw accg-node-callfn (accg)
  `(context-callfn (accg-node-context ,accg)))

(defmacro-raw accg-node-context-num (accg)
  `(context-num (accg-node-context ,accg)))

(defmacro-raw accg-node-ccms (accg)
  `(context-ccms (accg-node-context ,accg)))

;;; The following two structs are used to represent an SRG. See the
;;; paper on the polynomial approximation of SCT (a.k.a. SCP) for a
;;; full explanation. Briefly: an SRG has CCMs for nodes and edges
;;; labeled with > or >= between them as the corresponding CCMF
;;; dictates. In other words, the graph connects all the CCMF graphs
;;; into one graph.

(defstruct-raw srg-edge
  ;; The srg-edge represents an edge in an SRG.

  ;; * tail: the tail CCM of the edge.

  (tail  0 :type fixnum)

  ;; * head: the head CCM of the edge.

  (head  0 :type fixnum)

  ;; * ccmf: the CCMF from which this edge was derived.

  (ccmf (make-ccmf) :type ccmf)

;; * label: generally > or >=, indicating the label of the CCMF edge
;;   from which this edge is derived.

  (label 'none :type symbol))

(defstruct-raw srg-node
  ;; The srg-node struct represents a node of the SRG

  ;; * node: the index of the ACCG node associated with this SRG node.

  (node 0 :type fixnum)

  ;; * ccm: the index of the CCM in the array of CCMs assigned to the
  ;;   corresponding ACCG node.

  (ccm 0 :type fixnum)

  ;; * fwd-edges: the list of srg-edges of which this srg-node is the
  ;;   tail.

  (fwd-edges nil :type list)

  ;; * bwd-edges: the list of srg-edges of which this srg-node is the
  ;;   head.

  (bwd-edges nil :type list))

;;; the memoization struct contains the information that we use for
;;; memoization. The fields are as follows:
;;;
;;; * proved: the list of proved conjectures.
;;; * unproved0: the list of conjectures that we could not prove with 0 inductions.
;;; * unproved1: the list of conjectures that we could not prove with 1 induction.

(defstruct-raw memoization
  (proved nil :type list)
  (unproved (make-array 0 :initial-element nil :element-type 'list)
            :type (vector list)))

(defun-raw create-memoization (max-ind)
  (make-memoization :unproved (make-array (1+ max-ind)
                                          :initial-element nil
                                          :element-type 'list)))

;;; ccg-simplify-hyps-no-split takes a list of expressions, hyps,
;;; representing a conjunction of predicates and quickly simplifies
;;; them in such a way that does not cause a case split. It returns
;;; the list of simplified expressions.
(defun-raw ccg-simplify-hyps-no-split (hyps ctx ens wrld state)
  (declare (ignore ctx))
  (mv-let (nhyps ttree)
          (normalize-lst hyps t nil ens wrld nil
                         (backchain-limit wrld :ts))
          (er-progn
           (accumulate-ttree-and-step-limit-into-state ttree :skip state)
           (value (flatten-ands-in-lit-lst nhyps)))))

(defrec query-spec-var
  ((wrld . ens)
   (ctx . otf-flg)
   (stop-time . mem))
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Printing Functions                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw print-funct-ccms (functs wrld state)
  (if (endp functs)
      state
    (pprogn
     (fms "The CCM~#1~[~/s~] for ~x0 ~#1~[is~/are~] ~&1.~|"
          `((#\0 . ,(funct-fn (car functs)))
            (#\1 . ,(untranslate-lst
                     (mapcar #'de-propagate
                             (coerce (funct-ccms (car functs))
                                     'list))
                     nil
                     wrld)))
          *standard-co*
          state
          nil)
     (print-funct-ccms (cdr functs) wrld state))))

;; The following definitions culminate in print-counter-example.

(defun-raw prettify-ccms (ccm-array vars vals wrld)
  (let ((fn (if vars
                #'(lambda (x)
                    (untranslate (subcor-var vars vals
                                             (de-propagate x))
                                 nil wrld))
              #'(lambda (x)
                  (untranslate (de-propagate x)
                               nil wrld)))))
    (map 'vector fn ccm-array)))

(defmacro-raw ce-defun-fn (defun)
  `(cadr ,defun))

(defmacro-raw ce-defun-formals (defun)
  `(caddr ,defun))

(defmacro-raw ce-defun-body (defun)
  `(cadddr ,defun))

(defmacro-raw ce-defun-test (defun)
  `(let ((body (ce-defun-body ,defun)))
     (if (eq (fn-symb body) 'if)
         (cadr body)
       T)))

(defmacro-raw ce-defun-call (defun)
  `(let ((body (ce-defun-body ,defun)))
     (if (eq (fn-symb body) 'if)
         (caddr body)
       body)))

(defun-raw ccmf-graph-no-edges? (ccmf-graph)
  (loop for node across ccmf-graph
        when (or (consp (ccmf-node->-edges node))
                 (consp (ccmf-node->=-edges node)))
          return nil
        finally (return t)))

(defun-raw ccmf-graph-term (i graph ccms0 ccms1 acc)
  (if (< i 0)
      (cond ((endp acc) acc)
            ((endp (cdr acc)) (car acc))
            (t (cons 'and acc)))
    (let* ((node (aref graph i))
           (>=-edges (ccmf-node->=-edges node))
           (>-edges  (ccmf-node->-edges node))
           (ccm (de-propagate (aref ccms0 i))))
      (ccmf-graph-term (1- i)
                       graph
                       ccms0
                       ccms1
                       (append (mapcar #'(lambda (x)
                                           `(> ,ccm
                                               ,(de-propagate
                                                 (aref ccms1 x))))
                                       >-edges)
                               (mapcar #'(lambda (x)
                                           `(>= ,ccm
                                                ,(de-propagate
                                                  (aref ccms1 x))))
                                       >=-edges)
                               acc)))))

(defun-raw print-ccmfs1 (defuns defun0 defun1 ccmfs flst funct0 col wrld state)
  (if (endp defuns)
      state
    (let* ((graph (ccmf-graph (car ccmfs)))
           (ne? (ccmf-graph-no-edges? graph))
           (f0 (car defuns))
           (f1 (if (consp (cdr defuns))
                   (cadr defuns)
                 defun0))
           (f2 (cond ((endp (cdr defuns))
                      defun1)
                     ((endp (cddr defuns))
                      defun0)
                     (t (caddr defuns))))
           (fn0 (ce-defun-fn f0))
           (fn1 (ce-defun-fn f1))
           (fn2 (ce-defun-fn f2))
           (formals (ce-defun-formals f1))
           (actuals (fargs (ce-defun-call f0)))
           (ccms0 (prettify-ccms (funct-ccms (car flst)) nil nil wrld))
           (ccms0-lst (coerce ccms0 'list))
           (ccms1 (prettify-ccms (funct-ccms (if (endp (cdr flst))
                                                 funct0
                                               (cadr flst)))
                                 formals actuals wrld))
           (ccms1-lst (coerce ccms1 'list)))
      (pprogn
       (fms "When execution moves from the recursive call in ~x0 of ~x1 to ~
             ~#2~[itself~/the recursive call in ~x1 of ~x3~], we need to know ~
             how the measures of ~x0 compare with the result of substituting ~
             the formals of ~x1 with the actuals of the call to ~x1 in the ~
             measures of ~x1. The measure~#4~[~/s~] for ~x0 ~
             ~#4~[is~/are~]:~|~%~*6~%The result~#5~[~/s~] of applying the ~
             substitution to the measures of ~x1 ~#5~[is~/are~]:~|~%~*7~%We ~
             know ~#8~[nothing about how the values of these CCMs ~
             relate.~/the following about these CCMs:~%~%~Y9A~]~|~%If you can ~
             show that any of the terms in the first list is always either ~
             strictly greater than, or greater than or equal to some term in ~
             the second list, this could be helpful for proving termination.~|"
            (list (cons #\0 fn0)
                  (cons #\1 fn1)
                  (cons #\2 (if (eq fn0 fn1) 0 1))
                  (cons #\3 fn2)
                  (cons #\4 ccms0-lst)
                  (cons #\5 ccms1-lst)
                  (cons #\6 `("" "~x*.~|" "~x*~|" "~x*~|"
                              ,ccms0-lst))
                  (cons #\7 `("" "~x*.~|" "~x*~|" "~x*~|"
                              ,ccms1-lst))
                  (cons #\8 (if ne? 0 1))
                  (cons #\9 (ccmf-graph-term
                              (1- (array-dimension graph 0))
                              graph
                              ccms0
                              ccms1
                              nil))
                  (cons #\A (term-evisc-tuple nil state)))
            *standard-co* state nil)
       (print-ccmfs1 (cdr defuns)
                     defun0
                     defun1
                     (cdr ccmfs)
                     (cdr flst)
                     funct0
                     col wrld state)))))

(defun-raw print-ccmfs (defuns ccmfs flst col wrld state)
  (if (endp defuns)
      state
    (print-ccmfs1 defuns
                   (car defuns)
                   (if (endp (cdr defuns))
                       (car defuns)
                     (cadr defuns))
                   ccmfs
                   flst
                   (car flst)
                   col
                   wrld
                   state)))

(defun-raw print-ccms (defuns functs col wrld state)
  ;; (format t "defuns: ~A functs: ~A col: ~A state: ~A~%" defuns functs col state)
  (if (endp defuns)
      (mv-let (col state)
              (fmt1 "~|" nil col *standard-co* state nil)
              (declare (ignore col))
              state)
    (mv-let
     (col state)
     (fmt1 "The CCM~#1~[~/s~] for ~x0 ~#1~[is~/are~] ~&1. "
           (list (cons #\0 (cadar defuns))
                 (cons #\1 (untranslate-lst
                            (mapcar #'de-propagate
                                    (coerce (funct-ccms (car functs))
                                            'list))
                            nil
                            wrld)))
           col
           *standard-co*
           state nil)
     (print-ccms (cdr defuns) (cdr functs) col wrld state))))

(defun-raw produce-counter-example1 (ccmfs context-array alist wrld)
  (if (endp ccmfs)
      (mv nil nil nil)
    (let* ((context (aref context-array (car (ccmf-fc-num (car ccmfs)))))
           (funct (context-parent-funct context))
           (fn (funct-fn funct)))

      (mv-let
       (name i)
       (ccg-counter-example-fn-name fn (assoc-eq-value fn 0 alist) wrld)
       (mv-let
        (contexts functs names)
        (produce-counter-example1 (cdr ccmfs) context-array
                                  (assoc-set-eq fn (1+ i) alist) wrld)
        (mv (cons context contexts)
            (cons funct functs)
            (cons name names)))))))

(defun-raw produce-counter-example2 (contexts names name0 ctx ens wrld state)
  (if (endp contexts)
      (value nil)
    (let* ((context (car contexts))
           (funct (context-parent-funct context))
           (call (cons (if (endp (cdr names))
                           name0
                         (cadr names))
                       (fargs (context-call context)))))
      (er-let*
       ((ruler (state-global-let*
                ((inhibit-output-lst
                  ;; no output here.
                  *valid-output-names*))
                ;; remove any redundant or subsumed hyps.
                (simp-hyps0 (context-ruler context)
                            ctx ens wrld state nil t nil :term-order)))
        (body (value (if (endp ruler)
                         call
                       `(if ,(if (endp (cdr ruler))
                                 (car ruler)
                               `(and ,@ruler))
                            ,call
                          (list ,@(funct-formals funct))))))
        (rst (produce-counter-example2 (cdr contexts)
                                       (cdr names)
                                       name0
                                       ctx ens wrld state)))
       (value (cons `(defun ,(car names) ,(funct-formals funct) ,body)
                    rst))))))

(defun-raw accg-find-ccmf (accg i j)
  (loop for edge in (accg-node-fwd-edges (aref accg i))
        when (= j (accg-edge-head edge))
          return (accg-edge-ccmf edge)))

(defun-raw produce-counter-example (path accg context-array ctx ens wrld state)
  (let* ((ccmfs (loop for p on path
                      when (and (consp p) (consp (cdr p)))
                        collect (accg-find-ccmf accg (car p) (cadr p)))))
    (pprogn
     (fms "Producing counter-example, including simplifying rulers in order to ~
           maximize the readability of the counter-example."
          nil
          *standard-co*
          state nil)
     (mv-let
      (contexts functs names)
      (produce-counter-example1 ccmfs context-array nil wrld)
      (er-let* ((defuns (produce-counter-example2 contexts names (car names)
                                                  ctx ens wrld state)))
               (value (list* ccmfs functs defuns)))))))

(defun-raw print-counter-example (accg ce contexts ctx ens wrld state)
  (er-let*
   ((triple (produce-counter-example (cdr ce)
                                     accg
                                     contexts
                                     ctx ens wrld state))
    (ccmfs (value (car triple)))
    (functs (value (cadr triple)))
    (defuns (value (cddr triple))))
   (pprogn
    (fms "The following function definitions correspond to an actual loop in ~
          your function definitions for which the CCG analysis was unable to ~
          prove termination in all cases: ~%~%~Y01~%"
         (list (cons #\0 (untranslate (if (endp (cdr defuns))
                                          (car defuns)
                                        (cons 'mutual-recursion defuns))
                                      nil wrld))
               (cons #\1 (term-evisc-tuple nil state)))
         *standard-co*
         state nil)
    ;; (print-ccms defuns functs 0 wrld state)
    (print-ccmfs defuns ccmfs functs 0 wrld state)
    (let* ((loop-graph (car ce))
           (ne? (ccmf-graph-no-edges? loop-graph))
           (ccms (funct-ccms (car functs))))
      (fms "As it stands, we do not have enough information to show that this ~
            loop terminates. ~#0~[When we put it all together, we find that ~
            when we loop from ~x1 to itself, we know ~#2~[nothing about how ~
            the values of the CCMs change. ~/the following about how values ~
            change from one iteration to the loop to the next (measures are ~
            presented without substitution):~%~%~Y34~]~/~]~|~%Note that under ~
            this abstraction, the loop is idempotent (i.e. going through the ~
            loop again will result in the same information about ~
            non-increasing and decreasing values as we have just stated), and ~
            that there is no CCM that decreases to itself across the loop. ~
            There are therefore three possibilities: ~|~%(1) We did not guess ~
            the CCMs needed for proving termination. If this is the case, you ~
            could provide them for us using a :CONSIDER-CCMS or ~
            :CONSIDER-ONLY-CCMS hint (see :DOC CCG-XARGS). If you are truly ~
            desperate, you can resort to proving termination using ACL2's ~
            measure-based termination method (do this globally by using ~
            SET-TERMINATION-METHOD or just once by using the ~
            :TERMINATION-METHOD xarg; see :DOC CCG-XARGS).~|~%(2) We guessed ~
            the proper CCMs, but were unable to prove some necessary ~
            theorem(s) about how these values change from step to step in the ~
            loop. In this case, we suggest that you look at the ~
            counter-example we generated and use it to determine what ~
            additional lemmas are needed for CCG analysis to successfully ~
            prove termination.~|~%(3) The loop really is non-terminating for ~
            some inputs. In this case, you should alter the definition of the ~
            function so that it will terminate on all inputs.~%~%"
           (list (cons #\0 (if (consp (cdr defuns)) 0 1))
                 (cons #\1 (cadar defuns))
                 (cons #\2 (if ne? 0 1))
                 (cons #\3 (untranslate
                            (ccmf-graph-term
                             (1- (array-dimension loop-graph 0))
                             loop-graph
                             ccms
                             ccms
                             nil)
                            nil
                            wrld))
                 (cons #\4 (term-evisc-tuple nil state)))
           *standard-co*
           state nil)))))

(defun-raw print-ccmf-changes (col changes state)
  (if (endp changes)
      state
    (let ((change (car changes)))
      (mv-let
       (col state)
       (fmt1 "When execution moves ~@0, the following ~
             always holds:~|~%~x1.~|~%"
             `((#\0 . ,(if (consp (car change))
                           `("from context ~x0 to context ~x1"
                             (#\0 . ,(caar change))
                             (#\1 . ,(cdar change)))
                         `("across context ~x0"
                           (#\0 . ,(car change)))))
               (#\1 . ,(cdr change)))
             col
             *standard-co*
             state
             nil)
       (print-ccmf-changes col (cdr changes) state)))))

(defun-raw p< (p1 p2)
  (or (< (car p1) (car p2))
      (and (= (car p1) (car p2))
           (< (cdr p1) (cdr p2)))))

(defun-raw construct-accg-changes-printout (changes)
  (if (endp changes)
      nil
    (cons `("the edge from context ~x0 to context ~x1"
            (#\0 . ,(caar changes))
            (#\1 . ,(cdar changes)))
          (construct-accg-changes-printout (cdr changes)))))

(defun-raw print-accg-changes (changes state)
  (if (endp changes)
      (fms "~|" nil *standard-co* state nil)
    (pprogn
     (fms "~x0 -> ~x1"
          `((#\0 . ,(caar changes))
            (#\1 . ,(cdar changes)))
          *standard-co*
          state
          nil)
     (print-accg-changes (cdr changes) state))))

(defun-raw print-changes (col changes state)
  (if (and (endp (car changes))
           (endp (cdr changes)))
      (mv-let
       (col state)
       (fmt1 "We discovered nothing new about the CCG.~|"
             nil
             col
             *standard-co*
             state
             nil)
       (declare (ignore col))
       state)
    (mv-let
     (col state)
     (fmt1 "We discovered the following about the CCG.~|~%"
           nil
           col
           *standard-co*
           state
           nil)
     (mv-let
      (col state)
      (if (endp (car changes))
          (mv col state)
        (mv-let
         (col state)
         (fmt1 "We can safely omit the following edges from the CCG:~|"
               nil
               col
               *standard-co*
               state
               nil)
         (declare (ignore col))
         (mv 0 (print-accg-changes (car changes) state))))
     (print-ccmf-changes col
                         (sort (copy-list (cdr changes))
                               (if (consp (caadr changes))
                                   #'p<
                                 #'<)
                               :key #'car)
                         state)))))


(defun-raw print-context-array1 (i names context-array state)
  (if (>= i (array-dimension context-array 0))
      state
    (pprogn
     (let ((context (aref context-array i)))
       (fms "CALLING CONTEXT ~x0~#1~[~/ in the body of ~x2~]:~|rulers: ~
             ~x3~|call: ~x4~|"
            `((#\0 . ,i)
              (#\1 . ,names)
              (#\2 . ,(context-fn context))
              (#\3 . ,(context-ruler context))
              (#\4 . ,(context-call context)))
            *standard-co*
            state
            nil))
     (print-context-array1 (1+ i) names context-array state))))

(defun-raw print-context-array (names context-array state)
  (pprogn
   (fms "The calling contexts for ~#0~[this definition~/these definitions~] ~
         are:~|"
        `((#\0 . ,names))
        *standard-co*
        state
        nil)
  (print-context-array1 0 names context-array state)))

(defun-raw print-accg-edges3 (edges accg state)
  (if (endp edges)
      state
    (pprogn
     (let ((pair (accg-edge-context-pair (car edges) accg)))
       (fms "~x0 -> ~x1"
            `((#\0 . ,(car pair))
              (#\1 . ,(cdr pair)))
            *standard-co*
            state
            nil))
     (print-accg-edges3 (cdr edges) accg state))))

(defun-raw print-accg-edges2 (i n accg state)
  (if (>= i n)
      state
    (pprogn
     (print-accg-edges3 (accg-node-fwd-edges (aref accg i)) accg state)
     (print-accg-edges2 (1+ i) n accg state))))

(defun-raw print-accg-edges1 (accgs state)
  (if (endp accgs)
      (fms "~|" nil *standard-co* state nil)
    (pprogn
     (print-accg-edges2 0
                        (array-dimension (car accgs) 0)
                        (car accgs)
                        state)
     (print-accg-edges1 (cdr accgs) state))))

(defun-raw print-accg-edges (col accgs state)
  (if (endp accgs)
      state
    (mv-let
     (col state)
     (fmt1 "The Calling Context Graph has the following edges:~|"
          nil col *standard-co* state nil)
     (declare (ignore col))
     (print-accg-edges1 accgs state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the following code is for building a CCG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; limit-induction-hint-fn limits the amount of time spent on a proof
;;; attempt by limiting the amount of induction and subgoals that may
;;; be considered before the prover gives up. This is done with
;;; computed hintus.
(defun limit-induction-hint-fn (i)
  ;; this computed hint has two pieces. the first limits induction,
  ;; the second limits subgoals in order to avoid infinite loops.
  `(or (and (length-exceedsp (car id) ,i) ;;if we are i inductions deep
            (endp (cdadr id))             ;;and we are not in a subgoal of an induction
            (eq (cddr id) 0)              ;;and we haven't done anything with the current subgoal yet,
            '(:computed-hint-replacement t :do-not-induct :otf-flg-override));; do not induct any further.
       (and (> (cddr id) 20) ;; if we have been working on the same subgoal for 20 steps with no induction or case splitting,
            '(:computed-hint-replacement t
                                         :do-not '(eliminate-destructors
                                                   eliminate-irrelevance
                                                   generalize fertilize) ;; turn off all proof methods
                                         ;; Pete: put a quote in front of (eliminate ...) above since that generated an error
                                         :in-theory (theory 'minimal-theory))))) ;; and use minimal theory

(defun translated-limit-induction-hint (i)
  `((eval-and-translate-hint-expression
     "CCG Query" nil
     (cons
      'nil
      (cons
       ((lambda
          (i id)
          (if
              (if
                  (length-exceedsp (car id) i)
                  (if
                      (endp (cdr (car (cdr id))))
                      (if (eq (cdr (cdr id)) '0)
                          '(:computed-hint-replacement t
                                                       :do-not-induct :otf-flg-override)
                        'nil)
                    'nil)
                'nil)
              (if
                  (length-exceedsp (car id) i)
                  (if
                      (endp (cdr (car (cdr id))))
                      (if (eq (cdr (cdr id)) '0)
                          '(:computed-hint-replacement t
                                                       :do-not-induct :otf-flg-override)
                        'nil)
                    'nil)
                'nil)
            (if (< '20 (cdr (cdr id)))
                '(:computed-hint-replacement
                  t
                  :do-not '(eliminate-destructors eliminate-irrelevance
                                                  generalize fertilize)
                  :in-theory (theory 'minimal-theory))
              'nil)))
        ',i
        id)
       (cons state 'nil))))))

;;;ccg-simplify-contexts;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw ccg-negate (exp)
  ;; returns expression corresponding to the negation of expression exp.
  (if (and (consp exp)
           (eq (first exp) 'not))
      (second exp)
    `(not ,exp)))

(defun-raw ccg-addlist (lst)
  ;; creates a macro-expanded expression corresponding to the sum of a
  ;; list of expressions.
  (cond ((endp lst) 0)
        ((endp (cdr lst)) (car lst))
        (t `(binary-+ ,(car lst) ,(ccg-addlist (cdr lst))))))


(defun-raw ccg-count-contexts (tms)
  ;; given a list of lists of items, returns the total number of items.
  (let ((i 0))
    (dolist (tm tms i)
      (setf i (+ i (len tm))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; helper functions                                           ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following code implements memoization. Currently this works as
;;; follows. At the beginning of termination analysis, we create a
;;; memoization struct with the default values for each list. At each
;;; prover query that is not built-in-clauses only, we check the prove
;;; list to see if any previously proved query subsumes our current
;;; goal. If so, we know our goal is true. Otherwise, we check our
;;; current goal against those previously unproven using 1 induction
;;; and, if our current restrictions indicate that we should only use
;;; 0 inductions, those previously unproven using 0 inductions. Here
;;; we check for equality (modulo alpha renaming) rather than
;;; subsumption, due to the fact that ACL2 is not a decision
;;; procedure, but relies on heuristics to guide proofs. Hence, ACL2
;;; might fail to prove a given theorem but succeed in proving a more
;;; general version.  Therefore, unless we find the same query (modulo
;;; alpha renaming) in our unproved lists, we try the proof anyway.
;;;
;;; When a ACL2 is done with a query, we add it to proved, unproved0,
;;; or unproved1 depending on whether the proof attempt was successful
;;; (and if it was not successful, how many inductions were tried).
;;;
;;; Possible improvements:
;;;
;;; * instead of proving queries on the fly, perhaps we could collect
;;;   all the queries and sort them from most to least general. That
;;;   way, if we prove a query, we get for free all the queries that
;;;   it generalizes.
;;;
;;; * can we do some preprocessing on the queries before we compare
;;;   them for subsumption? The current subsumption checks are simple
;;;   syntactic comparisons.
;;;
;;; * we can use random testing to discover queries that are provably
;;;   false. We can then have another list, false-queries that we can
;;;   check against. When doing so, we can safely check subsumption
;;;   rather than equality, making it much more powerful than the
;;;   current unproved checks.

(defun-raw subsumed-by-proved-clause (cl proved)
  (and (consp proved)
       (or (eq t (subsumes *init-subsumes-count* (car proved) cl nil))
           (subsumed-by-proved-clause cl (cdr proved)))))

(defun-raw eliminate-subsumed-tail (cl cl-set acc)
  (if (endp cl-set)
      acc
    (eliminate-subsumed-tail cl (cdr cl-set)
                             (if (subsumes *init-subsumes-count*
                                           cl (car cl-set) nil)
                                 acc
                               (cons (car cl-set) acc)))))

(defun-raw add-proved-clause (cl proved)
  (cons cl (eliminate-subsumed-tail cl proved nil)))

(defun-raw equals-unproved-clause1 (cl unproved)
  ;; note, it is logically sufficient to check that cl subsumes some
  ;; unproved clause to say that if the unproved clause is unproveable
  ;; in the current theory, that cl will also be unproveable. However,
  ;; we are talking about clauses that ACL2 was unable to prove under
  ;; a set of restrictions. Given ACL2's heuristics and proving
  ;; algorithm, it is possible that adding hypotheses might lead ACL2
  ;; astray. Therefore, we want to attempt the proof unless we were
  ;; unsuccessful proving the exact same query.
  (and (consp unproved)
       (or (let ((cl-unproved (car unproved)))
             (and (eq t (subsumes *init-subsumes-count* cl cl-unproved nil))
                  (eq t (subsumes *init-subsumes-count* cl-unproved cl nil))))
           (equals-unproved-clause1 cl (cdr unproved)))))

(defun-raw equals-unproved-clause (cl unproved i)
  ;; checks if we already failed to prove cl using an induction depth of i or
  ;; higher.
  (and (< i (array-dimension unproved 0))
       (or (equals-unproved-clause1 cl (aref unproved i))
           (equals-unproved-clause cl unproved (1+ i)))))

;;; time-limit check
(defmacro-raw time-er (ctx)
  `(er soft ,ctx "CCG analysis has exceeded the specified time ~
        limit. If you did not expect a time-limit, check the global ~
         time-limit setting (see :DOC set-ccg-time-limit and the ~
         discussion of the :time-limit flag in :DOC CCG) to find out ~
         more. At this point you have several options:~|~% ~
         * Set the :don't-guess-ccms flag to t. Sometimes CCG analysis ~
           guesses too many CCMs which leads to excessive prover ~
           queries. This will eliminate *all* CCMs other than the ~
           acl2s-size of each formal.~|~%~
         * Do you see a variable that you don't think is relevant to the ~
           termination proof? In that case, us the :ignore-formals flag ~
           to tell the CCG analysis to throw out CCMs that contain that ~
           formal. This may also cut down on CCMs and therefore prover ~
           queries.~|~%~
         * Finally, if you are willing to wait some more, you ~
           could try increasing the time limit, or eliminating it by ~
           setting it to nil."))


(defun-raw time-left (stop-time ctx state)
  (let ((now (get-internal-run-time)))
    (if (< now stop-time)
        (value (rationalize
                (/ (- stop-time now)
                   (coerce internal-time-units-per-second 'float))))
      (time-er ctx))))

(defun-raw time-check (stop-time ctx state)
  (if (and (posp stop-time)
           (<= stop-time (get-internal-run-time)))
      (time-er ctx)
    (value nil)))

(defmacro-raw maybe-prover-before-stop-time (stop-time ctx state body)
  `(let ((stop-time ,stop-time))
     (if (null stop-time)
         ,body
       (er-let* ((time-limit (time-left stop-time ,ctx ,state)))
                (with-prover-time-limit time-limit
                                        ,body)))))

(defun prove-no-er (term pspv hints ens wrld ctx state)
  ;; calls prover, catching any error that occurred. Returns the error
  ;; triple whose value is the cons of the negation of the error value
  ;; returned by prove (i.e. whether prove successfully proved the
  ;; query or not) and either nil (if unsuccessful) or the resulting
  ;; ttree (if successful).
  (mv-let (er ttree state)
          (prove term pspv hints ens wrld ctx state)
          (if er
              (value (cons nil nil))
            (value (cons t ttree)))))

;; query is the work-horse of our algorithm. It calls the prover
;; with the appropriate restrictions to ensure that it does not
;; attempt to prove termination forever. This function returns an
;; error triple whose value is the ttree generated by the proof. If
;; the proof fails, the triple indicates an error.

(defun-raw query (hyps concl pt qspv state)
  (let* ((stop-time (access query-spec-var qspv :stop-time))
         (mem (access query-spec-var qspv :mem))
         (otf-flg (access query-spec-var qspv :otf-flg))
         (ens (access query-spec-var qspv :ens))
         (ctx (access query-spec-var qspv :ctx))
         (wrld (access query-spec-var qspv :wrld))
         (clause (add-literal concl (dumb-negate-lit-lst hyps) t))
         (bic-onlyp (equal pt :built-in-clauses))
         (ind-limit (if bic-onlyp -1 (cadr pt)))
         (displayed-goal (prettyify-clause-set (list clause)
                                               (let*-abstractionp state)
                                               wrld)))
    (pprogn (ccg-io? query nil state
                     (bic-onlyp ind-limit clause wrld)
                     (fms "We now make the following query, using ~
                           proof-technique ~x0 (see :DOC ~
                           CCG-hierarchy)~#1~[~/ and with the otf-flg set to ~
                           ~x2~]:~|~%GOAL~%~Y34."
                          `((#\0 . ,pt)
                            (#\1 . ,(if bic-onlyp 0 1))
                            (#\2 . ,otf-flg)
                            (#\3 . ,displayed-goal)
                            (#\4 . ,(term-evisc-tuple nil state)))
                          (proofs-co state)
                          state
                          nil))
            (er-let*
             ((pair
               (cond (bic-onlyp
                      ;; if the proof-technique tells us to only use built-in-clauses, we call built-in-clause-p
                      (mv-let (built-in-clausep ttree)
                              (built-in-clausep 'query clause ens (match-free-override wrld) wrld state)
                              (value (if built-in-clausep
                                         (cons t ttree)
                                       (cons nil nil)))))
                     ;; have we already proved a more general query?
                     ((subsumed-by-proved-clause clause (memoization-proved mem))
                      (pprogn
                       (ccg-io? query nil state
                                ()
                                (fms "But we see that this query is already ~
                                      subsumed by another query that was ~
                                      previously proven.~%~%"
                                     nil
                                     (proofs-co state)
                                     state
                                     nil))
                       (value (cons t nil))))
                     ;; have we already failed to prove this query using the same proof techniques?
                     ((equals-unproved-clause clause
                                              (memoization-unproved mem)
                                              ind-limit)
                      (pprogn
                       (ccg-io? query nil state
                                ()
                                (fms "But we see that we already tried and ~
                                      failed to prove an equivalent query ~
                                      using the same restrictions on the ~
                                      theorem prover.~%~%"
                                     nil
                                     (proofs-co state)
                                     state
                                     nil))
                       (value (cons nil nil))))
                     (t
                      ;; otherwise, we we need to call prove.
                      (er-let*
                       ((pair
                         (let ((hints (translated-limit-induction-hint ind-limit)))
                           (maybe-prover-before-stop-time
                            stop-time ctx state
                            (prove-no-er (termify-clause-set (list clause))
                                         (make-pspv ens wrld state
                                                    :displayed-goal displayed-goal
                                                    :otf-flg otf-flg)
                                         hints ens wrld ctx state)))))
                       (progn
                         ;; update the memoization
                         (if (car pair)
                             (setf (memoization-proved mem)
                                   (add-proved-clause clause
                                                      (memoization-proved mem)))
                           (setf (aref (memoization-unproved mem)
                                       ind-limit)
                                 (cons clause
                                       (aref (memoization-unproved mem)
                                             ind-limit))))
                         (value pair)))))))
             (pprogn
              (ccg-io? query nil state
                       ()
                       (fms "ACL2 has ~#0~[SUCCEEDED in proving this ~
                             query~/FAILED to prove this query~].~|"
                            (list (cons #\0 (if (car pair) 0 1)))
                            (proofs-co state)
                            state
                            nil))
              (er-progn
               (time-check stop-time ctx state)
               (if (car pair)
                   (accumulate-ttree-and-step-limit-into-state
                    (cdr pair)
                    :skip;(initial-step-limit wrld state)
                    state)
                 (pprogn
                  (erase-gag-state state)
                  (value nil)))
               (value (car pair))))))))

;; the following two functions, ccg-generic-dfs-visit and
;; ccg-generic-dfs perform a depth-first search of a "generic"
;; directed graph. That is, a graph that is represented as an array of
;; nodes with some way to get a list of adjacent nodes
;; (node-fwd-edges) and some way, given an edge to get the index of
;; the node that it points to (edge-head). The algorithm itself is
;; taken directly out of the CLRS algorithms book.

(defun-raw ccg-generic-dfs-visit (u graph f color time node-fwd-edges edge-head)
  (setf (aref color u) 'grey)
  (dolist (vn (funcall node-fwd-edges (aref graph u)))
    (let ((v (funcall edge-head vn)))
      (when (eq (aref color v) 'white)
        (setf time (ccg-generic-dfs-visit v graph f color time node-fwd-edges edge-head)))))
  (setf (aref color u) 'black)
  (setf (aref f time) u)
  (incf time))

(defun-raw ccg-generic-dfs (graph node-fwd-edges edge-head)
  ;; this is the main generic DFS function. See the comment before the
  ;; previous function for a description of the arguments. This
  ;; function returns an array of indices indicating the order that
  ;; the nodes of the graph were visited. That is, the ith element of
  ;; the return value is the index of the ith node visited.
  (let* ((size (array-total-size graph))
         (f (make-array size :element-type 'fixnum))
         (time 0)
         (color (make-array size
                            :element-type '(member white grey black)
                            :initial-element 'white)))
    (dotimes (i size f)
      (when (eq (aref color i) 'white)
        (setf time (ccg-generic-dfs-visit i graph f color time node-fwd-edges edge-head))))))

;;; The next two functions, like the previous two, operate on a
;;; "generic" graph that is represented as an array of
;;; nodes. Together, they implement an SCC analysis. The algorithm
;;; used here is straight from the CLRS algorithm book.

(defun-raw ccg-generic-scc-aux (u graph scc scc-array scc-num color node-bwd-edges edge-tail)
  ;; this is the helper function for ccg-generic-scc. u is the index
  ;; of the current node. graph is the array of nodes in the
  ;; graph. scc is the list of nodes in the scc that we are building.
  (let ((scc scc))
    (setf (aref color u) 'grey)
    (dolist (vn (funcall node-bwd-edges (aref graph u)))
      (let ((v (funcall edge-tail vn)))
        (when (eq (aref color v) 'white)
          (setf scc
                (ccg-generic-scc-aux v graph scc scc-array scc-num color
                                     node-bwd-edges edge-tail)))))
    (setf (aref color u) 'black)
    (setf (aref scc-array u) scc-num)
    (cons u scc)))

(defun-raw ccg-generic-scc (graph node-fwd-edges node-bwd-edges edge-tail edge-head)
  ;; this is the main scc algorithm. graph is the array of nodes
  ;; representing the graph to be analyzed. node-fwd-edges is a
  ;; function that takes a node from the graph and returns the list of
  ;; the edges for which the given node is the tail. node-bwd-edges
  ;; takes a node from the graph and returns the list of edges for
  ;; which the given node is the head. edge-tail takes an edge and
  ;; returns the index in graph that corresponds to the tail of the
  ;; edge. edge-head takes an edge nad returns the index in graph that
  ;; corresponds to the head of the edge. the function returns a list
  ;; of lists of the nodes such that each list lists all the nodes in
  ;; one scc, as well as an array indicating which scc each node
  ;; belongs to.
  (let ((scc-num -1))
    (loop
     with f = (ccg-generic-dfs graph node-fwd-edges edge-head)
     with size = (array-dimension graph 0)
     with color = (make-array size
                              :element-type '(member black grey white)
                              :initial-element 'white)
     with scc-array = (make-array size
                                  :element-type 'fixnum
                                  :initial-element 0)
     for i from (1- size) downto 0
     for u = (aref f i)
     when (eq (aref color u) 'white)
     collect (ccg-generic-scc-aux u graph nil scc-array (incf scc-num) color
                                  node-bwd-edges edge-tail)
     into sccs
     finally (return (values sccs scc-array)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; building an accg          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw accg-can-omit-edge? (node1 node2 hlevel qspv state)
  ;; given two ACCG nodes, node1 and node2, such that the function called by
  ;; the call of node1 is equal to the fn of node2, as well as a
  ;; ccg-restrict struct, and proof-related stuff (ens, wrld, ctx,
  ;; state), this function attempts to prove that it is impossible to
  ;; end up at node2 directly after visiting node1. We do this by
  ;; attempting to prove that the ruler of node1 implies the negation of
  ;; the ruler of node2 after the formals of the fn of node2 have been
  ;; replaced by the actuals of the call of node1. if this can be
  ;; proven, we return nil, otherwise, we return t.
  (if (hlevel-ccmfs-per-nodep hlevel)
      (value nil)
    (query (append (accg-node-ruler node1)
                   (subcor-var-lst (accg-node-formals node2)
                                   (fargs (accg-node-call node1))
                                   (accg-node-ruler node2)))
           nil
           (hlevel-proof-technique hlevel) qspv state)))

(defun-raw accg-fill-in-edges (accg name-node-alist)
  (loop for i from 0 below (array-dimension accg 0)
        for node1 = (aref accg i)
        for successors = (cdr (assoc (accg-node-callfn node1)
                                     name-node-alist))
        do (setf (accg-node-fwd-edges node1)
                 (loop for node2 in successors
                       for j = (accg-node-num node2)
                       for edge = (make-accg-edge :tail i :head j)
                       do (setf (accg-node-bwd-edges node2)
                                (cons edge (accg-node-bwd-edges node2)))
                       collect edge))))

(defun-raw context-to-accg-node-lst (contexts total)
  (if (endp contexts)
      (mv nil total)
    (mv-let
     (nodes ntotal)
     (context-to-accg-node-lst (cdr contexts) total)
     (let ((node (make-accg-node :context (car contexts))))
       (mv (cons node nodes) (cons node ntotal))))))

(defun-raw ccg-build-accg0 (names contexts)
  (if (endp names)
      (mv nil nil)
    (let ((name (car names))
          (context-list (car contexts)))
      (mv-let
       (alist total)
       (ccg-build-accg0 (cdr names) (cdr contexts))
       (mv-let
        (nodes ntotal)
        (context-to-accg-node-lst context-list total)
        (mv (acons name nodes alist)
            ntotal))))))

(defun-raw ccg-build-accg (names contexts)
  ;; given the names of the functions being analyzed, the contexts
  ;; organized as a list of lists of contexts such that the ith list
  ;; in contexts corresponds to the list of contexts in the ith
  ;; function in names, the ccg-restrict struct restrict, and the
  ;; other proof-related stuff, we build an ACCG.
  (mv-let
   (name-node-alist accg-node-lst)
   (ccg-build-accg0 names contexts)
   (let ((accg (coerce accg-node-lst 'vector)))
     (progn
       (loop for i from 0 below (array-dimension accg 0)
           do (setf (accg-node-num (aref accg i)) i))
       (accg-fill-in-edges accg name-node-alist)
       accg))))

(defun-raw simplify-contexts1 (context-lst ens wrld ctx state)
  (if (endp context-lst)
      state
    (mv-let
     (erp value state)
     (ccg-simplify-hyps-no-split (context-ruler (car context-lst))
                                 ctx ens wrld state)
     (progn
       (unless erp (setf (context-ruler (car context-lst)) value))
       (simplify-contexts1 (cdr context-lst) ens wrld ctx state)))))

(defun-raw simplify-contexts (contexts ens wrld ctx state)
  (if (endp contexts)
      state
    (pprogn
     (simplify-contexts1 (car contexts) ens wrld ctx state)
     (simplify-contexts (cdr contexts) ens wrld ctx state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; annotating accgs (ccmfs)                                   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; choosing ccms (see CAV paper)        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun de-propagate (term)
  (if (eq (fn-symb term) 'ccg-propagate)
      (fargn term 2)
    term))

(defun-raw ccg-formal-sizes (formals)
  ;; given a list of formals, this function returns a list of
  ;; expressions to calculate the acl2s-size of each formal.
  (loop for x in formals
        collect `(acl2s-size ,x)))

(defun-raw ccg-add-zp-ccm (r formals ccms)
  ;; if an expression, r -- which will generally correspond to one of
  ;; the expressions in a ruler -- is (not (zp e)) for some expression
  ;; e that is not in the list of formals, then we add e to our list
  ;; of ccms.
  (cond ((atom r) ccms)
        ((and (eq (ffn-symb r) 'not)
              (consp (fargn r 1))
              (eq (ffn-symb (fargn r 1)) 'zp)
              ;; NOTE: We could remove th
              (not (member-eq (fargn (fargn r 1) 1) formals)))
         (cons (fargn (fargn r 1) 1) ccms))
        (t ccms)))



#|
Fri Mar 28 01:31:05 EDT 2014
----------------------------

Pete:: I am puzzled by the code below and I'm making a change
even though I don't have time to really understand it. Here's the
issue. If I define a function like this:

(defun gen-int-range (x y)
  (cond ((and (integerp x) (integerp y))
         (if (<= x y)
           (cons x (gen-int-range (1+ x) y))
           nil))
        (t nil)))

Then the ccg proof goes through and ccg guesses the ccm I expect,
namely y-x+1.

But, if I switch the order of the variables and I define the
function like this:

(defun gen-int-range ( y x)
  (cond ((and (integerp x) (integerp y))
         (if (<= y x)
           (cons y (gen-int-range (1+ y) x))
           nil))
        (t nil)))

Now ccg fails! and it is because it should have guessed the ccm
x-y+1, but instead it guessed y-x+1. Now, looking at the code
below, notice the how p is defined in the let*. That definition
essentially orders the args based on the term order, so we lose
the information about how they were compared. This is not a good
idea. In many cases, it might be fine because acl2s-size is
robust, eg, acl2s-size -10 = 10, but in this case the ccm we
guess does not decrease and cgen finds a counterexample. So, I
don't understand why the term order is used here at all. I
rewrote just this case in my updated version of ccg, below.

Also, the comment doesn't correspond with what the code actually
does. For example, the (< e1 e2) case generates the measure
e2-e1+1.

(defun-raw ccg-add-<-ccm (r formals ccms)
  ;; if an expression, r -- which will generally correspond to one of
  ;; the expressions in a ruler -- is one of the following forms, we
  ;; add the corresponding expression to the ccms:
  ;;
  ;; * (< 0 e2) --> (acl2s-size e2)
  ;; * (< e1 e2) --> (acl2s-size (- e2 e1))
  ;; * (not (< e1 0)) --> (1+ (acl2s-size e1))
  ;; * (not (< e1 e2)) --> (1+ (acl2s-size (- e1 e2)))
  (declare (ignore formals))
  (cond ((atom r) ccms)
        ((or (eq (car r) '<)
             (and (eq (car r) 'not)
                  (consp (second r))
                  (eq (car (second r)) '<)))
         (let* ((r0 (if (eq (car r) '<) r (second r)))
                (p (term-order (second r0) (third r0)))
                (arg1 (if p (second r0) (third r0)))
                (arg2 (if p (third r0) (second r0))))
           (cond ((and (quotep arg1) (quotep arg2))
                  ccms)
                 ((not (or (quotep arg1) (quotep arg2)))
                  (cons `(acl2s-size (binary-+ '1
                                               (binary-+ ,arg2
                                                         (unary-- ,arg1))))
                        ccms))
                 ((and (quotep arg1) (acl2-numberp (unquote arg1)))
                  (if (and (or (eql (unquote arg1) 0)
                               (eql (unquote arg1) 1))
                           (variablep arg2))
                      ccms
                    (cons `(acl2s-size (binary-+ (quote ,(- 1 (unquote arg1))) ,arg2))
                          ccms)))
                 ((and (quotep arg2) (acl2-numberp (unquote arg2)))
                  (if (and (or (eql (unquote arg2) 0)
                               (eql (unquote arg2) 1))
                           (variablep arg1))
                      ccms
                    (cons `(acl2s-size (binary-+ (quote ,(- 1 (unquote arg2))) ,arg1))
                          ccms)))
                 (t
                  ccms))))
        (t ccms)))
|#


(defun-raw ccg-add-<-ccm (r formals ccms)
  ;; if an expression, r -- which will generally correspond to one of
  ;; the expressions in a ruler -- is one of the following forms, we
  ;; add the corresponding expression to the ccms:
  ;;
  ;; * (< 0 e2) --> (acl2s-size e2)
  ;; * (< e1 e2) --> (acl2s-size (- e2 e1))
  ;; * (not (< e1 0)) --> (1+ (acl2s-size e1))
  ;; * (not (< e1 e2)) --> (1+ (acl2s-size (- e1 e2)))
  (declare (ignore formals))
  (cond ((atom r) ccms)
        ((or (eq (car r) '<)
             (and (eq (car r) 'not)
                  (consp (second r))
                  (eq (car (second r)) '<)))
         (let* ((not? (eq (car r) 'not)) ; check if we are in a not
                (r0 (if (eq (car r) '<) r (second r)))
                (rarg1 (second r0)) ; the real arg1
                (rarg2 (third r0)) ; the real arg2
                (p (term-order (second r0) (third r0)))
                (arg1 (if p (second r0) (third r0)))
                (arg2 (if p (third r0) (second r0))))
           (cond ((and (quotep arg1) (quotep arg2))
                  ccms)
                 ((not (or (quotep arg1) (quotep arg2)))
                  (if not?
                      (cons `(acl2s-size (binary-+ '1
                                                   (binary-+ ,rarg1
                                                             (unary-- ,rarg2))))
                            ccms)
                    (cons `(acl2s-size  (binary-+ '1
                                                  (binary-+ ,rarg2
                                                            (unary-- ,rarg1))))
                          ccms)))
                 ((and (quotep arg1) (acl2-numberp (unquote arg1)))
                  (if (and (or (eql (unquote arg1) 0)
                               (eql (unquote arg1) 1))
                           (variablep arg2))
                      ccms
                    (cons `(acl2s-size (binary-+ (quote ,(- 1 (unquote arg1))) ,arg2))
                          ccms)))
                 ((and (quotep arg2) (acl2-numberp (unquote arg2)))
                  (if (and (or (eql (unquote arg2) 0)
                               (eql (unquote arg2) 1))
                           (variablep arg1))
                      ccms
                    (cons `(acl2s-size (binary-+ (quote ,(- 1 (unquote arg2))) ,arg1))
                          ccms)))
                 (t
                  ccms))))
        (t ccms)))

(defun-raw ccg-add-dec-ccm (arg ccms)
  ;; a rule for adding a ccm that is not very helpful in general, but
  ;; illustrates how it might be useful, in the future, to allow users
  ;; to define their own rules for adding ccms. given an expression
  ;; that should correspond to an argument of the call of a context,
  ;; adds arg to the list of ccms if it is of the form (dec e).
  (if (and (consp arg)
           (eq (car arg) 'dec))
      (cons arg ccms)
    ccms))

(defun-raw accg-guess-ccms-for-node (node)
  ;; given a node, guesses ccms beyond the basic acl2s-size of the
  ;; formals.
  (let ((ccms nil)
        (rulers (accg-node-ruler node))
        (formals (accg-node-formals node)))
    (dolist (r rulers ccms)
      (setf ccms (ccg-add-<-ccm r formals ccms))
      (setf ccms (ccg-add-zp-ccm r formals ccms)))
;;     (dolist (a (fargs (accg-node-call node)) ccms)
;;       (setf ccms (ccg-add-dec-ccm a ccms)))
    ))

(defun-raw ccg-remove-duplicate-ccms-in-functs (functs)
  ;; a function for removing any duplicate ccms in an array of lists of ccms.
  (dolist (funct functs functs)
    (setf (funct-ccms funct)
          (remove-duplicates (funct-ccms funct)
                             :test #'equal
                             :key #'de-propagate))))

(defun-raw ccg-remove-duplicate-ccms (ccms)
  ;; a function for removing any duplicate ccms in an array of lists of ccms.
  (let ((n (array-dimension ccms 0)))
    (dotimes (i n ccms)
      (setf (aref ccms i) (remove-duplicates (aref ccms i)
                                             :test #'equal
                                             :key #'de-propagate)))))

;; when we guess ccms beyond the basic acl2s-size of the formals of a
;; function, we need to propagate the ccms throughout the accg. for
;; example, suppose we have two functions, f and g, such that f
;; contains the call (g x y) when (not (zp (- y x))) and g always
;; calls (f (1+ x) y). then f will get assigned the ccm (- y x), but g
;; will only have (acl2s-size x) and (acl2s-size y). in this
;; situation, there will be no way to tell that (- y x) decreases each
;; time through the loop. we need some sort of "place-holder" to keep
;; track of the value of (- y x) when we are in the function g. the
;; next few functions do this by walking backwards through the graph,
;; visiting each node just once, and adding the ccm resulting in
;; substituting actuals for formals in the non-trivial ccms from the
;; next node. in our example, g would get the ccm (- y (1+ x)).



(defun-raw accg-propagate-ccm (ccm accg n consider-onlyp)
  ;; propagates a single ccm through the accg. here ccm is the ccm
  ;; expression, accg is the accg, n is the index of the node to which
  ;; the ccm is assigned, and consider-onlyp is an array of booleans
  ;; that tells us whether the user supplied the ccms using a
  ;; :CONSIDER-ONLY-CCMS hint or not for each node. this is done in a
  ;; breadth-first order to ensure the shortest propagation paths and
  ;; therefore simpler ccms in general.
  (let* ((size (array-dimension accg 0))
         ;; queued tells us if node i has been added to the queue for
         ;; each 0 <= i < size.
         (queued (make-array size :element-type 'boolean :initial-element nil))
         ;; successor tells us the index of the successor of node i
         ;; from which we propagate the ccm.
         (successor (make-array size :element-type 'integer :initial-element 0))
         ;; ccms is an array assigning each node index, i, to the ccm
         ;; for that node.
         (ccms (make-array size :initial-element nil))
         ;; queue is the queue into which we put the indices of the
         ;; nodes we are to visit in the order in which we are to
         ;; visit them. the initial element is -1 so we know when we
         ;; reach the end of the queue.
         (queue (make-array size :element-type 'integer :initial-element -1))
         (c (accg-node-context-num (aref accg n)))
         ;; i is the index of the queue where the next enqueue
         ;; operation should put the next node index.
         (i 0)
         ;; queue-preds is a small function that puts all the unqueued
         ;; predecessors of node m into the queue.
         (queue-preds (lambda (m)
                        (loop for edge in (accg-node-bwd-edges (aref accg m))
                              for pred = (accg-edge-tail edge)
                              unless (or (aref queued pred)
                                         (aref consider-onlyp pred))
                                do (setf (aref queued pred) t)
                                and do (setf (aref queue (incf i)) pred)
                                and do (setf (aref successor pred) m)))))
    (let ((node (aref accg n)))
      (setf (accg-node-ccms node)
            (cons ccm (accg-node-ccms node)))
      (setf (aref ccms n) ccm))
    (setf (aref queued n) t)
    (funcall queue-preds n)
    (loop for j from 1 below size
          for k = (aref queue j)
          when (= k -1) ;; if we get a -1, we have reached the end of the queue.
            return nil
          do (let* ((succ (aref successor k))
                    (node (aref accg k))
                    ;; we substitute actuals for formals in the ccm of the
                    ;; successor to get the new ccm.
                    (nccm (subcor-var (accg-node-callformals node)
                                      (fargs (accg-node-call node))
                                      (aref ccms succ))))
               (setf (aref ccms k) nccm))
          do (funcall queue-preds k))
    (loop for j from 1 below size
          for k = (aref queue j)
          when (= k -1)
            return nil
          do (let ((node (aref accg k)))
               (setf (accg-node-ccms node)
                     (cons `(ccg-propagate ,c ,(aref ccms k))
                           (accg-node-ccms node)))))))

(defun-raw accg-propagate-ccms (ccms accg consider-onlyp)
  ;; (print ccms) accg-propagate-ccms propagates all the ccms in ccms
  ;; throughout the accg. here, ccms is an array of lists of ccms
  ;; corresponding to the ccms assigned to each node in the
  ;; accg. consider-onlyp is an array of booleans telling us whether
  ;; or not the user supplied the ccms using a :CONSIDER-ONLY-CCMS
  ;; xarg for each node. we return nccms which holds the new list of
  ;; ccms for each node.
  (loop with size = (array-dimension ccms 0)
        for i from 0 below size
        do (loop for ccm in (aref ccms i)
                 do (accg-propagate-ccm ccm accg i consider-onlyp))))

(defun-raw accg-partition-ccms-by-function (ccms nodes)
  ;; in order to compute ccmfs by node instead of by edge, ccms need
  ;; to be assigned by function, not by accg node. this function takes
  ;; the ccms assigned to the nodes of a accg and unions all the ccms
  ;; of the contexts of each function. the result is an alist that
  ;; maps function names to the ccms for that function.
  (loop for i from 0 below (array-dimension ccms 0)
        for funct = (accg-node-parent-funct (aref nodes i))
        do (setf (funct-ccms funct)
                 (append (aref ccms i) (funct-ccms funct)))))

(defun-raw accg-guess-ccms (accg functs ccm-hints-alist)
  ;; accg-guess-ccms puts all the ccm-guessing together. it takes an
  ;; accg and an alist mapping function names to ccms that is
  ;; presumably provided by the user. the ccms are computed and then
  ;; the accg is annotated by setting the accg-node-ccms field of each
  ;; node in the accg to the appropriate list of ccms.
  (let* ((size (array-dimension accg 0))
         (ccms (make-array size :element-type 'list :initial-element nil))
         (consider-onlyp (make-array size :element-type 'boolean :initial-element nil)))
    ;; first we fill in the correct values for consider-onlyp for each
    ;; node depending on whether the user provided ccms using
    ;; :CONSIDER-ONLY-CCMs for the function containing the node. at
    ;; the same time, we set the ccms for any node for which the user
    ;; did supply ccms.
    (loop for i from 0 below size
          for entry = (assoc (accg-node-fn (aref accg i))
                             ccm-hints-alist)
          do (setf (aref consider-onlyp i) (cadr entry))
          unless (eq (cddr entry) *0*) ;; no value supplied is represented as *0*.
            do (setf (aref ccms i) (cddr entry)))
    ;; guess the non-trivial ccms for each node.
    (loop for i from 0 below size
          for node = (aref accg i)
          unless (or (aref consider-onlyp i)
                     ;; don't guess ccms for dead-ends.
                     (endp (accg-node-fwd-edges (aref accg i))))
            do (setf (aref ccms i)
                     (append (accg-guess-ccms-for-node node)
                             (aref ccms i))))
    ;; next, we propagate the ccms and then partition them by
    ;; function. finally, we set the ccm list of each node to be the
    ;; non-trivial ccms for the function plus the acl2s-size of each
    ;; formal of the parent function and the sum of all the formal
    ;; acl2s-sizes (if there is more than one formal).
     (accg-propagate-ccms
      (ccg-remove-duplicate-ccms ccms)
      accg
      consider-onlyp)
    (ccg-remove-duplicate-ccms-in-functs functs)
    (loop for funct in functs
          for fn-sccms in ccm-hints-alist
          for fsizes = (ccg-formal-sizes (funct-formals funct))
;;; I've commented out the next line to avoid a compiler warning.
;         for ccms = (funct-ccms funct)
          unless (cadr fn-sccms)
            do (setf (funct-ccms funct)
                     (append fsizes
                             (if (length-exceedsp fsizes 1)
                                 (cons (ccg-addlist fsizes)
                                       (funct-ccms funct))
                               (funct-ccms funct))))
          finally (ccg-remove-duplicate-ccms-in-functs functs))
    ;; finally, we coerce the ccms for each function from lists into vectors
    (loop for funct in functs
          do (setf (funct-ccms funct)
                   (coerce (funct-ccms funct) 'vector)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; accg annotation (ccmfs)        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw ccmf->-value? (ruler e1 e2 pt qspv state)
  ;; returns true if we can prove that, under the ruler conditions, e2
  ;; will always be o< e1.
  (query ruler `(o< ,(de-propagate e2) ,(de-propagate e1))
         pt qspv state))

(defun-raw ccmf->=-value? (ruler e1 e2 pt qspv state)
  ;; returns true if we can prove that, under the ruler conditions, e1
  ;; will never be o< e2.
  (query ruler `(not (o< ,(de-propagate e1) ,(de-propagate e2)))
         pt qspv state))

(defun-raw ccmf-skip-edge (f1 n1 c1 e1 f2 n2 e2 hlevel)
  ;; returns whether, based on the restrictions indicated by the
  ;; ccg-restrict struct, restrict, we should skip creating a ccmf
  ;; edge for the ccms e1 and e2. this is mostly based on the
  ;; ccg-restrict-measure-vars field.


  ;; (format t "ccmf-skip-edge: ~A ~A~%~%" e1 e2)
  (or (null hlevel)
      (eq (fn-symb e1) 'ccg-propagated)
      (and (eq (fn-symb e2) 'ccg-propagated)
           (not (equal (fargn e2 1) c1)))
      ;; NOTE: we used to think that built-in-clauses are so fast, we don't
      ;; need to skip any. However, we came across some very expensive analyses
      ;; (see one-way-unify1 in the foundations book in the paco directory of
      ;; the regression suite).
      (and ;;(not (ccg-restrict-bic-onlyp restrict))
           (let ((v1 (all-vars e1)) ;; v1 is all the variables in e1
                 (v2 (all-vars e2))) ;; v2 is all the variables in e2
             (and (not (and (eq f1 f2)
                            (= n1 n2)))
                  (case (hlevel-ccm-comparison-scheme hlevel)
                    ;; (:across
                    ;;  (not (and (subsetp v1 v2)
                    ;;            (subsetp v2 v1))))
                    ;; ;; if :equal, we skip if the variable sets are not equal.
                    (:equal
                     (not (and (subsetp v1 v2)
                               (subsetp v2 v1))))
                    ;; if :all, we skip if v1 is not a proper subset of v2.
                    (:all
                     (or (subsetp v2 v1)
                         (not (subsetp v1 v2))))
                    ;; if :some, we skip if v1 a subset of v2 or v1 and v2 do
                    ;; not intersect.
                    (:some
                     (or (subsetp v1 v2)
                         (not (intersectp-eq v1 v2))))
                    ;; if :none, we skip if v1 and v2 intersect.
                    (:none
                     (intersectp-eq v1 v2))))))))

(defun-raw accg-copy-ccmf-graph (graph &key (size nil))
  ;; creates a copy of a ccmf graph
  (let* ((n (array-dimension graph 0))
         (ngraph (make-array (if size (max n size) n)
                             :element-type 'ccmf-node
                             :initial-element (make-ccmf-node))))
    (loop for i from 0 below n
          for node = (aref graph i)
          do (setf (aref ngraph i)
                   (make-ccmf-node :>-edges (copy-list (ccmf-node->-edges node))
                                   :>=-edges (copy-list (ccmf-node->=-edges node)))))
    ngraph))

(defun-raw accg-add-ccmfs (accg)
  (loop for node1 across accg
        for in-sizes = (array-dimension (accg-node-ccms node1) 0)
        do (loop for edge in (accg-node-fwd-edges node1)
                 for head = (accg-edge-head edge)
                 for node2 = (aref accg head)
                 for graph = (make-array in-sizes)
                 do (loop for i from 0 below in-sizes
                          do (setf (aref graph i)
                                   (make-ccmf-node)))
                 do (setf (accg-edge-ccmf edge)
                          (make-ccmf :firstsite (accg-edge-tail edge)
                                     :lastsite  head
                                     :fc-num    (accg-node-context-num node1)
                                     :lc-num    (accg-node-context-num node2)
                                     :in-sizes  in-sizes
                                     :out-sizes (array-dimension (accg-node-ccms
                                                                  node2)
                                                                 0)
                                     :graph graph)))))

;;;;;;;;;;;;;;;;;;;;;;;;
;;; accg sccs        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw accg-scc (graph)
  (ccg-generic-scc graph
                   #'accg-node-fwd-edges #'accg-node-bwd-edges
                   #'accg-edge-tail #'accg-edge-head))

(defun-raw accg-edge-context-pair (edge accg)
  (cons (car
         (accg-node-context-num
          (aref accg
                (accg-edge-tail
                 edge))))
        (car
         (accg-node-context-num
          (aref accg
                (accg-edge-head
                 edge))))))

(defun-raw accg-delete-non-scc-edges1 (edges accg scc scc-array)
  (if (endp edges)
      (mv nil nil)
    (mv-let
     (changes nedges)
     (accg-delete-non-scc-edges1 (cdr edges) accg scc scc-array)
     (if (= scc (aref scc-array (accg-edge-head (car edges))))
         (mv changes (cons (car edges) nedges))
       (mv (cons (accg-edge-context-pair (car edges) accg)
                 changes)
           nedges)))))

(defun-raw accg-delete-non-scc-edges (accg scc-array)
  (loop with changes = nil
        for i from 0 below (array-dimension accg 0)
        for nodei = (aref accg i)
        for scci = (aref scc-array i)
        do (mv-let
            (nchanges nedges)
            (accg-delete-non-scc-edges1 (accg-node-fwd-edges nodei) accg scci scc-array)
            (progn
              (setf (accg-node-fwd-edges nodei) nedges)
              (setf changes (append nchanges changes))))
        do (setf (accg-node-bwd-edges nodei)
                 (delete-if-not #'(lambda (x)
                                    (= scci
                                       (aref scc-array
                                             (accg-edge-tail x))))
                  (accg-node-bwd-edges nodei)))
        finally (return changes)))

(defun-raw accg-separate-sccs0 (accg sccs scc-array &key (ccmfp nil))
  (if (endp (cdr sccs))
      (mv nil (list accg))
    (let* ((m (array-dimension accg 0)) ;; the number of nodes in the current accg
           (n (len sccs))               ;; the number of sccs
           (count (make-array n ;; an array keeping track of the size of each scc.
                              :element-type 'fixnum
                              :initial-element 0))
           (mapping (make-array m ;; a mapping from the old index of each node to its new index.
                                :element-type 'fixnum
                                :initial-element 0))
           (changes nil))
      ;; next, we calculate the values of count and the mapping.
      (loop for i from 0 below m
            for j = (aref scc-array i)
            do (setf (aref mapping i) (aref count j))
            do (incf (aref count j)))
      ;; naccgs is an array of the new accgs.
      (let ((naccgs (make-array n)))
        ;; we set each accg in naccg to be an array of nodes.
        (loop for i from 0 below n
              do (setf (aref naccgs i)
                       (make-array (aref count i))))
        ;; we now populate naccgs with nodes, setting the
        ;; accg-node-num and resetting the accg-node-bwd-edges
        (loop for i from 0 below m
              for sccn = (aref scc-array i)
              for noden = (aref mapping i)
              for node = (aref accg i)
              do (setf (aref (aref naccgs sccn) noden)
                       node)
              do (setf (accg-node-num node) noden)
              do (setf (accg-node-bwd-edges node) nil))
        ;; now we fix the edges
        (loop for i from 0 below n
              for naccg = (aref naccgs i)
              do (loop for j from 0 below (aref count i)
                       for node = (aref naccg j)
                       ;; we recalculate the accg-node-fwd-edges of node as follows
                       do (setf (accg-node-fwd-edges node)
                                (loop for e in (accg-node-fwd-edges node)
                                      for head = (accg-edge-head e)
                                      for nhead = (aref mapping head)
                                      for ccmf = (accg-edge-ccmf e)
                                      ;; if the edge traverses two
                                      ;; edges in the same scc,
                                      if (= (aref scc-array head) i)
                                      ;; set the head and tail of the edge
                                      do (setf (accg-edge-head e) nhead)
                                      and do (setf (accg-edge-tail e) j)
                                      ;; add the edge to the
                                      ;; appropriate bwd-edges list
                                      and do (let ((hnode (aref naccg nhead)))
                                               (setf (accg-node-bwd-edges hnode)
                                                     (cons e
                                                           (accg-node-bwd-edges hnode))))
                                      ;; collect e into our new list of fwd-edges
                                      and collect e
                                      ;; when we need to worry about
                                      ;; ccmfs, fix this edge's
                                      ;; ccmf.
                                      and when ccmfp
                                      do (setf (ccmf-firstsite ccmf) j)
                                      and do (setf (ccmf-lastsite ccmf)
                                                   nhead)
                                      else do (setf changes
                                                    (cons
                                                     (accg-edge-context-pair e accg)
                                                     changes))))))
        ;; finally, we collect all the non-trivial sccs into a list and return it.
        (mv changes
            (loop for i from 0 below n
                  for naccg = (aref naccgs i)
                  unless (and (= (aref count i) 1)
                              (not (accg-node-fwd-edges (aref naccg 0))))
                  collect naccg))))))

(defun-raw accg-separate-sccs (accg &key (ccmfp nil))
  ;; separates an accg into its sccs. ccmfp indicates whether or not
  ;; the accg has already been annotated with ccmfs. this function is
  ;; destructive.

  ;; we start by doing the scc analysis:
  (multiple-value-bind
      (sccs scc-array)
      (accg-scc accg)
     (accg-separate-sccs0 accg sccs scc-array :ccmfp ccmfp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; putting it all together ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw build-and-annotate-accgs (names functs contexts ccm-hints-alist)
  ;; build-and-annotate-accgs does exactly what it says. names is the
  ;; names of the functions, contexts is a list of lists of contexts
  ;; such that the ith list in contexts is the list of contexts in the
  ;; ith function in names. restrict is the current ccg-restrict
  ;; struct, and ccms-alist is the alist mapping function names to the
  ;; ccms provided for the user for that function.
  (let ((accg (ccg-build-accg names contexts)))
    (multiple-value-bind
        (sccs scc-array)
        (accg-scc accg)
      (progn
        (accg-delete-non-scc-edges accg scc-array)
        (accg-guess-ccms accg functs ccm-hints-alist)
        (accg-add-ccmfs accg)
        (mv-let
         (changes0 naccgs)
         (accg-separate-sccs0 accg sccs scc-array :ccmfp t)
         (declare (ignore changes0))
         naccgs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; refining accgs          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun-raw weaker-proof-techniquesp (h1 h2)
  ;; given two levels in the hierarchy, this function tells us whether the
  ;; proof-techniques of the first are weaker than the proof-techniques of the
  ;; second, i.e. that it might be possible to prove something using the proof
  ;; techniques of h2 that would not be proven using the techniques in h1.


  (or ;; h1 is nil in our first round of refinement, when their is no
      ;; previous level to the hierarchy
   (null h1)
   (not (null h2)) ;; this should never happen
   (let ((pt1 (car h1))
         (pt2 (car h2)))
     ;; the proof techniques of h1 are weaker if it limited to built-in-clauses
     ;; while h2 is not:
     (if (equal pt1 :built-in-clauses)
         (not (equal pt2 :built-in-clauses))
       ;; the proof techniques of h1 are weaker if it is of the form
       ;; (:induction-depth n1), h2 is of the form (:induction-depth n2) and
       ;; (< n1 n2).
       (and (consp pt2)
            (< (cadr pt1)
               (cadr pt2)))))))

(defun-raw accg-ccmf-adj-matrix (ccmf)
  ;; given a ccmf, this function builds an adjacency matrix where
  ;; element i,j is >, >=, or nil if there is a >-edge, >=-edge, or no
  ;; edge from ccm i of the first context to ccm j of the second index
  ;; in the ccmf, respectively.
  (loop with n1 = (ccmf-in-sizes ccmf)
        with n2 = (ccmf-out-sizes ccmf)
        with graph = (ccmf-graph ccmf)
        with matrix = (make-array `(,n1 ,n2)
                                  :initial-element nil
                                  :element-type '(member nil '>= '>))
        for i from 0 below n1
        for node = (aref graph i)
        do (loop for j in (ccmf-node->-edges node)
                 do (setf (aref matrix i j) '>))
        do (loop for j in (ccmf-node->=-edges node)
                 do (setf (aref matrix i j) '>=))
        finally (return matrix)))

;; currently destructive

(defun-raw accg-refine-ccmf2 (i j matrix node e1 hyps f1 c1 f2 ccms2 cformals args redop
                                changes old-hlevel hlevel qspv state)
  (let ((wrld (access query-spec-var qspv :wrld)))
    (if (< j 0)
        (value changes)
      (let* ((o2 (aref ccms2 j))
             (e2 (subcor-var cformals args o2))
             (u1 (untranslate e1 nil wrld))
             (u2 (untranslate o2 nil wrld))
             (skipp (or (ccmf-skip-edge f1 i c1 e1 f2 j e2 hlevel)
                        (not (or redop ;; if circumstances tell us to redo the > proof,
                                 (ccmf-skip-edge f1 i c1 e1 f2 j e2 old-hlevel)))))
             (label (aref matrix i j))
             (pt (hlevel-proof-technique hlevel)))
        (er-let*
         ((nlabel
           (cond (skipp (value label))
                 ((eq label '>) (value '>))
                 ((equal (de-propagate e1) (de-propagate e2)) (value '>=))
                 (t
                  (er-let*
                   ((result
                     (pprogn
                      (increment-timer 'other-time state)
                      (ccg-io? build/refine nil state
                               (u1 u2)
                               (fms "We attempt to prove that, under the given ~
                                   conditions, it is the case that the ~
                                   context measure ~x0 is always greater than ~
                                   ~x1.~|"
                                    `((#\0 . ,u1)
                                      (#\1 . ,u2))
                                    *standard-co*
                                    state
                                    nil))
                      (increment-timer 'print-time state)
                      (ccmf->-value? hyps e1 e2 pt qspv state))))
                   (cond (result (value '>))
                         ((eq label '>=) (value '>=))
                         (t
                          (er-let*
                           ((result
                             (pprogn
                              (increment-timer 'other-time state)
                              (ccg-io? build/refine nil state
                                       (u1 u2)
                                       (fms "Since the previous query failed, ~
                                           we attempt to prove that, under ~
                                           the given conditions,  it is the ~
                                           case that the context measure ~x0 ~
                                           is never less than ~x1.~|"
                                            `((#\0 . ,u1)
                                              (#\1 . ,u2))
                                            *standard-co*
                                            state
                                            nil))
                              (increment-timer 'print-time state)
                              (ccmf->=-value? hyps e1 e2 pt qspv state))))
                           (value (if result '>= nil))))))))))
         (progn
           ;;(format t "~&e1: ~A e2: ~A label: ~A~%" e1 e2 nlabel)
           (case nlabel
             (> (setf (ccmf-node->-edges node)
                      (cons j (ccmf-node->-edges node))))
             (>= (setf (ccmf-node->=-edges node)
                       (cons j (ccmf-node->=-edges node)))))
           (accg-refine-ccmf2 i (1- j) matrix node e1
                              hyps f1 c1 f2 ccms2 cformals args redop
                              (if (eq nlabel label)
                                  changes
                                (cons `(,nlabel ,u1 ,u2) changes))
                              old-hlevel hlevel qspv state)))))))

(defun-raw accg-refine-ccmf1 (i matrix ccmf
                               hyps f1 ccms1 c1 f2 ccms2 cformals args redop
                               changes old-hlevel hlevel
                               qspv state)
  ;; this function destructively refines a ccmf. note that its
  ;; signature looks just like that of accg-construct-ccmf-graph,
  ;; except we have the added arguments redop and old-hlevel, which
  ;; help us to know when we need to redo proofs we have already done.

  (if (< i 0)
      (value (cond ((endp changes) changes)
                   ((endp (cdr changes)) (car changes))
                   (t (cons 'and changes))))
    (er-let*
     ((changes0 (accg-refine-ccmf2 i (1- (ccmf-out-sizes ccmf)) matrix (aref (ccmf-graph ccmf) i)
                                   (aref ccms1 i) hyps f1 c1 f2 ccms2 cformals args redop
                                   changes old-hlevel hlevel qspv state)))
     (accg-refine-ccmf1 (1- i) matrix ccmf
                        hyps f1 ccms1 c1 f2 ccms2 cformals args redop
                        changes0 old-hlevel hlevel qspv state))))

(defun-raw accg-refine-ccmf (ccmf hyps f1 ccms1 c1 f2 ccms2 cformals args redop
                               old-hlevel hlevel qspv state)
  (let ((matrix (accg-ccmf-adj-matrix ccmf)))
    (loop for node across (ccmf-graph ccmf)
          do (setf (ccmf-node->-edges node) nil)
          do (setf (ccmf-node->=-edges node) nil))
    (accg-refine-ccmf1 (1- (ccmf-in-sizes ccmf)) matrix
                       ccmf hyps f1 ccms1 c1 f2 ccms2 cformals args redop
                       nil old-hlevel hlevel qspv state)))

(defun-raw accg-node-refine-ccmfs-per-edge
  (edges node1 accg ccms1 c1 ruler1 cformals args
         stronger-proofsp changes old-hlevel hlevel
         qspv state)
  (if (endp edges)
      (value changes)
    (let* ((edge (car edges))
           (node2 (aref accg (accg-edge-head edge)))
           (ccms2 (accg-node-ccms node2))
           (ruler2 (subcor-var-lst cformals args (accg-node-ruler node2)))
           (wrld (access query-spec-var qspv :wrld)))
      (pprogn
       (increment-timer 'other-time state)
       (ccg-io? build/refine nil state
                (node1 ruler1 wrld node2)
                (fms "We use theorem prover queries to discen how the context ~
                      measures change when execution moves from call ~x0 in ~
                      function ~x1 under the ruler ~x2 to call ~x3 in ~
                      function ~x4 under the ruler ~x5.~|"
                     `((#\0 . ,(accg-node-call node1))
                       (#\1 . ,(accg-node-fn node1))
                       (#\2 . ,(untranslate-lst ruler1 nil wrld))
                       (#\3 . ,(accg-node-call node2))
                       (#\4 . ,(accg-node-fn node2))
                       (#\5 . ,(untranslate-lst (accg-node-ruler node2) nil wrld)))
                     *standard-co*
                     state
                     nil))
       (increment-timer 'print-time state)
       (er-let*
        ((nchanges (accg-refine-ccmf (accg-edge-ccmf edge)
                                     (append ruler1 ruler2)
                                     (accg-node-fn node1)
                                     ccms1
                                     c1
                                     (accg-node-fn node2)
                                     ccms2
                                     cformals args
                                     stronger-proofsp
                                     old-hlevel hlevel
                                     qspv state)))
        (accg-node-refine-ccmfs-per-edge
         (cdr edges) node1 accg ccms1 c1 ruler1
         cformals args
         stronger-proofsp
         (if (null nchanges)
             changes
           (acons (cons (car (accg-node-context-num node1))
                        (car (accg-node-context-num node2)))
                  nchanges
                  changes))
         old-hlevel hlevel
         qspv state))))))

(defun-raw accg-refine-ccmfs1 (i accg stronger-proofsp changes
                                 old-hlevel hlevel qspv state)
  ;; refines all the ccmfs in an accg.
  (if (< i 0)
      (value changes)
    (let* ((node1 (aref accg i))
           (ccms1 (accg-node-ccms node1))
           (c1 (accg-node-context-num node1))
           (ruler1 (accg-node-ruler node1))
           (cformals (accg-node-callformals node1))
           (args (fargs (accg-node-call node1)))
           (wrld (access query-spec-var qspv :wrld)))
      (er-let*
       ((changes0
         (if (hlevel-ccmfs-per-nodep hlevel)
             ;; if we are creating/refining ccmfs on a per-node basis
             ;; (rather than per-edge), we refine one ccmf for the node and
             ;; propagate its graph to the ccmf of every edge.
             (pprogn
              (ccg-io? build/refine nil state
                       (c1 ruler1 wrld)
                       (fms "We use theorem prover queries to discern how our ~
                             context mesaures change when execution moves ~
                             across call ~x0 in function ~x1 under the ruler ~
                             ~x2.~|"
                            `((#\0 . ,(accg-node-call node1))
                              (#\1 . ,(accg-node-fn node1))
                              (#\2 . ,(untranslate-lst ruler1 nil wrld)))
                            *standard-co*
                            state
                            nil))
              (er-let*
               ((edge1 (value (car (accg-node-fwd-edges node1))))
                (node2 (value (aref accg (accg-edge-head edge1))))
                (ccmf (value (accg-edge-ccmf (car (accg-node-fwd-edges node1)))))
                (nchanges (accg-refine-ccmf ccmf
                                            ruler1
                                            (accg-node-fn node1)
                                            ccms1
                                            c1
                                            (accg-node-fn node2)
                                            (accg-node-ccms node2)
                                            cformals args
                                            stronger-proofsp
                                            old-hlevel hlevel
                                            qspv state))
                (ngraph (value (ccmf-graph ccmf))))
               (loop for edge in (cdr (accg-node-fwd-edges node1))
                     for occmf = (accg-edge-ccmf edge)
                     do (setf (ccmf-graph occmf)
                              (accg-copy-ccmf-graph ngraph))
                     finally (return (value (if (null nchanges)
                                                changes
                                              (acons (car (accg-node-context-num
                                                           node1))
                                                     nchanges
                                                     changes)))))))
           ;; if we are creating/refining ccmfs on a per-edge basis, we
           ;; refine the ccmf of each edge seperately.
           (accg-node-refine-ccmfs-per-edge (accg-node-fwd-edges node1)
                                            node1 accg ccms1 c1 ruler1 cformals args
                                            stronger-proofsp changes old-hlevel hlevel
                                            qspv state))))
       (accg-refine-ccmfs1 (1- i) accg stronger-proofsp changes0 old-hlevel hlevel
                           qspv state)))))

(defun-raw accg-refine-ccmfs (accg stronger-proofsp old-hlevel hlevel
                                   qspv state)
  (accg-refine-ccmfs1 (1- (array-dimension accg 0)) accg stronger-proofsp nil
                      old-hlevel hlevel
                      qspv state))

(defun-raw accg-refine-ccmfs-lst1 (accgs caccgs uaccgs changes stronger-proofsp
                                         old-hlevel hlevel qspv state)
  (if (endp accgs)
      (value (list* changes caccgs uaccgs))
    (er-let*
     ((accg (value (car accgs)))
      (nchanges (accg-refine-ccmfs accg stronger-proofsp old-hlevel hlevel
                                   qspv state)))
     (accg-refine-ccmfs-lst1 (cdr accgs)
                             (if (consp nchanges)
                                 (cons accg caccgs)
                               caccgs)
                             (if (consp nchanges)
                                 uaccgs
                               (cons accg uaccgs))
                             (append nchanges changes)
                             stronger-proofsp
                             old-hlevel hlevel
                             qspv state))))

(defun-raw accg-refine-ccmfs-lst (accgs stronger-proofsp old-hlevel hlevel
                                        qspv state)
  ;; refines the ccmfs of a list of accgs.
  ;;
  ;;
  ;;
  ;; OUTPUT: an error triple whose value is (list* d c u) where d ... c is the
  ;; list of accgs that were changed during refinement, and u is the list of
  ;; accgs that were unchanged during refinement.

  (accg-refine-ccmfs-lst1 accgs nil nil nil stronger-proofsp old-hlevel hlevel
                          qspv state))

(defun-raw prune-accg-node (node1 edges accg changes hlevel qspv state)
  (if (endp edges)
      (value changes)
    (let* ((edge (car edges))
           (node2 (aref accg (accg-edge-head edge))))
      (er-let*
       ((result
         (pprogn
          (increment-timer 'other-time state)
          (ccg-io? build/refine nil state
                   (node1 node2)
                   (fms "We attempt to prove that it is not possible for ~
                         execution to move from context ~x0 to context ~x1.~|"
                        `((#\0 . ,(car (accg-node-context-num node1)))
                          (#\1 . ,(car (accg-node-context-num node2))))
                        *standard-co*
                        state
                        nil))
          (increment-timer 'print-time state)
          (accg-can-omit-edge? node1 node2 hlevel qspv state))))
       (progn
         (unless result
           (setf (accg-node-fwd-edges node1)
                 (cons edge (accg-node-fwd-edges node1)))
           (setf (accg-node-bwd-edges node2)
                 (cons edge (accg-node-bwd-edges node2))))
         (prune-accg-node node1 (cdr edges) accg
                          (if result
                              (acons (car (accg-node-context-num node1))
                                     (car (accg-node-context-num node2))
                                     changes)
                            changes)
                          hlevel qspv state))))))

(defun-raw prune-accg1 (i accg changes hlevel qspv state)
  (if (< i 0)
      (value changes)
    (let* ((node (aref accg i))
           (edges (accg-node-fwd-edges node)))
      (setf (accg-node-fwd-edges node) nil)
      (er-let* ((nchanges (prune-accg-node node edges accg changes
                                           hlevel qspv state)))
               (prune-accg1 (1- i) accg nchanges hlevel qspv state)))))

(defun-raw prune-accg (accg hlevel qspv state)
  ;; reset all the bwd-edges
  (loop for node across accg
        do (setf (accg-node-bwd-edges node) nil))
  (pprogn
   (ccg-io? build/refine nil state
            ()
            (fms "We attempt to prune the CCG by using theorem prover queries ~
                  to determine if the rulers of adjacent calling contexts are ~
                  incompatible.~|"
                 nil
                 *standard-co*
                 state
                 nil))
   ;; prune!
   (prune-accg1 (1- (array-dimension accg 0)) accg nil hlevel qspv state)))

(defun-raw accg-refine-accg (accg stronger-proofsp old-hlevel hlevel
                                  qspv state)
  ;; this function refines an accg based on whether we have stronger
  ;; proof techniques available (stronger-proofsp), or some other
  ;; weaker set of restrictions (comparing restrict to
  ;; old-restrict). The result is a list of new accgs that have been
  ;; separated into sccs.
  (er-let*
   ((accg-changes0
     (if (and stronger-proofsp
              (not (hlevel-ccmfs-per-nodep hlevel)))
         ;; if we are using stronger proof techniques
         ;; and we are not doing ccmfs on a per-node
         ;; basis (in which case we avoid pruning to
         ;; allow for simpler justifications in the end)
         (prune-accg accg hlevel qspv state)
       (value nil))))
   (if (consp accg-changes0)
       (mv-let
        (accg-changes1 naccgs)
        (accg-separate-sccs accg :ccmfp t)
        (er-let*
         ((triple (accg-refine-ccmfs-lst naccgs stronger-proofsp
                                         old-hlevel hlevel
                                         qspv state)))
         (value (cons (cons (append accg-changes0 accg-changes1)
                            (car triple))
                      naccgs))))
     (er-let*
      ((changes0 (accg-refine-ccmfs accg stronger-proofsp
                                    old-hlevel hlevel
                                    qspv state)))
      (value (cons (cons nil changes0) (list accg)))))))

(defun-raw accg-refine-accgs1 (accgs ces changes caccgs uaccgs uces
                                     stronger-proofsp old-hlevel new-hlevel
                                     qspv state)
  (if (endp accgs)
      (value (list* changes caccgs uaccgs uces))
    (er-let*
     ((pair (accg-refine-accg (car accgs) stronger-proofsp
                              old-hlevel new-hlevel qspv state)))
     (if (or (consp (caar pair)) (consp (cdar pair)))
         (accg-refine-accgs1 (cdr accgs)
                             (cdr ces)
                             (cons (append (caar pair) (car changes))
                                   (append (cdar pair) (cdr changes)))
                             (append (cdr pair) caccgs)
                             uaccgs
                             uces
                             stronger-proofsp old-hlevel new-hlevel
                             qspv state)
       (accg-refine-accgs1 (cdr accgs)
                           (cdr ces)
                           changes
                           caccgs
                           ;; if there are no changes, (cdr pair) is a
                           ;; singleton list.
                           (append (cdr pair) uaccgs)
                           (cons (car ces) uces)
                           stronger-proofsp old-hlevel new-hlevel
                           qspv state)))))

(defun-raw accg-refine-accgs (accgs ces old-hlevel new-hlevel qspv state)
  ;; refines a list of accgs by calling accg-refine-accg repeatedly. Returns an
  ;; error triple whose value is (cons c u) where c is a list of the accgs that were
  ;; changed by refinement, and u is a list of the accgs that were not changed
  ;; by refinement.
  (pprogn
   (ccg-io? basics nil state
            (new-hlevel accgs)
            (fms "We now move to the ~x0 level of the hierarchy ~
                  (see :DOC CCG-hierarchy) in order to refine the remaining ~
                  SCC~#1~[~/s~] of our anotated CCG.~|"
                 `((#\0 . ,new-hlevel)
                   (#\1 . ,accgs))
                 *standard-co*
                 state
                 nil))
   (er-let*
    ((tuple (accg-refine-accgs1 accgs ces nil nil nil nil
                                 (weaker-proof-techniquesp old-hlevel
                                                           new-hlevel)
                                 old-hlevel new-hlevel
                                 qspv state))
     (changes (value (car tuple)))
     (caccgs (value (cadr tuple)))
     (uaccgs (value (caddr tuple)))
     (uces (value (cdddr tuple))))
    (pprogn
     (ccg-io? basics nil state
              (changes state)
              (mv-let
               (col state)
               (fmt "We have completed CCG refinement. "
                    nil
                    *standard-co*
                    state
                    nil)
               (print-changes col changes state)))
     (value (list* caccgs uaccgs uces))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the following code is used to clean up CCGs (see the SCP
;;; paper). the code culminates in the cln function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw srg-scc (graph)
  ;; srg-scc is the instantiation of ccg-generic-scc for srgs.
  (ccg-generic-scc graph
                   #'srg-node-fwd-edges #'srg-node-bwd-edges
                   #'srg-edge-tail #'srg-edge-head))


(defun-raw srg-scc-has->-edgep (scc scc-array srg)
  ;; srg-scc-has->-edgep tells us whether an scc of an srg contains an
  ;; edge labeled with a >. here scc is a list of indices of nodes in
  ;; the same scc, and scc-array maps srg indices to a unique scc
  ;; identifier (as in the second value returned by srg-scc).
  (let ((scc-num (aref scc-array (car scc))))
    (dolist (p scc nil)
      (let ((x (aref srg p)))
        (when (dolist (e (srg-node-fwd-edges x) nil)
                (when (and (eq (srg-edge-label e) '>)
                           (= scc-num (aref scc-array
                                            (srg-edge-head e))))
                  (return t)))
          (return t))))))

(defun-raw ccmf-remove-ccms (ccmf first-del-array last-del-array)
  ;; virtually and destructively removes ccms from a ccmf by removing
  ;; all edges involving those ccms. This is sufficient for our
  ;; purposes and easier than rebuilding the ccmf without the
  ;; ccms. here, ccmf is a ccmf struct, first-del-array and
  ;; last-del-array are arrays of booleans for which a value of t in
  ;; slot i indicates that the ith ccm should be removed from the ith
  ;; source or sink ccm, respectively. returns the ccmf or nil if all
  ;; the edges have been removed from the ccmf, in which case,
  ;; termination cannot be proven.
  (loop with graph = (ccmf-graph ccmf)
        for i from 0 below (ccmf-in-sizes ccmf) ;; we loop through the graph array.
        for node = (aref graph i)
        for f = (lambda (x) (aref last-del-array x))
        if (aref first-del-array i) ;; if we are supposed to delete this source node,
          do (setf (aref graph i) (make-ccmf-node)) ;; we set the node to a blank node
        else ;; otherwise, we remove all the > and >= edges that lead
             ;; to a deleted sink node:
          do (setf (aref graph i)
                   (make-ccmf-node :>-edges (delete-if f (ccmf-node->-edges node))
                                   :>=-edges (delete-if f (ccmf-node->=-edges node))))))

(defun-raw ccmf-remove-ccms-list (ccmfs deletep-array)
  ;; given a list of ccmfs and an array of arrays of booleans
  ;; indicating which ccms to delete for each context, calls
  ;; ccmf-remove-ccms on each ccmf in ccmfs with the appropriate
  ;; deletion arrays. this function is destructively updates each
  ;; ccmf.
  (dolist (ccmf ccmfs nil)
    (ccmf-remove-ccms ccmf
                      (aref deletep-array
                            (ccmf-firstsite ccmf))
                      (aref deletep-array
                            (ccmf-lastsite ccmf)))))

(defun-raw srg-restrict (srg ccms)
  ;; restricts the given srg to only the ccms indexed by the natural
  ;; numbers in the list ccms. this function is *not* destructive.
  (let* ((n (length ccms))
         (rsrg (make-array n)) ;; the restricted srg.
         (a (make-array (array-dimension srg 0) ;; maps the srg nodes
                        :element-type 'fixnum   ;; to their new index
                        :initial-element -1)))  ;; if they are in rsrg.
    ;; create a new node for each slot in rsrg with the node and ccm
    ;; of the appropriate node in the original srg. we also update the
    ;; map as we go mapping old node indices to new ones.
    (loop
     for p in ccms
     for i from 0
     for node = (aref srg p)
     do (setf (aref a p) i)
     do (setf (aref rsrg i)
              (make-srg-node :node (srg-node-node node)
                             :ccm  (srg-node-ccm  node))))
    (loop
     for p in ccms
     for i from 0
     for node = (aref srg p)
     for nnode = (aref rsrg i)
     do (loop for e in (srg-node-fwd-edges node)
              unless (= (aref a (srg-edge-head e)) -1)
              do (let* ((head (aref a (srg-edge-head e)))
                        (hnode (aref rsrg head))
                        (ne (make-srg-edge :head head
                                           :tail i
                                           :ccmf (srg-edge-ccmf e)
                                           :label (srg-edge-label e))))
                   (setf (srg-node-fwd-edges nnode)
                         (cons ne (srg-node-fwd-edges nnode)))
                   (setf (srg-node-bwd-edges hnode)
                         (cons ne (srg-node-bwd-edges hnode))))))
    rsrg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the following code implements the SCP analysis.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw srg-scc-for-node-aux (srg nn visited node-fwd-edges edge-head)
  ;; this is the helper function for srg-scc-for-node
  (setf (aref visited nn) t)
  (loop for edge in (funcall node-fwd-edges (aref srg nn))
        for head = (funcall edge-head edge)
        unless (aref visited head)
        do (srg-scc-for-node-aux srg head visited node-fwd-edges edge-head)))

(defun-raw srg-scc-for-node (srg nn)
  ;; given an srg and the index of a node in that srg (nn), returns an
  ;; array of booleans of the same size as srg which indicates for
  ;; each i whether the node of the srg at index i is in the same srg
  ;; as the node at index nn. it does so by traversing the srg from
  ;; node nn forwards and backwards and taking the intersection of the
  ;; nodes reached.
  (let* ((n (array-dimension srg 0))
         (in-scc-array (make-array n :element-type '(member t nil :ignore) :initial-element nil)))
    (let* ((n (array-dimension in-scc-array 0)))
      ;; traverse the graph forwards, using in-scc-array to keep track
      ;; of the visited nodes.
      (srg-scc-for-node-aux srg nn in-scc-array #'srg-node-fwd-edges #'srg-edge-head)
      ;; for our backwards traversal, we only want to visit nodes that
      ;; we already visited on our forward traversal. therefore, we
      ;; set the index of visited nodes to nil and the index of
      ;; unvisited nodes to the non-nil value :ignore.
      (loop for i from 0 below n
            if (aref in-scc-array i)
              do (setf (aref in-scc-array i) nil)
            else
              do (setf (aref in-scc-array i) :ignore))
      ;; now traverse the graph backwards.
      (srg-scc-for-node-aux srg nn in-scc-array #'srg-node-bwd-edges #'srg-edge-tail)
      ;; finally, reset any :ignore indices to nil, since they are not in the scc.
      (loop for i from 0 below n
            when (eq (aref in-scc-array i) :ignore)
              do (setf (aref in-scc-array i) nil))
      in-scc-array)))

(defun-raw srg-add-scc-for-node (srg nn in-scc-array)
  ;; takes the per-index disjunction of the boolean array in-scc-array
  ;; and the result of calling srg-scc-for-node on srg and nn. In
  ;; other words, given an array indicating which nodes are in a
  ;; collection of sccs, this function adds the scc containing node nn
  ;; to the array.
  (if (aref in-scc-array nn)
      in-scc-array
    (let ((new-in-scc-array (srg-scc-for-node srg nn)))
      (loop for i from 0 below (length in-scc-array)
            when (and (not (aref in-scc-array i))
                      (aref new-in-scc-array i))
            do (setf (aref in-scc-array i) t))
      in-scc-array)))

(defun-raw mtp (srg ccmfs num-contexts fwd-edges bwd-edges edge-head edge-tail)
  ;; generic function for finding a maximal thread presever (mtp) as
  ;; described in the scp paper. However, our algorithm is slightly
  ;; different than that described in the scp paper. this is because
  ;; we have a ccmf for every edge rather than every node. because of
  ;; this, we cannot keep one count value for each ccm in the srg,
  ;; since the are potentially multiple edges from the context
  ;; containing the ccm, and if the ccm is not non-increasing or
  ;; decreasing along any one of those edges, it is not part of the
  ;; mtp. therefore, for each ccm, we maintain several counts, one for
  ;; each outgoing edge.

  ;; the srg is an srg, the ccmfs is a list of ccmfs that should be
  ;; the ccmfs of the srg. num-contexts is the number of contexts
  ;; represented by the srg. fwd-edges, bwd-edges, edge-head, and
  ;; edge-tail are functions that tell us how to get around the
  ;; graph. these are here to allow us to quickly find mtps in a graph
  ;; and its inverse.
  (let* ((n (array-dimension srg 0))
         ;; we make the count array a matrix. for each ccm, we
         ;; maintain num-context counts. unless the accg is not
         ;; complete, some of these counts will always be 0. however,
         ;; this slight inefficiency in space allows us to maintain
         ;; simpler and more efficient code.
         (count (make-array `(,n ,num-contexts)
                            :element-type 'fixnum :initial-element 0))
         ;; the accg matrix is an adjacency matrix representation of
         ;; the accg implied by the ccmfs.
         (accg-matrix (make-array `(,num-contexts ,num-contexts)
                                   :element-type 'boolean
                                   :initial-element nil))
         ;; marked keeps track of which ccms are marked as not being
         ;; part of the mtp.
         (marked (make-array n :element-type 'boolean :initial-element nil))
         ;; the worklist keeps track of the ccms to visit.
         (worklist nil))
    ;; first, we construct the accg-matrix
    (dolist (ccmf ccmfs)
      (setf (aref accg-matrix (ccmf-firstsite ccmf) (ccmf-lastsite ccmf)) t))
    ;; next, we initiate the counts.
    (dotimes (i n)
      (let ((node (aref srg i)))
        ;; for each edge from node i, we increment the counter
        ;; corresponding to the index of the context for which the
        ;; head of e is a ccm:
        (dolist (e (funcall fwd-edges node))
          (incf (aref count i (srg-node-node (aref srg (funcall edge-head e))))))
        ;; for every successor of the context of node that has count 0
        ;; gets added to the worklist and is marked.
        (dotimes (j num-contexts)
          (when (and (aref accg-matrix (srg-node-node node) j)
                     (= (aref count i j) 0))
            (setf worklist (cons i worklist))
            (setf (aref marked i) t)))))
    ;; finally, we enter the meat of the algorithm, working through the worklist.
    (loop while (consp worklist)
          for cw = (car worklist)
          for j = (srg-node-node (aref srg cw))
          do (setf worklist (cdr worklist))
          ;; every node in the worklist is out of the mtp, so we
          ;; decrement the appropriate count of all its
          ;; predecessors. any of them whose count reaches 0 gets
          ;; added to the worklist and is marked.
          do (dolist (e (funcall bwd-edges (aref srg cw)))
               (let ((i (funcall edge-tail e)))
                 (unless (aref marked i)
                   (decf (aref count i j))
                   (when (= (aref count i j) 0)
                     (setf (aref marked i) t)
                     (setf worklist (cons i worklist))))))
          ;; finally, we return all the unmarked ccms.
          finally (return (loop for i from 0 below n
                                unless (aref marked i) collect i)))))

(defun-raw mtp-fwd (srg ccmfs num-contexts)
  ;; instantiation of mtp for analysis of the original srg/accg
  (mtp srg ccmfs num-contexts
       #'srg-node-fwd-edges #'srg-node-bwd-edges
       #'srg-edge-head #'srg-edge-tail))


(defun-raw mtp-bwd (srg ccmfs num-contexts)
  ;; instantiation of mtp for analysis of the transposition of the
  ;; srg/accg
  (mtp srg ccmfs num-contexts
       #'srg-node-bwd-edges #'srg-node-fwd-edges
       #'srg-edge-tail #'srg-edge-head))


(defun-raw fan-free (srg edge-list other-node num-contexts)
  ;; generic function for determining if there is no fanning in the
  ;; srg. edge-list is a function for retrieving the list of
  ;; incoming/outgoing edges of a node. other-node tells us how to get
  ;; the other node adjacent to an edge. num-contexts is the number of
  ;; contexts that the srg represents. in our context fanning is when
  ;; a ccm has multiple incoming/outgoing edges from ccms of the same
  ;; context.
  (loop
   with n = (array-dimension srg 0)
   ;; seen is an array keeping track of which contexts we have seen ccms from.
   with seen = (make-array num-contexts :element-type 'boolean :initial-element nil)
   for i from 0 below n
   ;; loop through the edges of srg ccm i, keeping track of the
   ;; contexts to which the adjacent ccms belong. if we see a context
   ;; twice, we have fanning and return nil.
   unless (loop for e in (funcall edge-list (aref srg i))
                for j = (funcall other-node e)
                for context = (srg-node-node (aref srg j))
                if (aref seen context) return nil
                else do (setf (aref seen context) t)
                finally (return t))
     return nil
   ;; reset the seen array. this is cheaper than creating a new array
   ;; for each iteration of the outer loop.
   do (loop for i from 0 below num-contexts
            do (setf (aref seen i) nil))
   finally (return t)))

(defun-raw fan-in-free (srg num-contexts)
  ;; instantiation of fan-free to check for fan-in
  (fan-free srg #'srg-node-bwd-edges #'srg-edge-tail num-contexts))


(defun-raw fan-out-free (srg num-contexts)
  ;; instantiation of fan-free to check for fan-out
  (fan-free srg #'srg-node-fwd-edges #'srg-edge-head num-contexts))

(defun-raw mtp-to-anchor (srg ahash)
  ;; given an srg that has been restricted to some mtp and a set of
  ;; ccmfs represented by a hash table, we add to ahash the anchor
  ;; implied by srg. that is, we add all ccmfs containing a > edge in
  ;; the restricted srg.
  (loop for i from 0 below (array-dimension srg 0)
        do (loop for e in (srg-node-fwd-edges (aref srg i))
                 when (and (eq (srg-edge-label e) '>)
                           (not (gethash (srg-edge-ccmf e) ahash)))
                   do (setf (gethash (srg-edge-ccmf e) ahash) t))
        finally (return ahash)))

(defun-raw simple-anchors (srg ahash ccmfs num-contexts)
  ;; simple anchors, also called type 1 anchors in other papers by the
  ;; scp authors, are anchors based on mtps.
  (let ((srgp (srg-restrict srg (mtp-fwd srg ccmfs num-contexts))))
    (if (fan-in-free srgp num-contexts)
        (mtp-to-anchor srgp ahash)
      (let ((srgq (srg-restrict srg (mtp-bwd srg ccmfs num-contexts))))
        (if (fan-out-free srgq num-contexts)
            (mtp-to-anchor srgq ahash)
          nil)))))

(defun-raw srg-restrict-edges (srg pred)
  ;; this function non-destructively constructs a new srg that is
  ;; identical to srg except it excludes edges that fail the
  ;; predicate, pred.
  (loop
   with n = (array-dimension srg 0)
   with rsrg = (make-array n)
   for i from 0 below n
   for node = (aref srg i)
   do (setf (aref rsrg i)
            (make-srg-node :node (srg-node-node node)
                           :ccm (srg-node-ccm node)
                           :fwd-edges (remove-if-not pred (srg-node-fwd-edges node))
                           :bwd-edges (remove-if-not pred (srg-node-bwd-edges node))))
   finally (return rsrg)))

(defun-raw ndg (srg)
  ;; constructs the no-descent graph, a subgraph of the srg consisting
  ;; of only nonstrict edges.
  (srg-restrict-edges srg (lambda (e) (eq (srg-edge-label e) '>=))))


(defun-raw srg-interior (srg)
  ;; constructs the interior of an srg, that is, the subgraph of the
  ;; srg consisting of the edges of the srg that are interior to an
  ;; scc of the srg.
  (multiple-value-bind
      (scc scc-array)
      (srg-scc srg)
    (declare (ignore scc))
    (srg-restrict-edges srg
                        (lambda (e)
                          (eq (aref scc-array (srg-edge-tail e))
                              (aref scc-array (srg-edge-head e)))))))


(defun-raw srg-to-matrix (srg)
  ;; straight-forward function for making an adjacency matrix of srg.
  (loop with n = (array-dimension srg 0)
        with matrix = (make-array (list n n)
                                  :element-type 'boolean
                                  :initial-element nil)
        for i from 0 below n
        do (loop for e in (srg-node-fwd-edges (aref srg i))
                 do (setf (aref matrix i (srg-edge-head e)) t))
        finally (return matrix)))

;;   (let* ((n (array-dimension srg 0))
;;          (matrix (make-array (list n n) :element-type 'boolean :initial-element nil)))
;;     (dotimes (i n matrix)
;;       (dolist (e (srg-node-fwd-edges (aref srg i)))
;;         (setf (aref matrix i (srg-edge-head e)) t)))))


(defun-raw ccmf-to-ccmfdown-in-srg (srg ccmf ndgi-matrix)
  ;; by ccmfdown, here, we mean the original ccmf minus any arcs
  ;; belonging to the interior of ndg of srg. for ccmf, G, this is
  ;; represented in the scp paper as G with a small down arrow to its
  ;; right. hence the name. we return a copy of the srg restricted to
  ;; not include edges in ccmfdown.
  (srg-restrict-edges srg
                      (lambda (e)
                        (not (and (eq (srg-node-node (aref srg (srg-edge-tail e)))
                                      (ccmf-firstsite ccmf))
                                  (eq (srg-node-node (aref srg (srg-edge-head e)))
                                      (ccmf-lastsite ccmf))
                                  (aref ndgi-matrix (srg-edge-tail e) (srg-edge-head e)))))))

(defun-raw anchor-find (srg ccmfs num-contexts)
  ;; the anchor finding algorithm, as given in the scp paper.
  (let ((ahash (make-hash-table :rehash-size 2 :rehash-threshold (float 3/4))))
    (multiple-value-bind
        (sccs scc-array)
        (srg-scc srg)
      (declare (ignore scc-array))
      ;; for every scc of the srg, look for simple anchors.
      (dolist (scc sccs)
        (simple-anchors (srg-restrict srg scc) ahash ccmfs num-contexts))
      ;; convert the set of anchors to a list.
      (let ((anchors (loop for k being the hash-keys of ahash using (hash-value v)
                           when v collect k)))
        ;;(format t "simple anchors: ~A~%" anchors)
        ;; if we have found anchors, return them.
        (if anchors
            anchors
          ;; otherwise, we attempt to find "type 2" anchors, as they
          ;; are called in the scp paper.
          (loop with ndgi-matrix = (srg-to-matrix (srg-interior (ndg srg)))
                for ccmf in ccmfs
                for h = (ccmf-to-ccmfdown-in-srg srg ccmf ndgi-matrix)
                when (or (mtp-fwd h ccmfs num-contexts)
                         (mtp-bwd h ccmfs num-contexts))
                  return (list ccmf)))))))

(defun-raw copy-a-ccmf (ccmf)
  (make-ccmf :firstsite (ccmf-firstsite ccmf)
             :lastsite (ccmf-lastsite ccmf)
             :fc-num (ccmf-fc-num ccmf)
             :lc-num (ccmf-lc-num ccmf)
             :graph (accg-copy-ccmf-graph (ccmf-graph ccmf))
             :in-sizes (ccmf-in-sizes ccmf)
             :out-sizes (ccmf-out-sizes ccmf)
             :steps (ccmf-steps ccmf)))

(defun-raw copy-ccmfs (ccmfs)
  ;; just like it says, this function copies a list of ccmfs.
  (loop for ccmf in ccmfs
    collect (copy-a-ccmf ccmf)))

(defun-raw copy-accg (accg)
  (let* ((n (array-dimension accg 0))
         (naccg (make-array n)))
    (loop for i from 0 below n
          for node = (aref accg i)
          do (setf (aref naccg i)
                   (make-accg-node :context (accg-node-context node)
                                   :num i)))
    (loop
     for node across accg
     for nnode across naccg
     do (setf (accg-node-fwd-edges nnode)
              (loop
               for edge in (accg-node-fwd-edges node)
               for head = (accg-edge-head edge)
               for hnode = (aref naccg head)
               for nedge = (make-accg-edge
                            :tail (accg-edge-tail edge)
                            :head head
                            :ccmf (copy-a-ccmf (accg-edge-ccmf edge)))
               do (setf (accg-node-bwd-edges hnode)
                        (cons nedge (accg-node-bwd-edges hnode)))
               collect nedge)))
    naccg))

(defun-raw accg-ccmfs (accg)
  ;; returns all the ccmfs used to annotate accg
  (loop for node across accg
        append (mapcar #'accg-edge-ccmf
                       (accg-node-fwd-edges node))))
;;   (let ((ccmfs nil))
;;     (dotimes (i (array-dimension accg 0) ccmfs)
;;       (dolist (e (accg-node-fwd-edges (aref accg i)))
;;         (setf ccmfs (cons (accg-edge-ccmf e) ccmfs))))))

(defun-raw accg-contexts (accg)
  ;; returns the contexts of the accg.
  (map 'vector (lambda (x) (accg-node-context x)) accg))

(defun-raw accg-srg-add-edge (tailnode headnode tailnum headnum ccmf label)
  ;; adds an adge to the tailnode and headnode of an srg.
  (let ((edge (make-srg-edge :tail tailnum
                             :head headnum
                             :ccmf ccmf
                             :label label)))
    (setf (srg-node-fwd-edges tailnode)
          (cons edge (srg-node-fwd-edges tailnode)))
    (setf (srg-node-bwd-edges headnode)
          (cons edge (srg-node-bwd-edges headnode)))
    nil))

(defun-raw accg-remove-edges-corresponding-to-ccmfs (accg ccmfs)
  ;; destructively removes edges corresponding to the list of ccmfs from the
  ;; accg. The ccmfs must be pointer-equal (eq) to the ones you want removed
  ;; from the accg.

  ;; first, we set the firstsite field of the ccmfs we want to remove
  ;; to -1.
  (loop for ccmf in ccmfs do (setf (ccmf-firstsite ccmf) -1))
  ;; next, we loop through all the accg-nodes, deleting any
  ;; incoming/outgoing edges whose firstsite is -1.
  (loop with pred = (lambda (edge)
                      (= (ccmf-firstsite (accg-edge-ccmf edge)) -1))
        for node across accg
        do (setf (accg-node-fwd-edges node)
                 (delete-if pred (accg-node-fwd-edges node)))
        do (setf (accg-node-bwd-edges node)
                 (delete-if pred (accg-node-bwd-edges node))))
  accg)

(defun-raw accg-construct-srg (accg)
  ;; constructs an srg from a accg. to do this, we "flatten" out the
  ;; ccms of each accg-node, laying all the ccms from all the
  ;; accg-nodes next to each other and creating an srg-node for each
  ;; ccm.
  (let* ((n (array-dimension accg 0))
         ;; we need an offset array to tell us what index in the srg
         ;; corresponds to the first ccm in each accg-node.
         (node-offset (make-array n
                                  :element-type 'fixnum
                                  :initial-element 0))
         (c 0))
    ;; compute the offsets:
    (dotimes (i n)
      (setf (aref node-offset i) c)
      (incf c (array-dimension (accg-node-ccms (aref accg i)) 0)))
    ;; at this point c = the number of nodes in the srg.
    (let ((srg (make-array c
                           :element-type 'srg-node
                           :initial-element (make-srg-node))))
      ;; make all the new nodes.
      (loop for i from 1 below c
            do (setf (aref srg i) (make-srg-node)))
      ;; now we add all the edges.
      (loop ;; we loop through the accg
       for i from 0 below n
       do (loop ;; we loop through the fwd-ccmfs of node i
           for edge in (accg-node-fwd-edges (aref accg i))
           for ccmf = (accg-edge-ccmf edge)
           for offset1 = (aref node-offset i)
           for offset2 = (aref node-offset (accg-edge-head edge))
           for cg = (ccmf-graph ccmf)
           do (loop ;; we loop through the ccmf.
               for j from 0 below (array-dimension cg 0)
               for a from offset1
               for nodea = (aref srg a)
               do (setf (srg-node-node nodea) i)
               do (setf (srg-node-ccm nodea) j)
               do (loop ;; we loop through the >-edges and add them to the srg.
                   for x in (ccmf-node->-edges (aref cg j))
                   for b = (+ offset2 x)
                   do (accg-srg-add-edge nodea (aref srg b) a b ccmf '>))
               do (loop ;; we loop through the >=-edges and add them to the srg.
                   for x in (ccmf-node->=-edges (aref cg j))
                   for b = (+ offset2 x)
                   do (accg-srg-add-edge nodea (aref srg b) a b ccmf '>=))))
       finally (return srg)))))

(defun-raw cln-accg (accg)
  ;; this function cleans a accg by removing any ccmf edge that is
  ;; not internal to an scc in the corresponding srg that contains a >
  ;; edge.
  (let* ((srg (accg-construct-srg accg)) ;; the srg for the accg.
         (n (array-dimension accg 0))
         (deletep-array (make-array n))) ;; tells us which ccms to delete.
    ;; initiate the deletep-array
    (dotimes (i n)
      (setf (aref deletep-array i)
            (make-array (array-dimension
                         (accg-node-ccms (aref accg i))
                         0)
                        :element-type 'boolean
                        :initial-element nil)))
    ;; analyze the sccs of the srg.
    (multiple-value-bind
        (sccs scc-array)
        (srg-scc srg)
      ;; for each scc, add the nodes of the scc to the deletep array
      ;; unless it contains a > edge.
      (loop for scc in sccs
            unless (srg-scc-has->-edgep scc scc-array srg)
            do (loop for v in scc
                     for node = (aref srg v)
                     for context = (srg-node-node node)
                     for ccm = (srg-node-ccm node)
                     do (setf (aref (aref deletep-array context) ccm) t))))
    ;; destructively remove the unwanted ccms.
    (progn
      (ccmf-remove-ccms-list (accg-ccmfs accg)
                             deletep-array)
      accg)))

(defun-raw scp (accg)
  ;; the main scp algorithm. it takes an accg and recursively removes
  ;; anchors and analyzes the sccs of the remainder of the graph until
  ;; either there is no graph left, or we can't find any more
  ;; anchors. see the scp paper.
  (when accg
    (let* ((n (array-dimension accg 0))
           (anchors (anchor-find (accg-construct-srg accg)
                                 (accg-ccmfs accg)
                                 n)))
      (when anchors
        (mv-let
         (changes sccs)
         (accg-separate-sccs
                     (accg-remove-edges-corresponding-to-ccmfs accg anchors))
         (declare (ignore changes))
         (loop for scc in sccs
               unless (scp (cln-accg scc))
               return nil
               finally (return t)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the following code implements the SCT analysis
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct-raw scg-path
  ;; the first num in the path
  (start 0 :type fixnum)
  ;; the second num in the path
  (end 0 :type fixnum)
  ;; the total length of the path
  (length 0 :type fixnum)
  ;; the interior of the path (everything except the start and end). We
  ;; represent this as a tree so that we don't have to append every time we
  ;; compose SCGs. We do this in such a way that a depth-first car-to-cdr
  ;; seorch of the tree returns the path.
  (interior nil :type (or null fixnum cons)))

(defun-raw new-scg-path (start end)
  (make-scg-path :start start
                 :end end
                 :length 2
                 :interior nil))

(defun-raw compose-scg-paths (p1 p2)
  (make-scg-path :start (scg-path-start p1)
                 :end (scg-path-end p2)
                 :length (1- (+ (scg-path-length p1)
                                (scg-path-length p2)))
                 :interior (let ((x (if (null (scg-path-interior p2))
                                        (scg-path-start p2)
                                      (cons (scg-path-start p2)
                                            (scg-path-interior p2)))))
                             (if (null (scg-path-interior p1))
                                 x
                               (cons (scg-path-interior p1) x)))))

(defun-raw flatten-scg-interior (interior acc)
  (cond ((null interior)
         acc)
        ((atom interior)
         (cons interior acc))
        (t
         (flatten-scg-interior (car interior)
                               (flatten-scg-interior (cdr interior)
                                                     acc)))))

(defun-raw flatten-scg-path (path)
  (cons (scg-path-start path)
        (flatten-scg-interior (scg-path-interior path)
                              (list (scg-path-end path)))))


;; for the purposes of this algorithm, we only need to know the starts and ends
;; of paths. We only need the interior to construct the paths later. Therefore,
;; we define functions for equality and ordering paths accordingly.
(defun-raw scg-path-equal (p1 p2)
  (and (= (scg-path-start p1)
          (scg-path-start p2))
       (= (scg-path-end p1)
          (scg-path-end p2))))

(defun-raw path< (p1 p2)
  (or (< (scg-path-start p1)
         (scg-path-start p2))
      (and (= (scg-path-start p1)
              (scg-path-start p2))
           (< (scg-path-end p1)
              (scg-path-end p2)))))


;; since we keep the interior of a path aronud for constructing
;; counter-examples, we want to keep around the shortest path. Therefore, when
;; given two paths with identical start and end points, we pick the one with
;; the shortest path.
(defun-raw shortest-scg-path (p1 p2)
  (if (<= (scg-path-length p1)
          (scg-path-length p2))
      p1
    p2))

(defstruct-raw scg
  (paths nil :type list)
  (newest-paths nil :type list)
  (new-newest-paths nil :type list)
  (num 0 :type fixnum)
  (graph nil))

(defun-raw sorted-set-union1 (lst1 lst2 key1 key2 predicate combine key test)
  ;; lst1 and lst2 should be sorted, non-empty lists.
  ;; key1 should be equal to (funcall key (car lst1))
  ;; key2 should be equal to (funcall key (car lst2))
  ;; key should be a unary function that returns an equal-able value.
  (cond ((funcall test key1 key2)
         (cons (car lst1)
               (sorted-set-union (cdr lst1) (cdr lst2)
                                 predicate
                                 :key key
                                 :combine combine
                                 :test test)))
        ((funcall predicate key1 key2)
         (cons (car lst1)
               (if (endp (cdr lst1))
                   lst2
                 (sorted-set-union1 (cdr lst1) lst2
                                    (funcall key (cadr lst1))
                                    key2
                                    predicate
                                    combine
                                    key
                                    test))))
        (t
         (cons (car lst2)
               (if (endp (cdr lst2))
                   lst1
                 (sorted-set-union1 lst1 (cdr lst2)
                                    key1
                                    (funcall key (cadr lst2))
                                    predicate
                                    combine
                                    key
                                    test))))))

(defun-raw sorted-set-union (lst1 lst2 predicate
                                  &key (key #'identity)
                                  (combine #'(lambda (x y)
                                               (declare (ignore y))
                                               x))
                                  (test #'equal))
  (cond ((endp lst1) lst2)
        ((endp lst2) lst1)
        (t
         (sorted-set-union1 lst1 lst2
                            (funcall key (car lst1))
                            (funcall key (car lst2))
                            predicate
                            combine
                            key
                            test))))

(defun-raw sorted-set-difference1 (lst1 lst2 key1 key2 predicate key test)
  ;; lst1 and lst2 should be sorted, non-empty lists.
  ;; key1 should be equal to (funcall key (car lst1))
  ;; key2 should be equal to (funcall key (car lst2))
  ;; key should be a unary function that returns an equal-able value.
  (cond ((funcall test key1 key2)
         (sorted-set-difference (cdr lst1) (cdr lst2)
                                predicate
                                :key key
                                :test test))
        ((funcall predicate key1 key2)
         (cons (car lst1)
               (if (endp (cdr lst1))
                   nil
                 (sorted-set-difference1 (cdr lst1) lst2
                                         (funcall key (cadr lst1))
                                         key2
                                         predicate
                                         key
                                         test))))
        (t
         (if (endp (cdr lst2))
             lst1
           (sorted-set-difference1 lst1 (cdr lst2)
                                   key1
                                   (funcall key (cadr lst2))
                                   predicate
                                   key
                                   test)))))

(defun-raw sorted-set-difference (lst1 lst2 predicate
                                       &key (key #'identity)
                                       (test #'equal))
  (cond ((endp lst1) nil)
        ((endp lst2) lst1)
        (t
         (sorted-set-difference1 lst1 lst2
                                (funcall key (car lst1))
                                (funcall key (car lst2))
                                predicate
                                key
                                test))))

(defun-raw sorted-union/difference1 (lst1 lst2 key1 key2 predicate combine key test)
  ;; lst1 and lst2 should be sorted, non-empty lists.
  ;; key1 should be equal to (funcall key (car lst1))
  ;; key2 should be equal to (funcall key (car lst2))
  ;; key should be a unary function that returns an equal-able value.
  (cond ((funcall test key1 key2)
         (mv-let (union difference)
                 (sorted-union/difference (cdr lst1) (cdr lst2)
                                          predicate
                                          :combine combine
                                          :key key
                                          :test test)
                 (mv (cons (funcall combine (car lst1) (car lst2))
                           union)
                     difference)))
        ((funcall predicate key1 key2)
         (mv-let (union difference)
                 (if (endp (cdr lst1))
                     (mv lst2 nil)
                   (sorted-union/difference1 (cdr lst1) lst2
                                             (funcall key (cadr lst1))
                                             key2
                                             predicate
                                             combine
                                             key
                                             test))
                 (mv (cons (car lst1) union)
                     (cons (car lst1) difference))))
        (t
         (mv-let (union difference)
                 (if (endp (cdr lst2))
                     (mv lst1 lst1)
                   (sorted-union/difference1 lst1 (cdr lst2)
                                             key1
                                             (funcall key (cadr lst2))
                                             predicate
                                             combine
                                             key
                                             test))
                 (mv (cons (car lst2) union)
                     difference)))))

(defun-raw sorted-union/difference (lst1 lst2 predicate
                                         &key (key #'identity)
                                         (combine #'(lambda (x y)
                                                      (declare (ignore y))
                                                      x))
                                         (test #'equal))
  (cond ((endp lst1) (mv lst2 nil))
        ((endp lst2) (mv lst1 lst1))
        (t
         (sorted-union/difference1 lst1 lst2
                                   (funcall key (car lst1))
                                   (funcall key (car lst2))
                                   predicate
                                   combine
                                   key
                                   test))))

(defun-raw sorted-adjoin (element set predicate
                                  &key (key #'identity)
                                  (combine #'(lambda (x y)
                                                      (declare (ignore y))
                                                      x))
                                  (test #'equal))
  (sorted-set-union (list element) set predicate
                    :key key :combine combine :test test))

(defun-raw sorted-remove-duplicates1 (lst carkey key combine test)
  (if (endp (cdr lst))
      lst
    (let ((cadrkey (funcall key (cadr lst))))
      (if (funcall test carkey cadrkey)
          (let ((comb (funcall combine (car lst) (cadr lst))))
            (sorted-remove-duplicates1  (cons comb (cddr lst))
                                        (funcall key comb)
                                        key
                                        combine
                                        test))
        (cons (car lst)
              (sorted-remove-duplicates1 (cdr lst)
                                        cadrkey
                                        key
                                        combine
                                        test))))))

(defun-raw sorted-remove-duplicates (lst &key (key #'identity)
                                         (combine #'(lambda (x y)
                                                      (declare (ignore y))
                                                      x))
                                         (test #'equal))
  (cond ((endp lst) nil)
        ((endp (cdr lst)) lst)
        (t
         (sorted-remove-duplicates1 lst
                                    (funcall key (car lst))
                                    key
                                    combine
                                    test))))


(defun-raw list-to-sorted-set (lst predicate
                                   &key (key #'identity)
                                   (combine #'(lambda (x y)
                                                      (declare (ignore y))
                                                      x))
                                   (test #'equal))
  ;; WARNING: THIS FUNCTION IS DESTRUCTIVE TO LST.
  (sorted-remove-duplicates (sort lst predicate :key key)
                            :key key
                            :combine combine
                            :test test))

(defun-raw scg-graph-key (graph)
  #-gcl
  graph
  #+gcl
  (loop for node across graph
        for >-edges = (ccmf-node->-edges node)
        for >=-edges = (ccmf-node->=-edges node)
        collect (cons (length >-edges) (length >=-edges)) into lens
        collect (cons >-edges >=-edges) into lst
        finally (list* (array-dimension graph 0) lens lst)))

(defun-raw update-scg-paths (graph paths i graph-hash)
  ;; graph is a ccmf-graph
  ;; paths is a sorted set of paths to be added for graph
  ;; i is our scg counter, used for giving each scg a unique numerical id.
  ;; graph-hash is an equalp hash-table (an equal hash-table in GCL)
  ;;
  ;; OUTPUT: 4 values:
  ;; 1. the new value of i.
  ;; 2. whether this is the first update to the new-newest-paths of the scg.
  ;; 3. the new paths added.
  ;; 4. the scg that was updated.
  ;; (format t "~&Calling: ~A~%" `(update-scg-paths ,graph ,paths ,i ,graph-hash))
  (let* ((key (scg-graph-key graph))
         (scg (gethash key graph-hash)))
    (if scg
        (let* ((new-newest-paths (scg-new-newest-paths scg))
               (npaths (sorted-set-difference
                        (sorted-set-difference paths
                                               (scg-paths scg)
                                               #'path<
                                               :test #'scg-path-equal)
                        (scg-newest-paths scg)
                        #'path<
                        :test #'scg-path-equal)))
          (mv-let (union difference)
                  (sorted-union/difference npaths new-newest-paths #'path<
                                           :test #'scg-path-equal
                                           :combine #'shortest-scg-path)
                  (progn
                    (setf (scg-new-newest-paths scg) union)
                    (mv i (endp new-newest-paths) difference scg))))
      (let ((nscg (make-scg :graph graph
                            :num i
                            :new-newest-paths paths)))
        (setf (gethash key graph-hash) nscg)
        ;; (format t "Returning: ~A~%"
        ;;                       `(update-scg-paths ,(1+ i)
        ;;                                          t
        ;;                                          ,paths
        ;;                                          ,nscg))
        (mv (1+ i) t paths nscg)))))

(defun-raw age-scgs (lst)
  ;; lst is a list of scgs
  ;;
  ;; SIDE-EFFECT: the scgs are "aged", i.e. their newest-paths are unioned with
  ;; their paths, the new-newest-paths are moved to the newest-paths, and their
  ;; new-newest-paths slot is set to nil.
  ;;
  ;; OUTPUT: lst
  (loop for scg in lst
        do (setf (scg-paths scg)
                 (sorted-set-union (scg-paths scg)
                                   (scg-newest-paths scg)
                                   #'path<
                                   :combine #'shortest-scg-path
                                   :test #'scg-path-equal))
        do (setf (scg-newest-paths scg)
                 (scg-new-newest-paths scg))
        do (setf (scg-new-newest-paths scg)
                 nil)
        finally (return lst)))

(defun-raw ccmfs-to-scgs1 (ccmfs graph-hash i acc)
  (if (endp ccmfs)
      (mv i (sort acc #'< :key #'scg-num))
    (let ((ccmf (car ccmfs)))
      (mv-let (ni new? diff scg)
              (update-scg-paths (ccmf-graph ccmf)
                                (list (new-scg-path (ccmf-firstsite ccmf)
                                                    (ccmf-lastsite ccmf)))
                                i
                                graph-hash)
              (ccmfs-to-scgs1 (cdr ccmfs) graph-hash ni
                              (if (and new? (consp diff))
                                  (cons scg acc)
                                acc))))))

(defun-raw ccmfs-to-scgs (ccmfs graph-hash)
  (ccmfs-to-scgs1 ccmfs graph-hash 0 nil))

(defun-raw compose-scg-graphs (g h)
  (loop with n = (array-dimension g 0)
        with gh = (make-array (array-dimension g 0)
                              :element-type 'ccmf-node
                              :initial-element (make-ccmf-node))
        for i below n
        for nodei = (aref g i)
        for >-edges = nil
        for >=-edges = nil
        do (loop for j in (ccmf-node->-edges nodei)
                 for nodej = (aref h j)
                 do (loop for k in (ccmf-node->-edges nodej)
                          do (setf >-edges (cons k >-edges)))
                 do (loop for k in (ccmf-node->=-edges nodej)
                          do (setf >-edges (cons k >-edges))))
        do (loop for j in (ccmf-node->=-edges nodei)
                 for nodej = (aref h j)
                 do (loop for k in (ccmf-node->-edges nodej)
                          do (setf >-edges (cons k >-edges)))
                 do (loop for k in (ccmf-node->=-edges nodej)
                          do (setf >=-edges (cons k >=-edges))))
        do (let* ((sorted->-edges (list-to-sorted-set >-edges #'<)))
             (setf (aref gh i)
                   (make-ccmf-node
                    :>-edges sorted->-edges
                    :>=-edges (sorted-set-difference
                               (list-to-sorted-set >=-edges #'<)
                               sorted->-edges
                               #'<))))
        finally (return gh)))

(defun-raw compose-scg-path-lsts1 (gpath hpaths acc)
  (if (or (endp hpaths)
          (not (= (scg-path-start (car hpaths))
                  (scg-path-end gpath))))
    acc
    (compose-scg-path-lsts1 gpath (cdr hpaths)
                            (cons (compose-scg-paths gpath (car hpaths))
                                  acc))))

(defun-raw compose-scg-path-lsts (gpaths hpaths acc)
  ;; gpaths should be a list of paths sorted in increasing order by their cdrs.
  ;; hpaths should be a list of paths sorted in increasing order by their cars.
  ;; acc is the accumulator
  ;; returns a sorted-set of paths (sorted by path<).
  (cond ((or (endp gpaths) (endp hpaths))
         (list-to-sorted-set acc #'path<
                             :test #'scg-path-equal
                             :combine #'shortest-scg-path))
        ((< (scg-path-end (car gpaths))
            (scg-path-start (car hpaths)))
         (compose-scg-path-lsts (cdr gpaths) hpaths acc))
        ((> (scg-path-end (car gpaths))
            (scg-path-start (car hpaths)))
         (compose-scg-path-lsts gpaths (cdr hpaths) acc))
        (t
         (compose-scg-path-lsts (cdr gpaths)
                                hpaths
                                (compose-scg-path-lsts1 (car gpaths)
                                                        hpaths
                                                        acc)))))

(defun-raw scg-counter-example? (scg diff)
  (and ;;there is a new self loop:
   (loop for path in diff
         when (= (scg-path-start path)
                 (scg-path-end path))
           return t
         finally (return nil))
   ;;there is no old self loop (in which case, we have already checked it out).
   (loop for path in (append (scg-paths scg)
                             (scg-newest-paths scg)
                             (sorted-set-difference (scg-new-newest-paths scg)
                                                    diff
                                                    #'path<
                                                    :test #'scg-path-equal))
         when (= (scg-path-start path)
                 (scg-path-end path))
           return nil
         finally (return t))
   ;; there is no >-edge from a CCM to itself:
   (loop with graph = (scg-graph scg)
         for i from 0 below (array-dimension graph 0)
         when (member i (ccmf-node->-edges (aref graph i)))
           return nil
         finally (return t))
   ;; the graph is idempotent
   (let ((graph (scg-graph scg)))
     (equalp (compose-scg-graphs graph graph)
             graph))))

(defun-raw shortest-self-loop (paths path)
  (cond ((endp paths) path)
        ((= (scg-path-start (car paths))
            (scg-path-end (car paths)))
         (shortest-self-loop (cdr paths)
                             (if (or (null path)
                                     (< (scg-path-length (car paths))
                                        (scg-path-length path)))
                                 (car paths)
                               path)))
        (t
         (shortest-self-loop (cdr paths) path))))

(defun-raw compose-scgs (g h i graph-hash)
  (let ((ghgraph (compose-scg-graphs (scg-graph g) (scg-graph h)))
        (ghpaths (compose-scg-path-lsts (sort (copy-list (scg-newest-paths g))
                                              #'< :key #'scg-path-end)
                                        (scg-newest-paths h)
                                        nil)))
    (mv-let (ni new? diff gh)
            (update-scg-paths ghgraph ghpaths i graph-hash)
            (if (scg-counter-example? gh diff)
                (mv t ni (cons (scg-graph gh)
                               (flatten-scg-path (shortest-self-loop diff nil))))
              (mv nil ni (if (and new? (consp diff)) gh nil))))))

(defun-raw scg-predecessors (scg)
  (sorted-remove-duplicates (mapcar #'scg-path-start (scg-newest-paths scg))))

(defun-raw scg-successors (scg)
  (list-to-sorted-set (mapcar #'scg-path-end (scg-newest-paths scg))
                      #'<))

(defun-raw organize-scgs-by-preds1 (scgs array)
  (if (endp scgs)
      nil
    (let ((scg (car scgs)))
      ;; to maintain the sortedness of the slots in the array, we loop through
      ;; and build our lists on the way back.
      (organize-scgs-by-preds1 (cdr scgs) array)
      (loop for i in (scg-predecessors scg)
            do (setf (aref array i)
                     (cons scg (aref array i)))))))

(defun-raw organize-scgs-by-preds (scgs numsites)
  (let ((array (make-array numsites :initial-element nil :element-type 'list)))
    (organize-scgs-by-preds1 scgs array)
    array))

(defun-raw union-scgs (scg-array indices)
  (loop for i in indices
        append (aref scg-array i) into union
        finally (return (list-to-sorted-set union #'< :key #'scg-num))))

(defun-raw copy-scgs (scgs)
  (loop for scg in scgs
        collect (make-scg :graph (scg-graph scg)
                          :num (scg-num scg)
                          :paths (scg-paths scg)
                          :newest-paths (scg-newest-paths scg)
                          :new-newest-paths (scg-new-newest-paths scg))))

(defun print-sct-loop-report (iteration comps state)
  (ccg-io? performance nil state
           (iteration comps)
           (fms "Iteration: ~x0 Compositions: ~x1."
                (list (cons #\0 iteration)
                      (cons #\1 comps))
                *standard-co*
                state
                nil)))

(defun-raw print-sct-total-report (success? comps graph-hash start-time state)
  (mv-let
   (col state)
   (ccg-io? size-change nil (mv col state)
            (success?)
            (fmt "~%SCT has found ~#0~[no~/a~] counter-example to ~
                  termination. "
                 (list (cons #\0 (if success? 0 1)))
                 *standard-co*
                 state
                 nil)
            :default-bindings ((col 0)))
   (mv-let
    (col state)
    (ccg-io? performance nil (mv col state)
             (comps graph-hash start-time internal-time-units-per-second)
             (fmt1 "In the process, ~x0 total ~#1~[compositions ~
                    were~/composition was~] performed and ~x2 unique ~
                    ~#3~[graphs were~/graph was~] created. Total time taken ~
                    was ~x4 seconds.~|"
                   (list (cons #\0 comps)
                         (cons #\1 (if (= comps 1) 1 0))
                         (cons #\2 (hash-table-count graph-hash))
                         (cons #\3 (if (= (hash-table-count graph-hash) 1)
                                       1 0))
                         (cons #\4 (/ (- (get-internal-run-time) start-time)
                                      ;;internal-time-units-per-second
                                      (coerce internal-time-units-per-second 'float))))
                   col
                   *standard-co*
                   state
                   nil)
             :default-bindings ((col 0)))
    (mv-let
     (col state)
     (ccg-io? size-change nil (mv col state)
              ()
              (fmt1 "~|" nil col *standard-co* state nil))
     (declare (ignore col))
     state))))

(defun-raw sct (ccmfs numsites state)
  ;; ccmfs: a list of CCMFs to be analyzed
  ;; numsites: the number of contexts over which the CCMFs range.
  ;; state: the state
  ;;
  ;; OUTPUT: an error triple whose value is a counter-example of the form (cons
  ;; g p) where g is a ccmf-graph and p is the shortest self-looping path
  ;; associated with g.

  ;; the basic algorithm for sct is fairly simple:
  ;; * let S be the set of SCGs
  ;; * repeat the following
  ;;   * if there is a maximal ccmf without a > edge from some ccm to
  ;;     itself, return the counter-example associated with that ccmf.
  ;;   * let S' be S unioned with the result of composing every pair
  ;;     <s,s'> in SxS such that the lastsite of s is the firstsite of s'.
  ;;   * if S' = S, return nil
  ;;   * set S <- S'
  ;;
  ;; however, this is inefficient, due to duplicate SCGs and the associativity
  ;; of composition. Therefore, we do the following.

  (let ((graph-hash (make-hash-table :test #-gcl 'equalp #+gcl 'equal))
        (start-time (get-internal-run-time)))
    ;; first, we create the scgs, putting them in the graph-hash
    (mv-let
     (i newest)
     (ccmfs-to-scgs ccmfs graph-hash)
     (progn
       ;;(format t "~&i: ~A~%newest: ~A~%" i newest)
       ;; we check if any of the new scgs are counter-examples to termination.
       (loop
        for scg in newest
        for nnp = (scg-new-newest-paths scg)
        when (scg-counter-example? scg nnp)
        do (return-from sct (value (cons (scg-graph scg)
                                         (flatten-scg-path
                                          (shortest-self-loop nnp nil))))))
       ;; we age the scgs.
       (age-scgs newest)
       ;; the main loop:
       (loop
        with total-comps = 0
        with generators = (organize-scgs-by-preds (copy-scgs newest) numsites)
        until (endp newest)
        for iteration from 0
        for new-newest = nil
        for comps = 0
        ;;do (print iteration)
        ;; for every scg, g, to be processed
        do (loop
            for g in newest
            ;; all the ends of the pathst associated with g:
            for gsucc = (scg-successors g)
            do (loop
                ;; for each generator that starts at a context where g ends,
                for h in (union-scgs generators gsucc)
                ;; compose them together, checking for counter-examples along
                ;; the way
                do (mv-let (counter-example? ni gh)
                           (compose-scgs g h i graph-hash)
                           (progn
                             (incf comps)
                             (incf total-comps)
                             (setf i ni)
                             ;; if we've found it, print out the report and
                             ;; return the counter-example.
                             (cond (counter-example?
                                    (pprogn
                                     (increment-timer 'other-time state)
                                     (print-sct-loop-report iteration comps
                                                            state)
                                     (print-sct-total-report nil
                                                             total-comps
                                                             graph-hash
                                                             start-time
                                                             state)
                                     (increment-timer 'print-time state)
                                     (return-from sct (value gh))))
                                   ;; otherwise, if gh is new and different, we
                                   ;; add it to our new-newest set.
                                   (gh
                                    (setf new-newest
                                          (cons gh new-newest))))))))
        ;; we age all of our SCGs.
        do (age-scgs (list-to-sorted-set (append newest
                                                 (copy-list new-newest))
                                         #'< :key #'scg-num))
        ;; new-newest is the new newest (hence the name).
        do (setf newest new-newest)
        ;; print the loop report.
        do (pprogn
            (increment-timer 'other-time state)
            (print-sct-loop-report iteration comps state)
            (increment-timer 'print-time state))
        ;; if we never find a counter-example, print out the report and return
        ;; nil.
        finally (pprogn
                 (increment-timer 'other-time state)
                 (print-sct-total-report t total-comps graph-hash start-time state)
                 (increment-timer 'print-time state)
                 (return (value nil))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the rest of the code connects our termination analysis with ACL2's ;;;
;;; function admission process.                                        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw find-funct (fn functs)
  (cond ((endp functs)
         (make-funct :fn fn))
        ((eq fn (funct-fn (car functs)))
         (car functs))
        (t
         (find-funct fn (cdr functs)))))

(defun-raw t-machine-to-contexts (t-machine parent-funct functs)
  (if (endp t-machine)
      nil
    (let* ((tac (car t-machine))
           (call (access tests-and-call tac :call)))
      (cons (make-context :ruler (access tests-and-call tac :tests)
                          :call call
                          :parent-funct parent-funct
                          :call-funct (find-funct (ffn-symb call) functs))
            (t-machine-to-contexts (cdr t-machine) parent-funct functs)))))

(defun-raw t-machines-to-contexts1 (t-machines functs all-functs)
  (if (endp t-machines)
      nil
    (cons (t-machine-to-contexts (car t-machines)
                                 (car functs)
                                 all-functs)
          (t-machines-to-contexts1 (cdr t-machines)
                                   (cdr functs)
                                   all-functs))))

(defun-raw t-machines-to-contexts (t-machines functs)
  (t-machines-to-contexts1 t-machines functs functs))

(defun-raw make-funct-structs (names arglists)
  (if (endp names)
      nil
    (cons (make-funct :fn (car names)
                      :formals (car arglists))
          (make-funct-structs (cdr names) (cdr arglists)))))

(defun ccg-measures-declared (measures)
  ;;; tells us whether the user declared any measures
  (and (consp measures)
       (or (not (equal (car measures) *0*))
       (ccg-measures-declared (cdr measures)))))

(defun-raw context-array (contexts)
  ;; turns a list of lists of contexts into an array and fixes the
  ;; context-num field of each context to be its index in the array.
  (let ((carray (coerce (loop for cs in contexts
                              append cs)
                        'vector)))
    (loop for i from 0 below (length carray)
          do (setf (context-num (aref carray i))
                   (list i)))
    carray))

(defun-raw accg-scp-list (lst proved unproved)
  ;; given a list of accgs, lst, performs scp on a cleaned version of the accg,
  ;; putting the cleaned accg into proved if scp determines the accg is
  ;; terminating or the original accg into unproved if it is not proven
  ;; terminating.
  (if (endp lst)
      (mv proved unproved)
    (let* ((accg (cln-accg (copy-accg (car lst)))))
      (cond ((scp (copy-accg accg))
             (accg-scp-list (cdr lst)
                            (cons accg proved)
                            unproved))
            (t
             (accg-scp-list (cdr lst) proved (cons (car lst) unproved)))))))

(defun-raw accg-sct-list1 (lst i n proved unproved ces state)
  ;; given a list of accgs, lst, performs sct on a cleaned version of each
  ;; accg, putting the cleaned into proved if sct determines the accg is
  ;; terminating or the original accg into unproved if it is not proven
  ;; terminating.
  (if (endp lst)
      (pprogn
       (let ((plen (len proved)))
         (ccg-io? basics nil state
                  (plen unproved)
                  (fms "Size-change analysis has proven ~x0 out of ~x1 SCCs of ~
                       the CCG terminating.~|"
                       `((#\0 . ,plen)
                         (#\1 . ,(+ plen (len unproved))))
                       *standard-co*
                       state
                       nil)))
       (value (list* proved unproved ces)))
    (pprogn
     (increment-timer 'other-time state)
     (ccg-io? size-change nil state
              ()
              (fms "We now begin size change analysis on the ~n0 SCC out of ~
                    ~n1."
                   (list (cons #\0 `(,i))
                         (cons #\1 n))
                   *standard-co*
                   state
                   nil))
     (increment-timer 'print-time state)
     (let* ((accg (cln-accg (copy-accg (car lst)))))
       (if (null accg)
           ;; this should no longer happen because cln-accg no
           ;; longer returns nil if there are empty ccmfs.
           (pprogn
            (increment-timer 'other-time state)
            (ccg-io? size-change nil state
                     ()
                     (fms "A trivial analysis has revealed that this SCC is ~
                           potentially non-terminating. We will set it aside ~
                           for further refinement.~|"
                          nil *standard-co* state nil))
            (increment-timer 'print-time state)
            (accg-sct-list1 (cdr lst) (1+ i) n proved (cons (car lst) unproved)
                            (cons nil ces) state))
         (er-let*
          ((ce (sct (accg-ccmfs accg) (array-dimension accg 0) state)))
          (if (null ce)
              (pprogn
               (increment-timer 'other-time state)
               (ccg-io? size-change nil state
                        ()
                        (fms "We have shown this SCC to be terminating, so we ~
                              do not need to refine it any further.~|"
                             nil *standard-co* state nil))
               (increment-timer 'print-time state)
               (accg-sct-list1 (cdr lst)
                               (1+ i)
                               n
                               (cons accg proved)
                               unproved
                               ces
                               state))
            (pprogn
             (increment-timer 'other-time state)
             (ccg-io? size-change nil state
                      ()
                      (fms "This SCC is potentially non-terminating. We will ~
                            set it aside for further refinement.~|"
                           nil *standard-co* state nil))
             (increment-timer 'print-time state)
             (accg-sct-list1 (cdr lst)
                             (1+ i)
                             n
                             proved
                             (cons (car lst) unproved)
                             (cons ce ces)
                             state)))))))))

(defun-raw accg-sct-list (lst proved unproved ces state)
  (accg-sct-list1 lst 1 (len lst) proved unproved ces state))

(defun ccg-counter-example-fn-name1 (char-lst pkg i wrld)
  (declare (xargs :guard (and (standard-char-listp char-lst)
                              (stringp pkg)
                              (natp i)
                              (plist-worldp wrld))))
  (let ((name (fix-intern$
               (coerce (append char-lst
                               `(#\_)
                               (explode-nonnegative-integer i 10 nil))
                       'string)
               pkg)))
    (cond ((new-namep name wrld) (mv name i))
          (t (ccg-counter-example-fn-name1 char-lst pkg (1+ i) wrld)))))

(defun ccg-counter-example-fn-name (root i wrld)
  (declare (xargs :guard (and (symbolp root)
                              (plist-worldp wrld)
                              (natp i))))
  (ccg-counter-example-fn-name1 (coerce (symbol-name root) 'list)
                                (symbol-package-name root)
                                i
                                wrld))

(defun assoc-set-eq (key value alist)
  (declare (xargs :guard (and (symbolp key)
                              (alistp alist))))
  (cond ((endp alist)
         (acons key value alist))
        ((eq key (caar alist))
         (acons key value (cdr alist)))
        (t
         (assoc-set-eq key value (cdr alist)))))

(defun assoc-eq-value (key default alist)
  (declare (xargs :guard (and (symbolp key)
                              (alistp alist))))
  (let ((pair (assoc-eq key alist)))
    (if (consp pair)
        (cdr pair)
      default)))

(defun-raw aref-lst (array lst)
  (mapcar #'(lambda (x) (aref array x)) lst))

(defun-raw alist-add-eq (alist key val)
  ;; given an alist whose values are lists, returns the alist
  ;; resulting from adding val to the list that is the value
  ;; corresponding to the key key.
  (cond ((endp alist)
         (acons key (list val) nil))
        ((eq (caar alist) key)
         (acons key (cons val (cdar alist)) (cdr alist)))
        (t
         (cons (car alist) (alist-add-eq (cdr alist) key val)))))

(defun-raw order-names-arglists (names arglists rv-alist)
  ;; when determining the minimal set of formals necessary to prove
  ;; termination, we do a simple search of all the subsets of
  ;; variables. to speed this up, we create a list indicating the
  ;; order that we add the variables. this list is ordered by number
  ;; of formals first, formal order second, and by function last. so,
  ;; if we have function f with formals (x y) and function g with
  ;; formals (a b), then the order would be ((f x) (g a) (f y) (g
  ;; b)). So, the sets we would try, in the order we try them, are as
  ;; follows:
  ;;
  ;; 1. {(f x)}
  ;; 2. {(g a)}
  ;; 3. {(f y)}
  ;; 4. {(g b)}
  ;; 5. {(f x) (g a)}
  ;; 6. {(f x) (f y)}
  ;; 7. {(f x) (g b)}
  ;; 8. {(g a) (f y)}
  ;; 9. {(g a) (g b)}
  ;; 10. {(f y) (g b)}
  ;; 11. {(f x) (g a) (f y)}
  ;; 12. {(f x) (g a) (g b)}
  ;; 13. {(f x) (f y) (g b)}
  ;; 14. {(g a) (f y) (g b)}
  ;; 15. {(f x) (g a) (f y) (g b)}
  ;;
  ;; the idea is that most functions require only a small subset of
  ;; the actuals to prove termination.

  (let* ((na-arrays (coerce (mapcar (lambda (x y) (coerce (cons x y) 'vector))
                                    names arglists)
                            'vector))
         (maxsize (loop for v across na-arrays maximize (array-dimension v 0))))
    (loop for i from 1 below maxsize
          append (loop for array across na-arrays
                       when (and (< i (array-dimension array 0))
                                 (not (member-eq (aref array i)
                                                 (cdr (assoc (aref array 0) rv-alist)))))
                         collect (cons (aref array 0)
                                       (aref array i))))))

(defmacro-raw ccmf-tail-fn (ccmf contexts)
  `(context-fn (aref ,contexts
                     (car (ccmf-fc-num ,ccmf)))))

(defmacro-raw ccmf-head-fn (ccmf contexts)
  `(context-fn (aref ,contexts
                     (car (ccmf-lc-num ,ccmf)))))

(defun-raw restrict-ccmf (ccmf ccmr1 ccmr2)
  ;; the dual to ccmf-remove-ccms, in that it only retains the ccms
  ;; indicated by ccmr1 and ccmr2, but is not destructive.
  (let* ((graph (ccmf-graph ccmf))
         (n (array-dimension graph 0))
         (ngraph (make-array n
                             :element-type 'ccmf-node
                             :initial-element (make-ccmf-node)))
         (nccmf (make-ccmf :firstsite (ccmf-firstsite ccmf)
                           :lastsite (ccmf-lastsite ccmf)
                           :fc-num (ccmf-fc-num ccmf)
                           :lc-num (ccmf-lc-num ccmf)
                           :in-sizes (ccmf-in-sizes ccmf)
                           :out-sizes (ccmf-out-sizes ccmf)
                           :graph ngraph))
         (f (lambda (x) (aref ccmr2 x))))
    (loop for i from 0 below n
          for node = (aref graph i)
          if (aref ccmr1 i)
            do (setf (aref ngraph i)
                     (make-ccmf-node
                      :>-edges (remove-if-not f (ccmf-node->-edges node))
                      :>=-edges (remove-if-not f (ccmf-node->=-edges node))))
          else
            do (setf (aref ngraph i) (make-ccmf-node)))
    (loop for node across ngraph
          when (or (consp (ccmf-node->-edges node))
                   (consp (ccmf-node->=-edges node)))
            return nccmf
          finally (return nil))))

(defun-raw can-solve-restricted-accgs? (accgs ccmrs scp? state)
  ;; this is the workhorse of our controller-alist search. given ccm
  ;; restrictions (see create-ccm-restrictions), ccmrs, and a flag to
  ;; indicate whether the original accg was solved using scp or sct,
  ;; we restrict the accg and attempt to reprove termination.
  (loop for accg in accgs
        for n = (array-dimension accg 0)
        for naccg = (make-array n)
        ;; first, initiate the naccg nodes
        do (loop for i from 0 below n
                 for node = (aref accg i)
                 do (setf (aref naccg i)
                          (make-accg-node
                           :context (accg-node-context node)
                           :num i)))
        ;; next, set the ccmfs for those nodes to be the restricted
        ;; version of the ccmfs of the original accg node.
        do (loop
            for i from 0 below n
            for node = (aref accg i)
            for nnode1 = (aref naccg i)
            for ccmr1 = (aref ccmrs (car (accg-node-context-num node)))
            do (loop
                for edge in (accg-node-fwd-edges node)
                for ccmf = (accg-edge-ccmf edge)
                for ccmr2 = (aref ccmrs (accg-edge-head edge))
                for nnode2 = (aref naccg (accg-edge-head edge))
                for nccmf = (restrict-ccmf ccmf ccmr1 ccmr2)
                if nccmf
                  do (let ((nedge (make-accg-edge :head (accg-edge-head edge)
                                                  :tail (accg-edge-tail edge)
                                                  :ccmf nccmf)))
                       (setf (accg-node-fwd-edges nnode1)
                             (cons nedge (accg-node-fwd-edges nnode1)))
                       (setf (accg-node-bwd-edges nnode2)
                             (cons nedge (accg-node-bwd-edges nnode2))))
                else do (return-from can-solve-restricted-accgs? (value nil))))
        ;; finally, run scp or sct as indicated. if we fail, then we
        ;; immediately return nil.
         do (if scp?
                (unless (scp (cln-accg naccg)) (return (value nil)))
              (er-let*
               ((caccg (value (cln-accg naccg)))
                (ce (if (null caccg)
                        (value t)
                      (sct (accg-ccmfs caccg) n state))))
               (unless (null ce) (return (value nil)))))
        finally (return (value t))))

(defun-raw create-ccm-restrictions (contexts av-alist)
  ;; creates "ccm restrictions", which is an array of boolean arrays
  ;; such that element i j is t iff we want to keep ccm j from context
  ;; i. which ccms to keep is determined by av-alist, which tells us
  ;; which variables from each function we are using for the current
  ;; restriction.
  (loop with n = (array-dimension contexts 0)
        with ccmrs = (make-array n)
        for i from 0 below n
        for context = (aref contexts i)
        for ccms = (context-ccms context)
        ;; vars are the variables we are allowed to use for this context.
        for vars = (cdr (assoc (context-fn context) av-alist))
        for m = (array-dimension ccms 0)
        for ccmri = (make-array m
                                :element-type 'boolean
                                :initial-element nil)
        do (setf (aref ccmrs i) ccmri)
        do (loop for j from 0 below m
                 do (setf (aref ccmri j)
                          (subsetp (all-vars (aref ccms j))
                                   vars)))
        finally (return ccmrs)))

(defun-raw ruler-vars (names contexts)
  ;; returns an alist mapping fucntion names to the variables used in
  ;; the rulers of the contexts of that function.
  (loop with rv-alist = (pairlis$ names nil)
        for context across contexts
        for fn = (context-fn context)
        for vars = (all-vars1-lst (context-ruler context) nil)
        for pair = (assoc fn rv-alist)
        do (setf (cdr pair) (union-eq vars (cdr pair)))
        finally (return rv-alist)))

(defun-raw cgma-aux (nalist proved-scp proved-sct contexts av-alist i state)
  ;; helper function for ccg-generate-measure-alist. nalist is the
  ;; list of function-formal pairs as generated by
  ;; order-names-arglists. proved-scp is a list of accgs proved
  ;; terminating by the scp algorithm, and proved-sct is a list of
  ;; accgs proved terminating by the sct algorithm. contexts is the
  ;; array of contexts. av-alist is an alist mapping each function
  ;; name to the formals that we want enabled, and i is the number of
  ;; formals we want to enable. returns the first av-alist
  ;; for which we can prove termination, or nil if we cannot
  ;; prove termination.
  (cond ((zp i) ;; if we don't want to add any more variables, try to
                ;; prove termination of the restricted accgs.
         (let ((ccmrs (create-ccm-restrictions contexts av-alist)))
           (er-let*
            ((p1 (can-solve-restricted-accgs? proved-scp ccmrs t state))
             (p2 (if p1
                     (can-solve-restricted-accgs? proved-sct ccmrs nil state)
                   (value nil))))
            (if p2
                (value av-alist)
              (value nil)))))
        ((endp nalist) ;; if we reach the end of the list before i
                       ;; reaches 0, just return nil.
         (value nil))
        (t ;; otherwise, we proceed in two different ways:
         (er-let*
          ;; first, we enable the first formal in nalist and
          ;; proceed to enable i-1 of the rest of the formals.
          ((nav-alist (cgma-aux (cdr nalist) proved-scp proved-sct contexts
                                (alist-add-eq av-alist
                                              (caar nalist)
                                              (cdar nalist))
                                (1- i)
                                state)))
          ;; if we were successful, report our success.
          (if nav-alist
              (value nav-alist)
            ;; otherwise, try leaving the current variable out
            ;; and enable i of the remaining variables.
            (cgma-aux (cdr nalist) proved-scp proved-sct
                      contexts av-alist i state))))))

(defun-raw ccg-generate-measure-alist1 (i nalist proved-scp proved-sct
                                          contexts rv-alist state)
  (er-let* ((av-alist (cgma-aux nalist proved-scp proved-sct
                                contexts rv-alist i state)))
           (if av-alist
               (value (mapcar (lambda (x) (cons (car x) (cons :? (cdr x))))
                              av-alist))
             (ccg-generate-measure-alist1 (1+ i) nalist
                                          proved-scp proved-sct
                                          contexts rv-alist state))))

(defun-raw ccg-generate-measure-alist (proved-scp proved-sct names arglists
                                                  contexts cpn state)
  ;; generates a measure-alist designed to minimize the resulting
  ;; controller-alist. we return the restricted set of the ccms
  ;; necessary for proving termination with :CCG consed onto the
  ;; front. the result is a "pseudo-measure" from which ACL2 can
  ;; compute a safe controller alist. proved-scp and proved-sct are
  ;; the accgs proved terminating using the scp or sct algorithm,
  ;; respectively. names is the list of names of the functions, and
  ;; arglists is the list of the arglists for each function. contexts
  ;; is the array of contexts. cpn tells us whether or not we proved
  ;; termination constructing contexts by node rather than by
  ;; edge. This is important because, in order to construct a sound
  ;; controller-alist we need to include all the variables in the
  ;; context rulers if we could not prove termination using per-node
  ;; contexts.

  ;; first, we construct an alist of the initially enabled formals
  ;; based on cpn, and use it to make an ordered list of name-formal
  ;; pairs.

  (let* ((rv-alist (if cpn (pairlis$ names nil) (ruler-vars names contexts)))
         (nalist (order-names-arglists names arglists rv-alist)))
    (ccg-generate-measure-alist1 0 nalist proved-scp proved-sct
                                             contexts rv-alist state)))


;;;;; ALL TERMINATION ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-raw name-var-pairs1 (name arglist rst)
  ;; name: the name of a function
  ;; arglist: the arglist of the function whose name is name
  ;; rst: the list to which to append the result
  ;;
  ;; OUTPUT: ((name . x) | x in arglist) appended to rst.

  (if (endp arglist)
      rst
    (acons name (car arglist)
           (name-var-pairs1 name (cdr arglist) rst))))

(defun-raw name-var-pairs (functs rv-alist)
  ;; functs: a list of structs of type funct.
  ;; rv-alist: an alist mapping the names of the functions in functs
  ;; to subsets of their formals. The idea is that these are
  ;; restricted variables. That is, in the measured-subset analysis,
  ;; all subsets must be supersets of the variables specified in
  ;; rv-alist.
  ;;
  ;; OUTPUT: two lists of the form ((fn . x) ...) where fn is the name
  ;; of a function in funct and x is a formal of that function. The
  ;; first list is of these pairs that we may consider removing from
  ;; the measured subset, and the second is a list of these pairs that
  ;; we may *not* consider removing from the measured subset (as
  ;; specified by rv-alist).
  (if (endp functs)
      (mv nil nil)
    (mv-let
     (free fixed)
     (name-var-pairs (cdr functs) rv-alist)
     (let* ((funct (car functs))
            (fn (funct-fn funct))
            (rv (cdr (assoc fn rv-alist))))
       (mv (name-var-pairs1 fn
                            (set-difference-eq (funct-formals funct) rv)
                            free)
           (name-var-pairs1 fn rv fixed))))))

(defun-raw get-ccm-vars1 (i ccms ccm-vars)
  ;; i: integer such that 0 <= i < |ccms|.
  ;; ccms: an array of calling context measures.
  ;; ccm-vars: accumulator array such that ccm-vars[j] contains a list
  ;; of all the variables in the expression ccms[j].
  ;;
  ;; OUTPUT: completed ccm-vars.
  (cond ((< i 0)
         ccm-vars)
        (t
         (setf (aref ccm-vars i)
               (all-vars (aref ccms i)))
         (get-ccm-vars1 (1- i) ccms ccm-vars))))

(defun-raw get-ccm-vars (ccms)
  ;; ccms: an array of ccms.
  ;;
  ;; OUTPUT: an array, ccm-vars, such that ccm-vars[i] contains the
  ;; list of variables in expression ccms[i] for all 0 <= i < |ccms|
  (let ((len (array-dimension ccms 0)))
    (get-ccm-vars1 (1- len) ccms (make-array len
                                             :element-type 'list
                                             :initial-element nil))))

(defun-raw fn-ccm-vars-alist (functs)
  (if (endp functs)
      nil
    (let ((funct (car functs)))
      (acons (funct-fn funct) (get-ccm-vars (funct-ccms funct))
             (fn-ccm-vars-alist (cdr functs))))))

(defun-raw gather-relevant-ccms1 (i var ccm-vars indices)
  ;; i: an integer such that 0 <= i < |ccm-vars|. Should initially be |ccm-vars|-1.
  ;; ccm-vars: an array of lists of integers.
  ;; var: a variable
  ;; indices: the accumulator; it is { k | i < k < |ccm-vars|
  ;;   s.t. ccm-vars[k] contains var }. Should initially be nil.
  ;;
  ;; OUTPUT: { k | 0 <= k < |ccm-vars| s.t. ccm-vars[k] contains var }
  (if (< i 0)
      indices
    (gather-relevant-ccms1 (1- i) var ccm-vars
                           (if (member-eq var (aref ccm-vars i))
                               (cons i indices)
                             indices))))

(defun-raw gather-relevant-ccms (var ccm-vars)
  ;; ccm-vars: an array of lists of variables
  ;; var: a variable
  ;;
  ;; OUTPUT: the list of the indices of the slots of ccm-vars that
  ;; contain var.
  (gather-relevant-ccms1 (1- (array-dimension ccm-vars 0)) var ccm-vars nil))

(defun-raw gather-all-relevant-ccms1 (avars alist)
  ;; functs: a list of structures of type funct
  ;;
  ;; OUTPUT: a mapping of sorts from formals to the ccms containing
  ;; those formals. See the note on the output of
  ;; gather-all-relevant-ccms-for-funct.
  (if (endp avars)
      nil
    (let* ((avar (car avars))
           (fn (car avar))
           (var (cdr avar)))
    (cons (gather-relevant-ccms var (cdr (assoc fn alist)))
          (gather-all-relevant-ccms1 (cdr avars) alist)))))

(defun-raw gather-all-relevant-ccms (avars functs)
  (gather-all-relevant-ccms1 avars (fn-ccm-vars-alist functs)))

(defun set-difference-and-intersection (set1 set2)
  (declare (xargs :guard (and (eqlable-listp set1)
                              (eqlable-listp set2))))
  ;; set1: an eqlable-listp.
  ;; set2: an eqlable-listp
  ;;
  ;; OUTPUT: two lists. The first is the difference of set1 and set2,
  ;; and the second is the intersection of set1 and set2.
  (if (endp set1)
      (mv nil nil)
    (mv-let (difference intersection)
            (set-difference-and-intersection (cdr set1) set2)
            (if (member (car set1) set2)
                (mv difference (cons (car set1) intersection))
              (mv (cons (car set1) difference) intersection)))))

(defun-raw ccmf-remove-relevant-edges1 (i graph relevant-ccms1 relevant-ccms2
                                          edges-alist)
  ;; i: integer such that 0 <= i < |graph|.
  ;; graph: a ccmf-graph.
  ;; relevant-ccms1: an increasing list of integers, j, such that 0 <=
  ;; j < |graph|. These are the ccms we are to virtually remove from
  ;; the graph by removing all its outgoing edges.
  ;; ASSUMPTION: relevant-ccms1 is in increasing order.
  ;; relevant-ccms2: a list of natural numbers. These are the ccms we
  ;; are to virtually remove from the target context of the graph by
  ;; removing all of its incoming edges.
  ;; edges-alist: the accumulator alist that maps each 0 <= j <
  ;; |graph| to a cons of the >-edges and >=-edges removed from the
  ;; graph, so we can put them back later.
  ;;
  ;; SIDE EFFECT: all edges to and from relevant ccms in the graph are
  ;; removed.
  ;;
  ;; OUTPUT: the completed edges-alist.

  (cond ((<= (array-dimension graph 0) i)
         edges-alist)
        ((and (consp relevant-ccms1)
              (= i (car relevant-ccms1)))
         ;; if i is a member of relevant-ccms1, it is the first
         ;; element because of our assumption that relevant-ccms1 is
         ;; increasing. In this case we remove all the outgoing edges
         ;; from graph[i].
         (let* ((node (aref graph i))
                (>-edges-i (ccmf-node->-edges node)) ;;get the >-edges
                (>=-edges-i (ccmf-node->=-edges node))) ;; get the >=-edges
           (setf (ccmf-node->-edges node) nil) ;; set the >-edges to nil
           (setf (ccmf-node->=-edges node) nil) ;; set the >=-edges to nil
           (ccmf-remove-relevant-edges1 (1+ i) graph
                                        (cdr relevant-ccms1) relevant-ccms2
                                        ;; add the removed edges (if
                                        ;; any) to the accumulator:
                                        (if (and (endp >-edges-i) (endp >=-edges-i))
                                            edges-alist
                                          (acons i (cons >-edges-i >=-edges-i)
                                                 edges-alist)))))
        ((consp relevant-ccms2)
         ;; if a non-nil relevant-ccms2 was supplied, we remove all
         ;; the edges pointing from graph[i] to ccms specified by
         ;; relevant-ccms2.
         (let* ((node (aref graph i))
                (>-edges-i (ccmf-node->-edges node))
                (>=-edges-i (ccmf-node->=-edges node)))
           (mv-let (>-diff >-intersect)
                   (set-difference-and-intersection >-edges-i relevant-ccms2)
                   (mv-let (>=-diff >=-intersect)
                           (set-difference-and-intersection >=-edges-i relevant-ccms2)
                           (progn
                             ;; if we removed any edges, set the new
                             ;; edge lists.
                             (when (consp >-intersect)
                               (setf (ccmf-node->-edges node) >-diff))
                             (when (consp >=-intersect)
                               (setf (ccmf-node->=-edges node) >=-diff))
                             (ccmf-remove-relevant-edges1
                              (1+ i) graph
                              relevant-ccms1 relevant-ccms2
                              ;; add the removed edges (if any) to the accumulator.
                              (if (and (endp >-intersect) (endp >=-intersect))
                                  edges-alist
                                (acons i (cons >-intersect >=-intersect)
                                       edges-alist))))))))
        (t
         ;; if the current index is not in relevant-ccms1 and
         ;; relevant-ccms2 is empty, there is nothing to do, so we
         ;; move on to the next index.
         (ccmf-remove-relevant-edges1 (1+ i)
                                      graph
                                      relevant-ccms1
                                      relevant-ccms2
                                      edges-alist))))

(defun-raw ccmf-remove-relevant-edges (ccmf relevant-ccms1 relevant-ccms2)
  ;; ccmf: a struct of type ccmf.
  ;; relevant-ccms1: an increasing list of integers, j, such that 0 <=
  ;; j < |graph|. These are the ccms we are to virtually remove from
  ;; the graph by removing all its outgoing edges.
  ;; ASSUMPTION: relevant-ccms1 is in increasing order.
  ;; relevant-ccms2: a list of natural numbers. These are the ccms we
  ;; are to virtually remove from the target context of the graph by
  ;; removing all of its incoming edges.
  ;;
  ;; SIDE EFFECT: all edges to and from relevant ccms in the ccmf are
  ;; removed.
  ;;
  ;; OUTPUT: the ccmf consed to an alist that maps each 0 <= j <
  ;; |graph| to a cons of the >-edges and >=-edges removed from the
  ;; graph, so we can put them back later.

  (let ((graph (ccmf-graph ccmf)))
    (cons ccmf
          (ccmf-remove-relevant-edges1 0
                                       graph
                                       relevant-ccms1 relevant-ccms2
                                       nil))))

(defun-raw ccmf-remove-relevant-edges-lst (ccmfs contexts fn relevant-ccms acc)
  ;; ccmfs: a list of structs of type ccmf which should be the ccmfs for fn.
  ;; contexts: an array of contexts.
  ;; fn: a function name
  ;; relevant-ccms: a list of indices of the ccms of fn. Indicates
  ;; which ccms to remove.
  ;; acc: the accumulator. This accumulates the removed edge
  ;; information so we can restore the ccmfs when we are done.
  ;;
  ;; SIDE EFFECT: all edges to and from relevant ccms in the ccmfs of
  ;; are removed.
  ;;
  ;; OUTPUT: the completed accumulator. It is an alist mapping the
  ;; ccmfs to an alist mapping the indicices of the source ccms of the
  ;; ccmf to a cons of the >-edges and >=-edges that were removed.

  (if (endp ccmfs)
      acc
    (let* ((ccmf (car ccmfs))
           (tcontext (aref contexts (car (ccmf-fc-num ccmf))))
           (relevant-ccms1 (if (eq (context-fn tcontext) fn) relevant-ccms nil))
           (hcontext (aref contexts (car (ccmf-lc-num ccmf))))
           (relevant-ccms2 (if (eq (context-fn hcontext) fn) relevant-ccms nil)))
      (ccmf-remove-relevant-edges-lst
       (cdr ccmfs)
       contexts
       fn
       relevant-ccms
       (cons (ccmf-remove-relevant-edges ccmf relevant-ccms1 relevant-ccms2)
             acc)))))

(defun-raw accg-remove-relevant-ccmf-edges1 (i accg contexts fn relevant-ccms acc)
  ;; i: natural number such that 0 <= i < |accg|.
  ;; accg: an array of structs of type accg-node.
  ;; contexts: an array of contexts.
  ;; fn: a function name.
  ;; relevant-ccms: the ccms to remove from all ccmfs corresponding to fn.
  ;; acc: the accumulator.
  ;;
  ;; SIDE EFFECT: all edges to and from relevant ccms in the ccmfs of
  ;; the accg are removed.
  ;;
  ;; OUTPUT: an alist mapping the ccmfs to an alist mapping the
  ;; indicices of the source ccms of the ccmf to a cons of the >-edges
  ;; and >=-edges that were removed.
  (if (< i 0)
      acc
    (let* ((node (aref accg i)))
      (accg-remove-relevant-ccmf-edges1
       (1- i)
       accg
       contexts
       fn
       relevant-ccms
       (if (eq (accg-node-fn node) fn)
           (let ((pred (lambda (edge)
                         (equal (accg-node-fn (aref accg (accg-edge-tail edge)))
                                fn))))
             (ccmf-remove-relevant-edges-lst
              (append (mapcar #'accg-edge-ccmf
                              (accg-node-fwd-edges node))
                      ;; remove all edges from contexts of fn to avoid
                      ;; redundant work.
                      (mapcar #'accg-edge-ccmf
                              (remove-if pred
                                         (accg-node-bwd-edges node))))
              contexts
              fn
              relevant-ccms
              acc))
         acc)))))

(defun-raw accg-remove-relevant-ccmf-edges (accg contexts fn relevant-ccms)

  ;; accg: an array of structs of type accg-node.
  ;; contexts: an array of contexts.
  ;; fn: a function name.
  ;; relevant-ccms: the ccms to remove from all ccmfs corresponding to fn.
  ;;
  ;; SIDE EFFECT: all edges to and from relevant ccms in the ccmfs of
  ;; the accg are removed.
  ;;
  ;; OUTPUT: an alist mapping the ccmfs to an alist mapping the
  ;; indicices of the source ccms of the ccmf to a cons of the >-edges
  ;; and >=-edges that were removed.

  (accg-remove-relevant-ccmf-edges1 (1- (array-dimension accg 0))
                                    accg
                                    contexts
                                    fn
                                    relevant-ccms
                                    nil))

(defun-raw accg-remove-relevant-ccmf-edges-lst-tail (accgs contexts fn relevant-ccms acc)
  ;; tail recursive implementation of accg-remove-relevant-ccmf-edges-lst

  (if (endp accgs)
      acc
    (accg-remove-relevant-ccmf-edges-lst-tail
     (cdr accgs)
     contexts
     fn
     relevant-ccms
     (accg-remove-relevant-ccmf-edges1
      (1- (array-dimension (car accgs) 0))
      (car accgs)
      contexts
      fn
      relevant-ccms
      acc))))

(defun-raw accg-remove-relevant-ccmf-edges-lst (accgs contexts fn relevant-ccms)
  ;; accgs: a list of accgs.
  ;; contexts: an array of contexts
  ;; fn: function name
  ;; relevant-ccms: the ccms of fn to "remove" (ccms are kept, but all
  ;; incoming and outgoing edges are removed).
  ;;
  ;; SIDE-EFFECT: all the incoming and outgoing edges of the indicated
  ;; ccms of fn in the ccmfs of the accgs are removed.
  ;;
  ;; OUTPUT: an alist mapping the ccmfs to an alist mapping the
  ;; indicices of the source ccms of the ccmf to a cons of the >-edges
  ;; and >=-edges that were removed.
  (accg-remove-relevant-ccmf-edges-lst-tail accgs contexts fn relevant-ccms nil))

(defun-raw restore-edges1 (ccmf alist)
  ;; ccmf: a struct of type ccmf.
  ;; alist: maps indices of the ccmf to the cons of the >-edges and
  ;; >=-edges that should be added back to the ccmf.
  ;;
  ;; SIDE-EFFECT: the edges indicated by the alist are added back to the ccmf.
  ;;
  ;; OUTPUT: nil.
  (if (endp alist)
      nil
    (let* ((entry (car alist))
           (i (car entry))
           (>-edges (cadr entry))
           (>=-edges (cddr entry))
           (node (aref (ccmf-graph ccmf) i)))
      (setf (ccmf-node->-edges node)
            (merge 'list
                   >-edges
                   (ccmf-node->-edges node)
                   #'<))
      (setf (ccmf-node->=-edges node)
            (merge 'list
                   >=-edges
                   (ccmf-node->=-edges node)
                   #'<))
      (restore-edges1 ccmf (cdr alist)))))

(defun-raw restore-edges (alist)
  ;; alist: maps ccmfs to alists mapping indices of the ccmf to the
  ;; cons of the >-edges and >=-edges that should be added back to the
  ;; ccmf.
  ;;
  ;; SIDE-EFFECT: the edges indicated by the alist are added back to
  ;; their respective ccmfs.
  ;;
  ;; OUTPUT: nil.

  (if (endp alist)
      nil
    (progn
      (restore-edges1 (caar alist) (cdar alist))
      (restore-edges (cdr alist)))))

(defun-raw can-scp-lstp (accgs)
  ;; accgs: a list of accgs.
  ;;
  ;; OUTPUT: returns non-nil iff scp succeeds for all the accgs.
  (or (endp accgs)
      (and (scp (cln-accg (copy-accg (car accgs))))
           (can-scp-lstp (cdr accgs)))))

(defun-raw can-sct-lstp (accgs state)
  ;; accgs: a list of accgs
  ;; state: the state
  ;;
  ;; OUTPUT: returns non-nil iff sct succeeds for the ccmfs of all the accgs.
  (if (endp accgs)
      (value t)
    (let ((naccg (cln-accg (copy-accg (car accgs)))))
      (if (null naccg)
          (value nil)
        (er-let*
         ((ce (sct (accg-ccmfs naccg)
                   (array-dimension naccg 0)
                   state)))
         (if (null ce)
             (can-sct-lstp (cdr accgs) state)
           (value nil)))))))

(defun remove-covered-subsets-tail (avar subsets acc)
  ;;tail recursive implementation of remove-covered-subsets
  (cond ((endp subsets) acc)
        ((equal avar (caar subsets))
         (remove-covered-subsets-tail avar (cdr subsets) acc))
        (t
         (remove-covered-subsets-tail avar
                                      (cdr subsets)
                                      (cons (car subsets) acc)))))

(defun remove-covered-subsets (avar subsets)
  ;; avar: an element.
  ;; subsets: a list of lists.
  ;;
  ;; OUTPUT: the subset of subsets which do not have avar as its first element.
  (remove-covered-subsets-tail avar subsets nil))

(defun remove-avar-from-subsets-tail (avar subsets acc)
  ;; a tail-recursive implementation of remove-avar-from-subsets.
  (if (endp subsets)
      acc
    (remove-avar-from-subsets-tail avar (cdr subsets)
                                   (cons (if (equal avar (caar subsets))
                                             (cdar subsets)
                                           (car subsets))
                                         acc))))

(defun remove-avar-from-subsets (avar subsets)
  ;; avar: an element
  ;; subsets: a list of lists
  ;;
  ;; OUTPUT: the result of removing avar from all the lists in subsets
  ;; for which avar is the first element.
  (remove-avar-from-subsets-tail avar subsets nil))

(defun add-avar-to-subsets-tail (avar subsets acc)
  ;; a tail-recursive implementation of add-avar-to-subsets.
  (if (endp subsets)
      acc
    (add-avar-to-subsets-tail avar (cdr subsets)
                              (acons avar (car subsets) acc))))

(defun add-avar-to-subsets (avar subsets)
  ;; avar: an element.
  ;; subsets: a list of lists.
  ;;
  ;; OUTPUT: the result of consing avar to every element of subsets.
  (add-avar-to-subsets-tail avar subsets nil))

(defun-raw all-termination1 (proved-scp proved-sct contexts avars
                                        relevant-edges subsets state)
  ;; proved-scp: a list of accgs for which scp succeeds.
  ;; proved-sct: a list of accgs for which sct succeeds.
  ;; contexts: an array of contexts.
  ;; avars: a list of pairs of the form (fn. x) where fn is a function
  ;; name, and x is a formal of that function.
  ;; relevant-edges: a list of lists of indices such that the ith
  ;; element of avars appears exactly in the ccms of the corresponding
  ;; function indicated by the indices of the ith member of relevant-edges.

  ;; subsets: a list of lists of the elements of avars. This helps us
  ;; avoid finding supersets of already discovered measured-subsets by
  ;; telling us what subsets to avoid (because they would result in a
  ;; superset of an already calculated measured-subset).
  ;;
  ;; OUTPUT: a list of lists of the elements of avars coresponding to
  ;; minimal variables needed to still successfully run scp on the
  ;; elements of proved-scp and run sct on the elements of proved-sct.
  (cond ((member-equal '() subsets)
         ;; if '() is in subsets, that means that we have recreated an
         ;; already calculated measured-subset, so we stop and return
         (value '()))
        ((endp avars)
         ;; since we prune as we go, we know that if we make it to the
         ;; end of the avars, we have a solution. So, we return the
         ;; set containing the empty set, which will be populated on
         ;; our way back up the search tree.
         (value '(())))
        (t
         (let* ((avar (car avars)) ;; take the first avar.
                (fn (car avar))   ;; the formal name

                ;; we begin by removing all the ccm edges that are
                ;; relevant to var from all the accgs in both
                ;; proved-sct and proved scp.

                (re-info (accg-remove-relevant-ccmf-edges-lst-tail
                          proved-sct
                          contexts
                          fn
                          (car relevant-edges)
                          (accg-remove-relevant-ccmf-edges-lst
                           proved-scp
                           contexts
                           fn
                           (car relevant-edges)))))

           ;; if we can still prove termination without var, we
           ;; continue our search down the subtree in which var
           ;; is disabled. otherwise, we set nsubsets to be the
           ;; empty set.
           (er-let*
            ((p (can-sct-lstp proved-sct state))
             (nsubsets (if (and p
                                (can-scp-lstp proved-scp))
                           (all-termination1 proved-scp proved-sct
                                             contexts
                                             (cdr avars) (cdr relevant-edges)
                                             (remove-covered-subsets avar subsets)
                                             state)
                         (value '()))))
            (progn
              ;; next we restore the edges we removed.
              (restore-edges re-info)
              ;; finally, we search the branch of the search tree in
              ;; which var is enabled.
              (er-let*
               ((nnsubsets (all-termination1
                            proved-scp proved-sct
                            contexts
                            (cdr avars) (cdr relevant-edges)
                            (append nsubsets
                                    (remove-avar-from-subsets avar subsets))
                            state)))
               ;; our solution is all the minimal measured subsets we
               ;; discovered with var disabled along with var added to
               ;; all the minimal measured subsets we discovered with
               ;; var enabled.
               (value (append nsubsets
                              (add-avar-to-subsets avar nnsubsets))))))))))

(defun-raw funct-fns-lst (functs)
  ;; given a list of functs, returns a corresponding list of all their funct-fns.
  (if (endp functs)
      nil
    (cons (funct-fn (car functs)) (cdr functs))))

(defun append-to-all (list list-of-lists)
  (if (endp list-of-lists)
      nil
    (cons (append list (car list-of-lists))
          (append-to-all list (cdr list-of-lists)))))

(defun-raw all-termination (proved-scp proved-sct contexts functs cpn state)
  ;; proved-scp: a list of accgs for which scp succeeds.
  ;; proved-sct: a list of accgs for which sct succeeds.
  ;; contexts: an array of contexts.
  ;; functs: a list of structures of type funct.
  ;; cpn: a boolean telling us if we proved termination using ccmfs
  ;; per node (as opposed to per edge).
  ;;
  ;; OUTPUT: the minimal measured subsets of functs using the accgs
  ;; that were used to prove termination.

  ;; we need this strange case in the beginning.
  (if (and (endp proved-scp)
           (endp proved-sct))
      (value '(()))

    (let ((names (funct-fns-lst functs)))
      (mv-let
       (free fixed)
       ;; if we proved termination with ccmfs per node, then by
       ;; Vroon's dissertation, there is a measure involving only
       ;; those variables that are needed to show termination in
       ;; proved-scp and proved-sct. That is, all variables are
       ;; candidates for removal from the measured-subset. If we
       ;; used ccmfs per edge, then the dissertation tells us
       ;; that we need to keep all variables that appear in the
       ;; ruler. So these are off-limits for removal from the
       ;; measured subset.
       (name-var-pairs functs
                       (if cpn
                           (pairlis$ names nil)
                         (ruler-vars names contexts)))
       ;; we append all the required variables to the calculated
       ;; measured subset.
       (let ((relevant-ccms (gather-all-relevant-ccms free functs)))
         (er-let* ((at1 (all-termination1 proved-scp proved-sct
                                          contexts free relevant-ccms nil state)))
                  (value (append-to-all fixed at1))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ACL2 integration                       ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-ccms1 (m edcls key ctx state)

  ;; this function is based on get-measures1 in the ACL2 sources.

  ;; A typical edcls is given above, in the comment for get-guards.  Note
  ;; that the :CCMs entry is found in an XARGS declaration.  By the check
  ;; in chk-dcl-lst we know there is at most one :CCMs entry in each XARGS
  ;; declaration.  But there may be more than one declaration.  If more than
  ;; one measure is specified by this edcls, we'll cause an error.  Otherwise,
  ;; we return the measure or the term *0*, which is taken as a signal that
  ;; no measure was specified.

  ;; Our first argument, m, is the list of ccms term found so far, or
  ;; *0* if none has been found.  We map down edcls and ensure that
  ;; each XARGS either says nothing about :CCMs or specifies m.

  (cond ((null edcls) (value m))
        ((eq (caar edcls) 'xargs)
         (let ((temp (assoc-keyword key (cdar edcls))))
           (cond ((null temp)
                  (get-ccms1 m (cdr edcls) key ctx state))
                 ((equal m *0*)
                  (get-ccms1 (cadr temp) (cdr edcls) key ctx state))
                 ((and (subsetp-equal m (cadr temp))
                       (subsetp-equal (cadr temp) m))
                  (get-ccms1 m (cdr edcls) key ctx state))
                 (t (er soft ctx
                        "It is illegal to declare two different ~
                         sets values for the key ~x0 for the admission ~
                         of a single function. But you have specified ~
                         ~x0 ~x1 and ~x1 ~x2."
                        key m (cadr temp))))))
        (t (get-ccms1 m (cdr edcls) key ctx state))))

(defun get-ccms2 (lst key ctx state)
  ;; this function is based on get-measures2 in the acl2-sources
  (cond ((null lst) (value nil))
        (t (er-let* ((m (get-ccms1 *0* (fourth (car lst)) key ctx state))
                     (rst (get-ccms2 (cdr lst) key ctx state)))
                    (value (cons m rst))))))

(defun get-ccms (symbol-class lst key ctx state)

  ;; based on get-measures in the ACL2 sources

  ;; This function returns a list in 1:1 correspondence with lst containing
  ;; the user's specified :CCMs (or *0* if no measure is specified).  We
  ;; cause an error if more than one :CCMs is specified within the edcls of
  ;; a given element of lst.

  ;; If symbol-class is program, we ignore the contents of lst and simply return
  ;; all *no-measure*s.  See the comment in chk-acceptable-defuns where get-ccms is
  ;; called.

  (cond
   ((eq symbol-class :program)
    (value (make-list (length lst) :initial-element *0*)))
   (t (get-ccms2 lst key ctx state))))

(defun translate-ccms-list (ccms-list ctx wrld state)
  ;; translates a list of ccm lists using translate measures.
  (cond ((endp ccms-list) (value nil))
        (t (er-let* ((tccms (if (eq (car ccms-list) *0*)
                                (value *0*)
                              (translate-measures (car ccms-list)
                                                  t ctx wrld state)))
                     (rst (translate-ccms-list (cdr ccms-list)
                                               ctx wrld state)))
                    (value (cons tccms rst))))))

(defun chk-no-overlap (consider consider-only)
  ;; makes sure that, for each function, there is not both a consider
  ;; and consider-only hint.
  (cond ((endp consider)
         nil)
        ((not (or (eq (car consider) *0*)
                  (eq (car consider-only) *0*)))
         (cons consider consider-only))
        (t
         (chk-no-overlap (cdr consider) (cdr consider-only)))))

(defun combine-ccm-hints (consider consider-only uc uco ctx state)

  ;; combines the :CONSIDER-CCMS and :CONSIDER-ONLY-CCMS hints into one list of
  ;; CCMs. We do not allow both of these to be specified for the same function,
  ;; so we check that one or the other is *0*. The value returned is a list of
  ;; pairs. The car of each pair is nil iff the given CCM is from a
  ;; :CONSIDER-CCMS hint and non-nil if it is from a :CONSIDER-ONLY-CCMS
  ;; hint. The cdr of each pair is the hint itself. If neither xarg is given
  ;; (i.e. if they are both *0*) for a given function, the car of the pair is
  ;; nil, and the cdr is *0*.

  (cond ((endp consider)
         (value nil))
        ((eq (car consider-only) *0*)
         (er-let* ((rst (combine-ccm-hints (cdr consider) (cdr consider-only)
                                           (cdr uc) (cdr uco)
                                           ctx state)))
                  (value (acons nil (car consider) rst))))
        ((eq (car consider) *0*)
         (er-let* ((rst (combine-ccm-hints (cdr consider) (cdr consider-only)
                                           (cdr uc) (cdr uco)
                                           ctx state)))
                  (value (acons t (car consider-only) rst))))
        (t
         (er soft ctx
             "It is illegal to provide both a :CONSIDER and ~
              a :CONSIDER-ONLY hint for the same function. But ~
              you have specified :CONSIDER ~x0 and :CONSIDER-ONLY ~x1."
             (car uc) (car uco)))))

(defconst *ccg-xargs-keywords*
  '(:CONSIDER-CCMS :CONSIDER-ONLY-CCMS :TERMINATION-METHOD
                   :CCG-PRINT-PROOFS :TIME-LIMIT
                   :CCG-HIERARCHY))

(defun get-unambiguous-xargs-val1/edcls (key v edcls ctx state)

; V is the value specified so far for key in the XARSGs of this or previous
; edcls, or else the consp '(unspecified) if no value has been specified yet.
; We cause an error if a value different from that specified so far is
; specified.  We return either the consp '(unspecified) or the uniformly agreed
; upon value.

  (cond
   ((null edcls) (value v))
   ((eq (caar edcls) 'xargs)
    (let ((temp (assoc-keyword key (cdar edcls))))
      (cond ((null temp)
             (get-unambiguous-xargs-val1/edcls key v (cdr edcls) ctx state))
            ((or (consp v)
                 (equal v (cadr temp)))
             (get-unambiguous-xargs-val1/edcls key (cadr temp) (cdr edcls)
                                              ctx state))
            (t
             (er soft ctx
                 "It is illegal to specify ~x0 ~x1 in one place and ~
                  ~x2 in another within the same definition.  The ~
                  functionality controlled by that flag operates on ~
                  the entire event or not at all."
                 key v (cadr temp))))))
   (t (get-unambiguous-xargs-val1/edcls key v (cdr edcls) ctx state))))

(defun get-unambiguous-xargs-val1 (key lst ctx state)

; We scan the edcls of lst and either extract a single uniformly agreed
; upon value for key among the XARGS and return that value, or else no
; value is specified and we return the consp '(unspecified) or else two or
; more values are specified and we cause an error.  We also cause an error
; if any edcls specifies a non-symbol for the value of key.  Thus, if we
; return a symbol it is the uniformly agreed upon value and if we return
; a consp there was no value specified.

  (cond ((null lst) (value '(unspecified)))
        (t (er-let*
            ((v (get-unambiguous-xargs-val1 key (cdr lst) ctx state))
             (ans (get-unambiguous-xargs-val1/edcls key v (fourth (car lst))
                                                    ctx state)))
            (value ans)))))

(defun get-unambiguous-xargs-val (key lst default ctx state)

; Lst is a list of mutually recursive defun tuples of the form (name args doc
; edcls body).  We scan the edcls for the settings of the XARGS keyword key.
; If at least one entry specifies a setting, x, and all entries that specify a
; setting specify x, we return x.  If no entry specifies a setting, we return
; default.  If two or more entries specify different settings, we cause an
; error.

; We assume every legal value of key is a symbol.  If you supply a consp
; default and the default is returned, then no value was specified for key.

; Just to be concrete, suppose key is :mode and default is :logic.  The
; user has the opportunity to specify :mode in each element of lst, i.e., he
; may say to make the first fn :logic and the second fn :program.  But
; that is nonsense.  We have to process the whole clique or none at all.
; Therefore, we have to meld all of his various :mode specs together to come
; up with a setting for the DEFUNS event.  This function explores lst and
; either comes up with an unambiguous :mode or else causes an error.

  (er-let* ((x (get-unambiguous-xargs-val1 key lst ctx state)))
           (cond ((equal x '(unspecified)) (value default))
                 (t (value x)))))


(defun chk-acceptable-ccg-xargs (fives symbol-class ctx wrld state)
  (er-let* ((untranslated-consider (get-ccms symbol-class
                                             fives
                                             :CONSIDER-CCMs
                                             ctx state))
            (consider (translate-ccms-list untranslated-consider ctx wrld state))
            (untranslated-consider-only (get-ccms symbol-class
                                                  fives
                                                  :CONSIDER-ONLY-CCMs
                                                  ctx state))
            (consider-only (translate-ccms-list untranslated-consider-only
                                                ctx wrld state))
            (ccms (combine-ccm-hints consider consider-only
                                     untranslated-consider
                                     untranslated-consider-only
                                     ctx state))
            (verbose (get-unambiguous-xargs-flg
                      :CCG-PRINT-PROOFS
                      fives
                      (get-ccg-print-proofs) ;; default is global setting
                      ctx state))
            (time-limit (get-unambiguous-xargs-val
                         :TIME-LIMIT
                         fives
                         ;; the default time-limit is that specified in the
                         ;; world
                         (get-ccg-time-limit wrld)
                         ctx state)))
           (cond ((not (booleanp verbose))
                  (er soft ctx
                      "The :CCG-PRINT-PROOFS specified by XARGS must either ~
                       be NIL or T. ~x0 is neither."
                      verbose))
                 ((not (or (null time-limit)
                           (rationalp time-limit)))
                  (er soft ctx
                      "The :TIME-LIMIT specified by XARGS must either be NIL ~
                       or a rational number. ~x0 is neither."
                      time-limit))
                 (t
                  (value (list ccms
                               verbose
                               time-limit))))))

(defun ?-ccm-lstp (lst)
  (or (endp lst)
      (let ((ccm (car lst)))
        (and (true-listp ccm)
             (eq (car ccm) :?)
             (arglistp (cdr ccm))
             (?-ccm-lstp (cdr lst))))))

(defun ccg-redundant-measure-for-defunp (def justification wrld)
  (let* ((name (car def))
         (measure0 (if justification
                       (access justification
                               justification
                               :measure)
                     nil))
         (dcls (butlast (cddr def) 1))
         (measures (fetch-dcl-field :measure dcls)))

    (cond ((and (consp measure0)
                (eq (car measure0) :?))
           (if (and (consp measures)
                    (null (cdr measures))
                    (eq (caar measures) :?)
                    (set-equalp-eq (cdar measures)
                                   (cdr measure0)))
               'redundant
             (msg "the existing measure for ~x0 is ~x1, possibly indicating ~
                   it was previously proven terminating using the CCG ~
                   analysis. The new measure must therefore be explicitly ~
                   declared to be a call of :? on the measured subset; for ~
                   example, ~x1 will serve as the new :measure."
                  name
                  measure0)))
          (t
           (let* ((wrld1 (decode-logical-name name wrld))
                  (val (scan-to-cltl-command (cdr wrld1)))
                  (old-def (assoc-eq name (cdddr val))))
             (or (non-identical-defp-chk-measures
                  name
                  measures
                  (fetch-dcl-field :measure
                                   (butlast (cddr old-def)
                                            1))
                  justification)
                 'redundant))))))

(defun ccg-redundant-subset-for-defunp (chk-measurep chk-ccmsp def wrld)
  (let* ((name (car def))
         (justification (getprop name
                                 'justification
                                 'nil
                                 'current-acl2-world
                                 wrld))
         (mok (if chk-measurep
                  (ccg-redundant-measure-for-defunp def justification wrld)
                'redundant)))
    (cond ((consp mok) ; a message
           mok)
          ((and chk-ccmsp justification)
           (let ((subset (access justification justification :subset))
                 (ccms-lst (fetch-dcl-field :consider-only-ccms
                                            (butlast (cddr def) 1))))

; Pete: Fri Aug 16 EDT 2019: Added the (null ccms-lst) case
; below. This seems reasonable because we know that the existing
; measured subset works, and this defun is not claiming some different
; measured subset, so there's no difference between the case we're in
; and the case where the user identified the exact justification in
; the world. I need to come back to this later to make sure I'm not
; missing something.
               
             (if (or (null ccms-lst)
                     (and (consp ccms-lst)
                          (null (cdr ccms-lst))
                          (?-ccm-lstp (car ccms-lst))
                          (set-equalp-eq (all-vars1-lst (car ccms-lst) nil)
                                         subset)))
                 'redundant
               (msg "A redundant definition using CCG termination must use ~
                     the xarg :consider-only-ccms to declare a list of CCMs ~
                     of the form (:? ...) whose arguments are equal to the ~
                     measured subset of the previous definition. The ~
                     definition of ~x0 does not do this. The previously ~
                     defined version of this function has measured subset ~
                     ~x1. Thus, an appropriate list of CCMs to declare would ~
                     be ~x2."
                    name
                    subset
                    `((:? ,@subset))))))
          (t
           'redundant))))

(defun ccg-redundant-subset-for-defunsp1 (chk-measurep chk-ccmsp def-lst wrld ans)
  (if (endp def-lst)
      ans
    (let ((ans0 (ccg-redundant-subset-for-defunp chk-measurep
                                                 chk-ccmsp
                                                 (car def-lst)
                                                 wrld)))
      (cond ((consp ans0) ans0) ; a message
            ((eq ans ans0)
             (ccg-redundant-subset-for-defunsp1 chk-measurep
                                                chk-ccmsp
                                                (cdr def-lst)
                                                wrld
                                                ans))
            (t nil)))))

(defun ccg-redundant-subset-for-defunsp (chk-measurep chk-ccmsp def-lst wrld)
  (if (null def-lst)
      'redundant
    (let ((ans (ccg-redundant-subset-for-defunp chk-measurep
                                                chk-ccmsp
                                                (car def-lst)
                                                wrld)))
      (if (consp ans)
          ans ;; a message
        (ccg-redundant-subset-for-defunsp1 chk-measurep
                                           chk-ccmsp
                                           (cdr def-lst)
                                           wrld
                                           ans)))))

; Should this be in sync with redundant-or-reclassifying-defunsp ? --harshrc
(defun ccg-redundant-or-reclassifying-defunsp (chk-measurep
                                               chk-ccmsp
                                               defun-mode
                                               symbol-class
                                               ld-skip-proofsp
                                               def-lst
                                               wrld)
  (let* ((dcls (butlast (cddar def-lst) 1))
         (termination-method (fetch-dcl-field :termination-method dcls))
         (use-acl2p (and (consp termination-method)
                         (eq (car termination-method) :measure)))
         (ans (redundant-or-reclassifying-defunsp0 defun-mode
                                                   symbol-class
                                                   ld-skip-proofsp
                                                   use-acl2p
                                                   def-lst
                                                   wrld)))
    (cond ((or use-acl2p
               (consp ans) ;; a message
               (not (eq ans 'redundant))

; the following 2 are a negation of the conditions for checking measures in
; redundant-or-reclassifying-defunsp. We skip the check that each old
; definition also has defun-mode of :logic, because if
; redundant-or-reclassifying-defunsp0 returns 'redundant, and defun-mode is
; :logic, we know that the old definitions must also all be logic (otherwise
; there would have been an error or the new definitions would be
; reclassifications). Keep this in sync with the conditions for checking
; measures in redundant-or-reclassifying-defunsp.
               
               (not (eq defun-mode :logic))
               ld-skip-proofsp)
           ans)
          (t
           (ccg-redundant-subset-for-defunsp chk-measurep
                                             chk-ccmsp
                                             def-lst
                                             wrld)))))

(defun get-and-chk-ccg-hierarchy (fives ctx wrld state)
  (er-let*
   ((hierarchy (get-unambiguous-xargs-val
                :CCG-HIERARCHY
                fives
                *0*
                ctx state)))
    (if (equal hierarchy *0*)
        (value (get-ccg-hierarchy wrld))
      (er-progn
       (chk-ccg-hierarchy hierarchy ctx state)
       (value (fix-ccg-hierarchy hierarchy))))))

(defun ccg-hierarchy-kinds-of-levels (hierarchy has-ccgp has-measurep)
  (declare (xargs :guard (and (hlevel-listp hierarchy)
                              (booleanp has-ccgp)
                              (booleanp has-measurep))))
  (cond ((and has-ccgp has-measurep)
         (mv t t))
        ((endp hierarchy)
         (mv has-ccgp has-measurep))
        (t
         (let ((is-measurep (equal (caar hierarchy) :measure)))
           (ccg-hierarchy-kinds-of-levels (cdr hierarchy)
                                          (or has-ccgp (not is-measurep))
                                          (or has-measurep is-measurep))))))


; ccg version of chk-acceptable-defuns (see defuns.lisp). Should be synced? --harshrc
; annotated portions which differ by "ccg rewrite" comment --harshrc
(defun ccg-chk-acceptable-defuns (lst ctx wrld state #+:non-standard-analysis std-p)

; WARNING: This function installs a world, hence should only be called when
; protected by a revert-world-on-error.

; Rockwell Addition:  We now also return the non-executable flag.

; This function does all of the syntactic checking associated with defuns.  It
; causes an error if it doesn't like what it sees.  It returns the traditional
; 3 values of an error-producing, output-producing function.  However, the
; "real" value of the function is a list of items extracted from lst during the
; checking.  These items are:

;    names     - the names of the fns in the clique
;    arglists  - their formals
;    docs      - their documentation strings
;    pairs     - the (section-symbol . citations) pairs parsed from docs
;    guards    - their translated guards
;    measures  - their translated measure terms
;    ruler-extenders-lst
;              - their ruler-extenders
;    mp        - the domain predicate (e.g., o-p) for well-foundedness
;    rel       - the well-founded relation (e.g., o<)
;    hints     - their translated hints, to be used during the proofs of
;                the measure conjectures, all flattened into a single list
;                of hints of the form ((cl-id . settings) ...).
;    guard-hints
;              - like hints but to be used for the guard conjectures and
;                untranslated
;    std-hints (always returned, but only of interest when
;               #+:non-standard-analysis)
;              - like hints but to be used for the std-p conjectures
;    otf-flg   - t or nil, used as "Onward Thru the Fog" arg for prove
;    bodies    - their translated bodies
;    symbol-class
;              - :program, :ideal, or :common-lisp-compliant
;    normalizeps
;              - list of Booleans, used to determine for each fn in the clique
;                whether its body is to be normalized
;    reclassifyingp
;              - t or nil, t if this is a reclassifying from :program
;                with identical defs.
;    wrld      - a modified wrld in which the following properties
;                may have been stored for each fn in names:
;                  'formals, 'stobjs-in and 'stobjs-out
;    non-executablep - t or nil according to whether these defuns are to
;                  non-executable.  Non-executable defuns may violate the
;                  translate conventions on stobjs.
;    guard-debug
;              - t or nil, used to add calls of EXTRA-INFO to guard conjectures
;    measure-debug
;              - t or nil, used to add calls of EXTRA-INFO to measure conjectures
;    split-types-terms
;              - list of translated terms, each corresponding to type
;                declarations made for a definition with XARGS keyword
;                :SPLIT-TYPES T
;    new-lambda$-alist-pairs
;              - list of pairs to add to the world global lambda$-alist

  (er-let*
   ((fives (chk-defuns-tuples lst nil ctx wrld state))

; Fives is a list in 1:1 correspondence with lst.  Each element of
; fives is a 5-tuple of the form (name args doc edcls body).  Consider the
; element of fives that corresponds to

;   (name args (DECLARE ...) "Doc" (DECLARE ...) body)

; in lst.  Then that element of fives is (name args "Doc" (...) body),
; where the ... is the cdrs of the DECLARE forms appended together.
; No translation has yet been applied to them.  The newness of name
; has not been checked yet either, though we know it is all but new,
; i.e., is a symbol in the right package.  We do know that the args
; are all legal.

    (tm (get-unambiguous-xargs-flg :TERMINATION-METHOD
                                   fives
                                   (get-termination-method wrld)
                                   ctx state)) ;ccg rewrite
    (term-method (if (or (eq tm :ccg)
                         (eq tm :measure))
                     (value tm)
                   (er soft ctx
                       "The :TERMINATION-METHOD flag must be :CCG or ~
                        :MEASURE, but ~x0 is none of these."
                       tm))) ;ccg rewrite

    (names (value (strip-cars fives))))
   (er-progn
    (chk-no-duplicate-defuns names ctx state)
    (chk-xargs-keywords fives ;ccg rewrite
                        (if (eq term-method :ccg)
                            (append *ccg-xargs-keywords*
                                    *xargs-keywords*)
                          (cons :termination-method
                                *xargs-keywords*))
                        ctx state)
    (er-let*
     ((tuple (chk-acceptable-defuns0 fives ctx wrld state))
      (hierarchy (if (eq term-method :ccg)
                     (get-and-chk-ccg-hierarchy fives ctx wrld state)
                   (value nil)))) ;ccg rewrite
     (let* ((stobjs-in-lst (car tuple))
            (defun-mode (cadr tuple))
            (non-executablep (caddr tuple))
            (symbol-class (cdddr tuple)))
       (mv-let ;ccg rewrite
        (has-ccgp has-measurep)
        (if (eq term-method :measure)
          (mv nil t)
        (ccg-hierarchy-kinds-of-levels hierarchy nil nil))
        (let ((rc (ccg-redundant-or-reclassifying-defunsp
                   has-measurep has-ccgp
                   defun-mode symbol-class
                   (ld-skip-proofsp state) lst wrld))) ;ccg rewrite - CHECK - harshrc
          (cond
           ((eq rc 'redundant)
            (chk-acceptable-defuns-redundancy names ctx wrld state))
           ((eq rc 'verify-guards)

; We avoid needless complication by simply causing a polite error in this
; case.  If that proves to be too inconvenient for users, we could look into
; arranging for a call of verify-guards here.

            (chk-acceptable-defuns-verify-guards-er names ctx wrld state))

; Synced with latest version of chk-acceptable-defuns svn version 1020
; Added below cond clause for hons.
; june 16 2013 - harshrc
           ((and (eq rc 'reclassifying)
              (conditionally-memoized-fns names
                                          (table-alist 'memoize-table wrld)))

; We no longer recall exactly why we have this restriction.  However, after
; discussing this with Sol Swords we think it's because we tolerate all sorts
; of guard violations when dealing with :program mode functions, but we expect
; guards to be handled properly with :logic mode functions, including the
; condition function.  If we verify termination and guards for the memoized
; function but not the condition, that could present a problem.  Quite possibly
; we can relax this check somewhat after thinking things through -- e.g., if
; the condition function is a guard-verified :logic mode function -- if there
; is demand for such an enhancement.

         (er soft ctx
             "It is illegal to verify termination (i.e., convert from ~
              :program to :logic mode) for function~#0~[~/s~] ~&0, because ~
              ~#0~[it is~/they are~] currently memoized with conditions; you ~
              need to unmemoize ~#0~[it~/them~] first.  See :DOC memoize."
             (conditionally-memoized-fns names
                                         (table-alist 'memoize-table wrld))))
           (t
            (er-let*
             ((tuple1 (chk-acceptable-defuns1 names fives
                                              stobjs-in-lst defun-mode symbol-class rc
                                              non-executablep ctx wrld state
                                              #+:non-standard-analysis std-p))
              (tuplec (if (eq term-method :measure)
                          (value (list nil nil nil)) ;ccg rewrite
                        (chk-acceptable-ccg-xargs fives symbol-class
                                                  ctx wrld state))))
             (value (append (list 'chk-acceptable-defuns term-method)
                         (cdr tuple1)
                         tuplec
                         `(,hierarchy))))))))))))) ;ccg rewrite

;; (defun ccg-chk-acceptable-defuns (fives lst ctx wrld state #+:non-standard-analysis std-p)

;; ; Rockwell Addition:  We now also return the non-executable flag.

;; ; This function does all of the syntactic checking associated with defuns.  It
;; ; causes an error if it doesn't like what it sees.  It returns the traditional
;; ; 3 values of an error-producing, output-producing function.  However, the
;; ; "real" value of the function is a list of items extracted from lst during the
;; ; checking.  These items are:

;; ;    names     - the names of the fns in the clique
;; ;    arglists  - their formals
;; ;    docs      - their documentation strings
;; ;    pairs     - the (section-symbol . citations) pairs parsed from docs
;; ;    guards    - their translated guards
;; ;    measures  - their translated measure terms
;; ;    ruler-extenders-lst
;; ;              - their ruler-extenders
;; ;    mp        - the domain predicate (e.g., o-p) for well-foundedness
;; ;    rel       - the well-founded relation (e.g., o<)
;; ;    hints     - their translated hints, to be used during the proofs of
;; ;                the measure conjectures, all flattened into a single list
;; ;                of hints of the form ((cl-id . settings) ...).
;; ;    guard-hints
;; ;              - like hints but to be used for the guard conjectures and
;; ;                untranslated
;; ;    std-hints (always returned, but only of interest when
;; ;               #+:non-standard-analysis)
;; ;              - like hints but to be used for the std-p conjectures
;; ;    otf-flg   - t or nil, used as "Onward Thru the Fog" arg for prove
;; ;    bodies    - their translated bodies
;; ;    symbol-class
;; ;              - :program, :ideal, or :common-lisp-compliant
;; ;    normalizeps
;; ;              - list of Booleans, used to determine for each fn in the clique
;; ;                whether its body is to be normalized
;; ;    reclassifyingp
;; ;              - t or nil, t if this is a reclassifying from :program
;; ;                with identical defs.
;; ;    wrld      - a modified wrld in which the following properties
;; ;                may have been stored for each fn in names:
;; ;                  'formals, 'stobjs-in and 'stobjs-out
;; ;    non-executablep - t or nil according to whether these defuns are to
;; ;                  non-executable.  Non-executable defuns may violate the
;; ;                  translate conventions on stobjs.
;; ;    guard-debug
;; ;              - t or nil, used to add calls of EXTRA-INFO to guard conjectures

;;   (er-let*
;;    ((tm (get-unambiguous-xargs-flg :TERMINATION-METHOD
;;                                    fives
;;                                    (get-termination-method wrld)
;;                                    ctx state))
;;     (term-method (if (or (eq tm :ccg)
;;                          (eq tm :measure))
;;                      (value tm)
;;                    (er soft ctx
;;                        "The :TERMINATION-METHOD flag must be :CCG or ~
;;                         :MEASURE, but ~x0 is none of these."
;;                        tm)))
;;     (names (value (strip-cars fives))))
;;    (er-progn
;;     (chk-no-duplicate-defuns names ctx state)
;;     (chk-xargs-keywords fives
;;                         (if (eq term-method :ccg)
;;                             (append *ccg-xargs-keywords*
;;                                     *xargs-keywords*)
;;                           (cons :termination-method
;;                                 *xargs-keywords*))
;;                         ctx state)
;;     (er-let*
;;      ((tuple0 (chk-acceptable-defuns0 fives ctx wrld state))
;;       (stobjs-in-lst (value (car tuple0)))
;;       (defun-mode (value (cadr tuple0)))
;;       (verify-guards (value (caddr tuple0)))
;;       (symbol-class (value (cdddr tuple0)))
;;       (hierarchy (if (eq term-method :ccg)
;;                      (get-and-chk-ccg-hierarchy fives ctx wrld state)
;;                    (value nil))))
;;      (mv-let
;;       (has-ccgp has-measurep)
;;       (if (eq term-method :measure)
;;           (mv nil t)
;;         (ccg-hierarchy-kinds-of-levels hierarchy nil nil))
;;       (er-let*
;;        ((rc (value (ccg-redundant-or-reclassifying-defunsp
;;                     has-measurep has-ccgp
;;                     defun-mode symbol-class
;;                     (ld-skip-proofsp state) lst wrld))))
;;        (cond
;;         ((eq rc 'redundant)
;;          (chk-acceptable-defuns-redundancy names ctx wrld state))
;;         ((eq rc 'verify-guards)
;;          (chk-acceptable-defuns-verify-guards names ctx wrld state))
;;         (t
;;          (er-let*
;;           ((tuple1 (chk-acceptable-defuns1 names fives stobjs-in-lst
;;                                            defun-mode symbol-class rc ctx
;;                                            wrld state
;;                                            #+:non-standard-analysis
;;                                            std-p))
;;            (tuplec (if (eq term-method :measure)
;;                        (value (list nil nil nil))
;;                      (chk-acceptable-ccg-xargs fives symbol-class
;;                                                ctx wrld state))))
;;           (value (append (list 'chk-acceptable-defuns term-method)
;;                          (cdr tuple1)
;;                          tuplec
;;                          `(,hierarchy))))))))))))

(defun find-?-ccm1 (ccm-list)
  (and (consp ccm-list)
       (let ((ccm (car ccm-list)))
         (or (and (consp ccm)
                  (eq (car ccm) :?)
                  ccm)
             (find-?-ccm1 (cdr ccm-list))))))

(defun find-?-ccm (names ccms)
  ;; looks for CCMS with :? as the function.
  (if (endp ccms)
      nil
    (let ((bad-ccm (find-?-ccm1 (car ccms))))
      (if bad-ccm
          (cons (car names) bad-ccm)
        (find-?-ccm (cdr names) (cdr ccms))))))

(defun fns-without-consider-only-ccms-hints (names ccms)
  ;; checks if all the CCMs have been declared using :CONSIDER-ONLY-CCMS. Any
  ;; functions for which this is not the case are collected into a list.
  ;; Ccms should of the form returned by combine-ccm-hints.
  (if (endp ccms)
      nil
    (let ((rst (fns-without-consider-only-ccms-hints (cdr names)
                                                     (cdr ccms))))
      (if (and (consp (car ccms))
               (caar ccms))
          rst
        (cons (car names)
              rst)))))

(defun-raw ccm-o-p-clauses2 (contexts term clauses)
  (if (endp contexts)
      clauses
    (ccm-o-p-clauses2
     (cdr contexts)
     term
     (conjoin-clause-to-clause-set
      (add-literal term
                   (dumb-negate-lit-lst (context-ruler (car contexts)))
                   t)
      clauses))))

(defun-raw ccm-o-p-clauses1 (contexts ccm-list clauses)
  (if (endp ccm-list)
      clauses
    (ccm-o-p-clauses1 contexts (cdr ccm-list)
                       (ccm-o-p-clauses2 contexts
                                          (mcons-term* 'o-p (car ccm-list))
                                          clauses))))

(defun-raw ccm-o-p-clauses0 (contexts ccm-list clauses)
  (cond ((endp contexts)
         clauses)
        ((eq (car ccm-list) *0*)
         (ccm-o-p-clauses0 (cdr contexts)
                            (cdr ccm-list)
                            clauses))
        (t
         (ccm-o-p-clauses0 (cdr contexts)
                            (cdr ccm-list)
                            (ccm-o-p-clauses1 (car contexts)
                                               (car ccm-list)
                                               clauses)))))

(defun-raw ccm-o-p-clauses (contexts ccm-list)
  ;; builds the clauses to prove that the CCMs in ccm-list all
  ;; evaluate to natural numbers.
  (ccm-o-p-clauses0 contexts ccm-list nil))

(defun-raw ccg-intermediate-step (accgs ces new-hlevel old-hlevel proved qspv state)
   (er-let*
    ((triple (accg-refine-accgs accgs ces old-hlevel new-hlevel qspv state))
     (caccgs (value (car triple)))
     (uaccgs (value (cadr triple)))
     (uces (value (cddr triple))))
    (cond ((endp caccgs)
           (pprogn
            ;;(progn (print uaccgs) state)
            (ccg-io? basics nil state
                     ()
                     (fms "Since we have no new information, we skip size ~
                           change analysis and attempt to further refine the ~
                           SCCs.~|"
                          nil
                          *standard-co*
                          state
                          nil))
            (value (list* proved uaccgs uces))))
           (t
            (pprogn
             (let ((clen (len caccgs)))
               (ccg-io? basics nil state
                        (uaccgs clen caccgs)
                        (fms "~@0 of the CCG ~#\3~[was~/were~] altered. We ~
                              analyze ~#\3~[it~/each of these~] with the size ~
                              change termination analysis.~@4~|"
                             `((#\0 . ,(if (consp uaccgs)
                                           "~N1 of the ~n2 SCCs"
                                         "~#\3~[The sole SCC~/All the SCCs~]"))
                               (#\1 . ,clen)
                               (#\2 . ,(+ clen (len uaccgs)))
                               (#\3 . ,caccgs)
                               (#\4 . ,(if (endp uaccgs)
                                           ""
                                         " The others will be set aside ~
                                               for further refinement.")))
                             *standard-co*
                             state
                             nil)))
             (accg-sct-list caccgs proved uaccgs uces state))))))

(defun-raw ccg-measure-step (hlevel names t-machines measure-alist mp rel
                                    bodies verbose qspv state)
  (if (consp measure-alist)
      (let ((ctx (access query-spec-var qspv :ctx))
            (wrld (access query-spec-var qspv :wrld))
            (ens (access query-spec-var qspv :ens))
            (stop-time (access query-spec-var qspv :stop-time))
            (otf-flg (access query-spec-var qspv :otf-flg))
            (pt (cadr hlevel)))
     (pprogn
       (ccg-io? basics nil state
                (hlevel)
                (fms "The current level of the CCG hierarchy is ~x0. We ~
                      therefore attempt a measure proof.~|"
                     `((#\0 . hlevel))
                     *standard-co*
                     state
                     nil))
       (mv-let
        (erp pair state)
        (er-let*
         ((hints (if (equal pt :built-in-clauses)
                     (translate-hints
                      "Measure Built-in-clauses Hint"
                      '(("goal"
                         :do-not '(eliminate-destructors
                                   eliminate-irrelevance
                                   generalize
                                   fertilize)
                         :in-theory (theory 'minimal-theory)
                         :do-not-induct :otf-flg-override))
                      ctx wrld state)
                   (value (translated-limit-induction-hint (cadr pt))))))
         (state-global-let*
          ((inhibit-output-lst (if verbose
                                   (@ inhibit-output-lst)
                                 (list* 'event 'error (@ inhibit-output-lst)))))
          (maybe-prover-before-stop-time
           stop-time ctx state
           (prove-termination names t-machines measure-alist mp rel
                              hints otf-flg bodies nil
                              ctx ens wrld state
                              (f-get-global
                               'accumulated-ttree
                               state)))))
        (if erp
            (er-progn
             (time-check stop-time ctx state)
             (pprogn
              (ccg-io? basics nil state
                       ()
                       (fms "Since ACL2 has failed to prove the measure ~
                             conjecture, we continue with the hierarchical ~
                             analysis.~|"
                            nil
                            *standard-co*
                            state
                            nil))
              (value nil)))
          (pprogn
           (ccg-io? basics nil state
                    ()
                    (fms "ACL2 has succeeded in proving the measure ~
                          conjecture, thereby proving termination."
                         nil
                         *standard-co*
                         state
                         nil))
           (value (list* :measure
                         (car pair)
                         measure-alist
                         (cdr pair))))))))
    (pprogn
     (ccg-io? basics nil state
              (hlevel)
              (fms "Skipping level ~x0 of the hierarchy due to previously ~
                    mentioned error when guessing measures."
                   `((#\0 . hlevel))
                   *standard-co*
                   state
                   nil))
     (value nil))))

(defun-raw ccg (accgs ces last-ccg-hlevel hierarchy proved context-array
                      names arglists t-machines measure-alist mp rel bodies
                      verbose qspv state)
  (cond ((endp accgs)
         (pprogn
          (increment-timer 'other-time state)
          (ccg-io? basics nil state
                   ()
                   (fms "We have successfully proven termination! We now weed ~
                         out irrelevant CCMs so that we can minimize the ~
                         measured-subset. This may require running the size ~
                         change analysis several more times.~|"
                        nil
                        *standard-co*
                        state
                        nil))
          (increment-timer 'print-time state)
          (er-let*
           ((ms (ccg-generate-measure-alist
                 nil proved
                 names arglists
                 context-array
                 ;; the following is overly-cautious. It could be the case that
                 ;; some SCCs were proven terminating with ccmfs-per-node
                 ;; and others with ccmfs-per-edge, in which case we would
                 ;; be assuming here that we proved all of the SCCs terminating
                 ;; with ccmfs-per-edge.
                 (hlevel-ccmfs-per-nodep last-ccg-hlevel)
                 state)))
           (pprogn
            (mv-let
             (col state)
             (io? event nil (mv col state)
                  (names ms)
                  (fmt "CCG analysis has succeeded in proving termination of ~
                        ~&0 using CCMs over the following variables~#0~[~/, ~
                        respectively~]: ~&1. Thus, we admit ~#0~[this ~
                        function~/these ~ functions~] under the principle of ~
                        definition."
                       (list (cons #\0 names)
                             (cons #\1 (strip-cddrs ms)))
                       *standard-co*
                       state
                       nil)
                  :default-bindings ((col 0)))
             (value (list* :ccg
                           col
                           ms
                           (f-get-global
                            'accumulated-ttree
                            state))))))))
        ((endp hierarchy)
         (pprogn
          (ccg-io? basics nil state
                   ()
                   (fms "We have completed all levels of the hierarchy, but ~
                         have failed to prove termination."
                        ()
                        *standard-co*
                        state
                        nil))
          (if (null (car ces))
              state
            (ccg-io? counter-example nil state
                     ()
                     (print-counter-example
                      (car accgs) (car ces)
                      context-array
                      (access query-spec-var qspv :ctx)
                      (access query-spec-var qspv :ens)
                      (access query-spec-var qspv :wrld)
                      state)))
          (mv t nil state)))
        ((eq (caar hierarchy) :MEASURE)
         (er-let*
          ((tuple (ccg-measure-step (car hierarchy)
                                    names
                                    t-machines
                                    measure-alist
                                    mp
                                    rel
                                    bodies
                                    verbose
                                    qspv
                                    state)))
          (if tuple
              (value tuple)
            (ccg accgs ces last-ccg-hlevel (cdr hierarchy) proved context-array
                 names arglists t-machines measure-alist mp rel bodies
                 verbose qspv state))))
        (t
         (er-let*
          ((tuple
            (state-global-let*
             ((inhibit-output-lst
               (if verbose
                   (@ inhibit-output-lst)
                 (list* 'prove 'proof-tree (@ inhibit-output-lst)))))
             (ccg-intermediate-step accgs
                                    ces
                                    (car hierarchy)
                                    last-ccg-hlevel
                                    proved
                                    qspv
                                    state)))
           (nproved (value (car tuple)))
           (naccgs (value (cadr tuple)))
           (nces (value (cddr tuple))))
          (ccg naccgs nces (car hierarchy) (cdr hierarchy) nproved
               context-array
               names arglists t-machines measure-alist mp rel bodies
               verbose qspv state)))))

(defun-raw build-accgs (names contexts functs ccm-hints wrld state)
  (let* ((context-array (context-array contexts))
         ;; (num-contexts (array-dimension context-array 0))
         (accgs (build-and-annotate-accgs names
                                          functs
                                          contexts
                                          (pairlis$ names ccm-hints))))
    ;; first we build the accgs using the first restriction
    (pprogn
     (increment-timer 'other-time state)
     (ccg-io? basics nil state
              (names context-array accgs)
              (pprogn
               (fms "We begin with the Calling Context Graph (CCG), ~
                     containing the following contexts (if the output doesn't ~
                     make sense, see :DOC CCG and also the paper referenced ~
                     above):~|"
                    nil
                    *standard-co*
                    state
                    nil)
               (print-context-array1 0 names context-array state)
               (fms "and the following edges:~|"
                    nil *standard-co* state nil)
               (print-accg-edges1 accgs state)
               (fms "We have annotated the CCG with the following calling ~
                     context measures (CCMs):~|"
                    nil *standard-co* state nil)
               (print-funct-ccms functs wrld state)))
     (increment-timer 'print-time state)
     (pprogn
      (ccg-io? basics nil state
               ()
               (fms "Before we begin the hierarchical analysis, we run our ~
                     size-change analysis so we have a baseline for refinement."
                    nil
                    *standard-co*
                    state
                    nil))
      (er-let*
       ((tuple (accg-sct-list accgs nil nil nil state)))
       (value (cons context-array tuple)))))))

(defun max-induction-depth1 (hierarchy max)
  (declare (xargs :guard (and (hlevel-listp hierarchy)
                              (integerp max)
                              (<= -1 max))))
  (if (endp hierarchy)
      max
    (max-induction-depth1
     (cdr hierarchy)
     (cond ((or (equal (caar hierarchy) :measure)
                (equal (hlevel-proof-technique (car hierarchy))
                       :built-in-clauses))
            max)
           (t
            (max max (cadr (hlevel-proof-technique (car hierarchy)))))))))

(defun max-induction-depth (hierarchy)
  (max-induction-depth1 hierarchy -1))

(defun ruler-extender-printout1 (names ruler-extenders-lst)
  (if (endp names)
      nil
    (cons `("function ~x0 has ruler extenders ~x1"
            (#\0 . ,(car names))
            (#\1 . ,(car ruler-extenders-lst)))
          (ruler-extender-printout1 (cdr names)
                                    (cdr ruler-extenders-lst)))))

(defun ruler-extender-printout (names ruler-extenders-lst)
  `("" "~@*." "~@*, and " "~@*, "
    ,(ruler-extender-printout1 names ruler-extenders-lst)))

(defun-raw prove-termination-with-ccg (names functs contexts
                                             ruler-extenders-lst ccm-hints
                                             hierarchy verbose time-limit
                                             arglists measures t-machines mp
                                             rel otf-flg bodies
                                             ctx ens wrld state ttree)

  ;; based on prove-termination in the ACL2 sources, this function
  ;; attempts to prove the termination of the given functions. names
  ;; is the list of names of the the functions, term-method is the
  ;; termination method to be used (:hybrid or :ccg), contexts are the
  ;; contexts for the functions, ccm-hints is a list of pairs as defined by
  ;; combine-ccm-hints, cpn, verbose, time-limit, and ccm-comparison-scheme are the
  ;; user-specified CCG options, arglists is the list of lists of
  ;; formals for the functions, measures are the user-specified
  ;; measures, t-machines are the termination machines of the
  ;; functions, mp and rel are the domain and relation for proving
  ;; termination with a measure and otf-flg is the on-through-the-fog
  ;; flag.

  ;; If we succeed, we return 4 values, consed together as "the" value
  ;; in this error/value/state producing function. The first value is
  ;; the proof method that ultimately proved termination (:ccg or
  ;; :measure). The second value is the "justification" alist. For a
  ;; measure-based proof, this is the measure-alist, and for a
  ;; CCG-based proof, this is the result of
  ;; ccg-generate-measure-alist. The last two values are the column
  ;; and ttree. Currently, we simply return 0 for the column and nil
  ;; for the ttree. I believe the column value is correct, but the
  ;; ttree should eventually be the accumulation of all the ttrees
  ;; associated with all the proofs done in the termination analysis.


  ;; This function is specially coded so that if contexts is nil then
  ;; it is a signal that there is only one element of names and it is
  ;; a non-recursive function.  In that case, we short-circuit all of
  ;; the proof machinery and simply do the associated output.  We
  ;; coded it this way to preserve the invariant that
  ;; prove-termination is THE place the defun output is initiated.

  ;; This function increments timers.  Upon entry, any accumulated time
  ;; is charged to 'other-time.  The printing done herein is charged
  ;; to 'print-time and the proving is charged to 'prove-time.

  (let* ((ccms (mapcar #'cdr ccm-hints))
         (entry (find-?-ccm names ccms))
         ;;(time-limit (get-ccg-time-limit wrld))
         (stop-time (if time-limit (+ (get-internal-run-time)
                                      (* internal-time-units-per-second
                                         time-limit))
                      nil))
         (qspv (make query-spec-var
                            :stop-time stop-time
                            :mem (create-memoization
                                  (max-induction-depth hierarchy))
                            :otf-flg otf-flg
                            :ens ens
                            :ctx ctx
                            :wrld wrld)))
    (cond
     ((and entry
           (not (ld-skip-proofsp state)))
      (let ((fn (car entry))
            (ccm (cdr entry)))
        (er soft ctx
            "A CCM of the form (:? v1 ... vk) is only legal when the defun is ~
             redundant (see :DOC redundant-events) or when skipping proofs ~
             (see :DOC ld-skip-proofsp).  The CCM ~x0 supplied for function ~
             symbol ~x1 is thus illegal."
            ccm fn)))
     ((null contexts)
      (mv-let (col state)
              (io? event nil (mv col state)
                   (names)
                   (fmt "Since ~&0 is non-recursive, its admission is trivial.  "
                        (list (cons #\0 names))
                        (proofs-co state)
                        state
                        nil)
                   :default-bindings ((col 0)))
              (value (list* :ccg (or col 0) nil nil))))
     ((ld-skip-proofsp state)
      (let ((fns (fns-without-consider-only-ccms-hints names ccms)))
        (if (consp fns)
            (er soft ctx
                "Proofs cannot be skipped on a CCG termination proof unless ~
                 CCMs are defined for every function. You did not supply CCMs ~
                 for function~#0~[~/s~] ~&0. Therefore, proofs cannot be skipped."
                fns)
          (value (list* :ccg
                        0
                        (pairlis$ names
                                  (mapcar (lambda (x)
                                            `(:? ,@(all-vars1-lst (cdr x) nil)))
                                          ccms))
                        ;nil -- harshrc typo bug?? Dec 23 2014 10:35pm
                        nil)))))
     (t
      (pprogn
       (ccg-io?
        basics nil state
        (names ruler-extenders-lst)
        (fms "Attempting to prove termination using Calling Context Graph ~
              (CCG) analysis. There are various ways in which users can ~
              control CCG analysis. See the :DOC CCG for details. This ~
              analysis is described in a 2006 CAV paper by Manolios and ~
              Vroon.~|~%The ruler-extenders for each function are as follows: ~
              ~*0~|"
             `((#\0 .
                ,(ruler-extender-printout names
                                          ruler-extenders-lst)))
             *standard-co*
             state
             nil))
       (simplify-contexts contexts ens wrld ctx state)
       (mv-let
        (o-p-clauses ttree)
        (clean-up-clause-set (ccm-o-p-clauses contexts ccms)
                             ens wrld ttree state)
        (er-let*
            ((ttree (accumulate-ttree-and-step-limit-into-state
                      ttree :skip state)))
        (pprogn
         (increment-timer 'other-time state)
         (er-let*
          ((displayed-goal (value
                            (prettyify-clause-set o-p-clauses
                                                  (let*-abstractionp state)
                                                  wrld)))
           (simp-phrase (value (tilde-*-simp-phrase ttree)))
           (ttree1
            (if o-p-clauses
                (pprogn
                 (io? event nil state
                      (ttree displayed-goal simp-phrase)
                      (fms "You have told us to consider CCMs that are not ~
                             trivially proved to be ordinals. ~
                             Therefore, the conjecture that we must prove ~
                             before we can continue with the CCG ~
                             analysis~#0~[~/, given ~*1,~] is ~
                             ~@2~%~%Goal~%~Q34."
                           `((#\0 . ,(if (nth 4 simp-phrase) 1 0))
                             (#\1 . ,simp-phrase)
                             (#\2 . ,(if (tagged-objectsp 'sr-limit ttree)
                                         " as follows (where the ~
                                           subsumption/replacement limit ~
                                           affected this analysis; see :DOC ~
                                           case-split-limitations)."
                                       ""))
                             (#\3 . ,displayed-goal)
                             (#\4 . ,(term-evisc-tuple nil state)))
                           (proofs-co state)
                           state
                           nil))
                 (increment-timer 'print-time state)
                 (prove (termify-clause-set o-p-clauses)
                        (make-pspv
                         ens wrld state
                         :displayed-goal displayed-goal
                         :otf-flg otf-flg)
                        nil ens wrld ctx state))
              (value ttree))))
          (mv-let
           (has-ccgp has-measurep)
           (ccg-hierarchy-kinds-of-levels hierarchy nil nil)
           (er-let*
            ((ba-tuple
              (if has-ccgp
                  (build-accgs names contexts functs ccm-hints wrld state)
                (list* (make-array 0
                                   :initial-element (make-context)
                                   :element-type 'context)
                       `(,(make-array 0
                                      :initial-element (make-accg-node)
                                      :element-type 'accg-node))
                       `(,(make-array 0
                                      :initial-element (make-accg-node)
                                      :element-type 'accg-node))
                       `(nil))))
             (context-array (value (car ba-tuple)))
             (proved-accgs (value (cadr ba-tuple)))
             (accgs (value (caddr ba-tuple)))
             (ces (value (cdddr ba-tuple)))
             (measure-alist
              (if (not has-measurep)
                  (value nil)
                (mv-let
                 (erp ma state)
                 (guess-measure-alist names arglists
                                      measures
                                      t-machines
                                      ctx wrld state)
                 (if (not erp)
                     (value ma)
                   (pprogn
                    (ccg-io? basics nil state
                             (names)
                             (fms "Since there was an error guessing the ~
                                   measure~#0~[~/s~], we will skip all levels ~
                                   of the hierarchy of the form (:MEASURE ~
                                   PT).~|"
                                  `((#\0 . ,names))
                                  *standard-co*
                                  state
                                  nil))
                    (value nil)))))))
            (er-let* ((quadruple
                       (ccg accgs ces nil hierarchy proved-accgs context-array
                            names arglists t-machines measure-alist mp rel bodies
                            verbose qspv state)))
              (let* ((term-method (car quadruple))
                     (col (cadr quadruple))
                     (measure-alist (caddr quadruple))
                     (ttree-new (cdddr quadruple)))
                (prog2$
                 nil;dummy --harshrc
                 ;(cw "~%DEBUG: measure-alist = ~x0~%" measure-alist)
                 (value (list* term-method
                               col
                               measure-alist
                               (cons-tag-trees ttree-new ttree1))))))

              )))))))))))

(defun-raw ccg-prove-termination-recursive
  (names arglists measures ccm-hints
         ruler-extenders-lst t-machines mp rel
         verbose time-limit hierarchy
         otf-flg bodies ctx ens wrld state)

; Next we get the measures for each function.  That may cause an error
; if we couldn't guess one for some function.

  (let ((functs (make-funct-structs names arglists)))
    (prove-termination-with-ccg
     names functs (t-machines-to-contexts t-machines functs)
     ruler-extenders-lst
     ccm-hints hierarchy verbose time-limit arglists measures t-machines
     mp rel otf-flg bodies ctx ens wrld state nil)))

(defun-raw ccg-put-induction-info
  (names arglists term-method measures ccms ruler-extenders-lst bodies
         mp rel verbose time-limit hierarchy
         hints otf-flg big-mutrec measure-debug
         ctx ens wrld state)

; WARNING: This function installs a world.  That is safe at the time of this
; writing because this function is only called by defuns-fn0, which is only
; called by defuns-fn, where that call is protected by a revert-world-on-error.

; We are processing a clique of mutually recursive functions with the names,
; arglists, measures, ruler-extenders-lst, and bodies given.  All of the above
; lists are in 1:1 correspondence.  The hints is the result of appending
; together all of the hints provided.  Mp and rel are the domain predicate and
; well-founded relation to be used.  We attempt to prove the admissibility of
; the recursions.  We cause an error if any proof fails.  We put a lot of
; properties under the function symbols, namely:

;    recursivep                     all fns in names
;    justification                  all recursive fns in names
;    induction-machine              the singly recursive fn in name*
;    quick-block-info               the singly recursive fn in name*
;    symbol-class :ideal            all fns in names

; *If names consists of exactly one recursive fn, we store its
; induction-machine and its quick-block-info, otherwise we do not.

; If no error occurs, we return a triple consisting of the column the printer
; is in, the final value of wrld and a tag tree documenting the proofs we did.

; Note: The function could be declared to return 5 values, but we would rather
; use the standard state and error primitives and so it returns 3 and lists
; together the three "real" answers.

  (prog2$

; [Note: With the introduction of loop$-recursion into ACL2 we had to modify
; this code to stop it from accepting defuns exhibiting loop$ recursion.  The
; check is conservative but meant to be fast.  JSM 23 Jan, 2020.]

   (choke-on-loop$-recursion nil
                             names
                             (car bodies) ; irrelevant if names not singleton
                             'ccg-put-induction-info)
   (let ((wrld1 (putprop-recursivep-lst nil nil names bodies wrld)))

; Pete: Putprop-recursivep-lst now takes the new loop$-recursion-checkedp and
; loop$-recursion arguments, which if nil will mean a hard error is signalled
; if putprop-recursivep-lst detects recursion inside loop$ bodies.  See the
; Essay on Choking on Loop$ Recursion.  Basically, the question is whether you
; want to extend ccg to handle such recursion (and then change the two flags
; appropriately) or leave them as is and suffer errors if ccg is called on
; functions that use loop$ recursion.

; The put above stores a note on each function symbol as to whether it is
; recursive or not.  An important question arises: have we inadventently
; assumed something axiomatically about inadmissible functions?  We say no.
; None of the functions in question have bodies yet, so the simplifier doesn't
; care about properties such as 'recursivep.  However, we make use of this
; property below to decide if we need to prove termination.

     (cond ((and (null (cdr names))
                 (null (getprop (car names) 'recursivep nil
                                'current-acl2-world wrld1)))

; If only one function is being defined and it is non-recursive, we can quit.
; But we have to store the symbol-class and we have to print out the admission
; message with prove-termination so the rest of our processing is uniform.

            (er-let*
                ((tuple (prove-termination-non-recursive names bodies mp rel hints otf-flg big-mutrec
                                                         ctx ens wrld1 state)))
              (value (cons nil tuple))))
           (t
            (let ((t-machines (termination-machines nil nil
; loop$-recursion-checkedp and loop$-recursion declared value = nil
                                                    names
                                                    nil ; = arglists
; when loop$-recursion-checkedp = nil, arglists is irrelevant
                                                    bodies ruler-extenders-lst)))
              (er-let*
                  ((wrld1 (update-w

; Sol Swords sent an example in which a clause-processor failed during a
; termination proof.  That problem goes away if we install the world, which we
; do by making the following binding.

                           t ; formerly big-mutrec
                           wrld1))
                   (quadruple
                    (if (eq term-method :measure)
                        (er-let* ((triple (prove-termination-recursive
                                           names arglists
                                           measures
                                           t-machines
                                           mp rel hints otf-flg bodies
                                           measure-debug
                                           ctx ens wrld1 state)))
                          (value (cons :measure triple)))
                        (ccg-prove-termination-recursive names arglists
                                                         measures
                                                         ccms
                                                         ruler-extenders-lst
                                                         t-machines
                                                         mp rel
                                                         verbose
                                                         time-limit
                                                         hierarchy
                                                         otf-flg bodies
                                                         ctx ens wrld1 state))))
                ;;(progn
                ;;(print quadruple)
                ;; (prog2$
                ;;  (cw "~%DEBUG:: quadruple = ~x0~%~%" quadruple)
                (let* ((term-method (car quadruple))
                       (col (cadr quadruple))
                       (measure-alist (caddr quadruple))
                       (ttree (cdddr quadruple)))
                  (er-let*
                      ((tuple (put-induction-info-recursive nil ; loop$-recursion
                                                            names arglists
                                                            col ttree
                                                            measure-alist t-machines
                                                            ruler-extenders-lst
                                                            bodies mp rel wrld1
                                                            state)))
                    (value (cons term-method tuple)))))))))))

(defun defun-redundant-get-ccms (fives wrld)
  ;; gets the CCMs installed into the world for a given set of function definitions.
  (if (endp fives)
      nil
    (let ((subset (access justification
                          (getprop (first (car fives))
                                   'justification
                                   (make justification :subset '())
                                   'current-acl2-world
                                   wrld)
                          :subset)))
      (cons `((:? ,@subset))
            (defun-redundant-get-ccms (cdr fives) wrld)))))


(defun defun-redundant-get-measures (fives wrld)
  ;; gets the CCMs installed into the world for a given set of function definitions.
  (if (endp fives)
      nil
    (let ((subset (access justification
                          (getprop (first (car fives))
                                   'justification
                                   (make justification :subset '())
                                   'current-acl2-world
                                   wrld)
                          :subset)))
      (cons `(:? ,@subset)
            (defun-redundant-get-measures (cdr fives) wrld)))))

(defun remove-keywords (keys lst)
  (cond ((endp lst)
         nil)
        ((member-eq (car lst) keys)
         (remove-keywords keys (cddr lst)))
        (t
         (list* (car lst) (cadr lst) (remove-keywords keys (cddr lst))))))

(defun remove-dcls0 (edcls keys)
  (cond ((endp edcls) nil) ;; if we don't have any xargs, we don't need to do anything.
        ((eq (caar edcls) 'xargs)
         (let ((newlst (remove-keywords keys (cdar edcls))))
           (if (endp newlst)
               (remove-dcls0 (cdr edcls) keys)
             (acons 'xargs
                    newlst
                    (remove-dcls0 (cdr edcls) keys)))))
        (t (cons (car edcls)
                 (remove-dcls0 (cdr edcls) keys)))))

(defun remove-dcls (fives keys)
  ;; we alter the definitions given in fives to remove xarg
  ;; declarations corresponding to the given keys
  (cond ((endp fives)
         nil)
        ((endp (nth 3 (car fives))) ;; if there are no declarations, there is nothing to do.
         (cons (car fives)
               (remove-dcls (cdr fives) keys)))
        (t
         (cons (update-nth 3 (remove-dcls0 (nth 3 (car fives)) keys) (car fives))
               (remove-dcls (cdr fives) keys)))))

(defun update-keyword (key val lst)
  (cond ((endp lst)
         (list key val))
        ((eq (car lst) key)
         (cons key (cons val (remove-keywords `(,key) (cddr lst)))))
        (t
         (cons (car lst)
               (cons (cadr lst)
                     (update-keyword key val (cddr lst)))))))

(defun unambiguously-fix-dcls0 (edcls key val)
  (cond ((endp edcls)
         (list (cons 'xargs (list key val))))
        ((eq (caar edcls) 'xargs)
         (acons 'xargs (update-keyword key val (cdar edcls))
                (remove-dcls0 (cdr edcls) `(,key))))
        (t
         (cons (car edcls)
               (unambiguously-fix-dcls0 (cdr edcls) key val)))))

(defun unambiguously-fix-dcls (fives key vals)
  ;; we alter the definitions given in fives to declare key to be of
  ;; vals, such that the ith definition in fives has key set to the
  ;; ith value of vals.
  (cond ((endp fives)
         nil)
        (t
         (cons (update-nth 3 (unambiguously-fix-dcls0 (nth 3 (car fives)) key (car vals))
                           (car fives))
               (unambiguously-fix-dcls (cdr fives) key (cdr vals))))))

(defun app-lst (lst)
  ;; appends all the elements of lst together.
  (if (endp lst)
      nil
    (append (car lst) (app-lst (cdr lst)))))

(defun fives-to-defuns0 (fives)
  (if (endp fives)
      nil
    (let* ((five (car fives))
           (name (first five))
           (args (second five))
           (doc (third five))
           (dcls (fourth five))
           (body (fifth five))
           (d1 (list body))
           (d2 (if doc (cons doc d1) d1))
           (d3 (if dcls (acons 'declare dcls d2) d2)))
      (cons `(defun ,name ,args ,@d3)
            (fives-to-defuns0 (cdr fives))))))

(defun fives-to-defuns (fives)
  ;; turns a list of "fives" into defuns from which such "fives" would
  ;; be derived.
  `(with-output
    :off (summary event)
    ,(if (endp (cdr fives))
         (car (fives-to-defuns0 fives))
       (cons 'mutual-recursion
             (fives-to-defuns0 fives)))))


;; END raw definitions for CCG analysis


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; These support optional make-event expansion by events other than make-event.
; -Peter Dillinger

(defun dynamic-make-event-fn (body event-form state)
;;  (declare (xargs :mode :program))
  (make-event-fn `',body
                 nil
                 nil
                 nil
                 event-form
                 state))

;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun defun-make-event (names fives symbol-class term-method wrld event-form state)
  (if (or (eq symbol-class :program)
          (and (null (cdr names))
               (null (getprop (car names) 'recursivep nil
                              'current-acl2-world wrld))))
      (value (cond ((null (cdr names)) (car names))
                   (t names)))
    (let* ((fives0 (remove-dcls fives
                                (if (eq term-method :measure)
                                    *ccg-xargs-keywords*
                                  (list* :HINTS
                                         :MEASURE
                                         :WELL-FOUNDED-RELATION
                                         *ccg-xargs-keywords*))))
           (fives1 (unambiguously-fix-dcls fives0 :termination-method
                                           (make-list (length fives)
                                                      :initial-element :measure)))
           (fives2 (if (eq term-method :measure)
                       fives1
                     (unambiguously-fix-dcls
                      fives1
                      :MEASURE
                      (defun-redundant-get-measures fives wrld)))))
      (er-progn
       (state-global-let* ((accumulated-ttree nil)
                           (inhibit-output-lst (cons 'summary (@ inhibit-output-lst))))
                          (dynamic-make-event-fn (fives-to-defuns fives2)
                                                 event-form
                                                 state))
       (value (cond ((null (cdr names)) (car names))
                    (t names)))))))

; defines a function to bridge ACL2 and raw lisp.  if you ask ACL2 what its
; definition is, it will say "(value nil)," but if you run it, you get the
; behavior of the raw body.  there are no soundness issues with that because
; the function is flagged as permanently :program-mode only.
;
; defun-bridge is provided by my hacker stuff. -Peter

; June 16 2013 - ccg.lisp certification breaks with ACL2 6.2
; Keep this function and defuns-fn1 call in sync in ACL2 sources - harshrc

(defun-raw ccg-defuns-fn0

; WARNING: This function installs a world.  That is safe at the time of this
; writing because this function is only called by defuns-fn, where that call is
; protected by a revert-world-on-error.

  (names arglists docs pairs guards term-method measures
         ccms ;ccg
         ruler-extenders-lst mp rel
         verbose time-limit hierarchy ;ccg
         hints guard-hints std-hints
         otf-flg guard-debug guard-simplify measure-debug bodies symbol-class
         normalizeps split-types-terms new-lambda$-alist-pairs
         non-executablep
         type-prescription-lst
         #+:non-standard-analysis std-p
         ctx wrld state)
  (cond
   ((eq symbol-class :program)
    (defuns-fn-short-cut
      nil nil ; loop$-recursion-checkedp and loop$-recursion
      names docs pairs guards measures split-types-terms
      bodies
      non-executablep ; not sure about this, but seems plausible
      ctx wrld state))
   (t
    (let ((ens (ens state))
          (big-mutrec (big-mutrec names)))
      (er-let*
       ((tuple (ccg-put-induction-info names arglists
                                       term-method ;ccg specific
                                       measures
                                       ccms ;ccg
                                       ruler-extenders-lst
                                       bodies
                                       mp rel
                                       verbose ;ccg
                                       time-limit ;ccg
                                       hierarchy ;ccg
                                       hints
                                       otf-flg
                                       big-mutrec
                                       measure-debug
                                       ctx ens wrld state)))
       (defuns-fn1
         (cdr tuple) ;(car tuple) is term-method
         ens
         big-mutrec
         names
         arglists
         docs
         pairs
         guards
         guard-hints
         std-hints
         otf-flg
         guard-debug
         guard-simplify
         bodies
         symbol-class
         normalizeps
         split-types-terms
         new-lambda$-alist-pairs
         non-executablep
         type-prescription-lst
         #+:non-standard-analysis std-p
         ctx
         state))))))

(defun-bridge ccg-defuns-fn (def-lst state event-form #+:non-standard-analysis std-p)

; Important Note:  Don't change the formals of this function without
; reading the *initial-event-defmacros* discussion in axioms.lisp.

; On Guards

; When a function symbol fn is defund the user supplies a guard, g, and a
; body b.  Logically speaking, the axiom introduced for fn is

;    (fn x1...xn) = b.

; After admitting fn, the guard-related properties are set as follows:

; prop                after defun

; body                   b*
; guard                  g
; unnormalized-body      b
; type-prescription      computed from b
; symbol-class           :ideal

; * We actually normalize the above.  During normalization we may expand some
; boot-strap non-rec fns.

; In addition, we magically set the symbol-function of fn

; symbol-function        b

; and the symbol-function of *1*fn as a program which computes the logical
; value of (fn x).  However, *1*fn is quite fancy because it uses the raw body
; in the symbol-function of fn if fn is :common-lisp-compliant, and may signal
; a guard error if 'guard-checking-on is set to other than nil or :none.  See
; oneify-cltl-code for the details.

; Observe that the symbol-function after defun may be a form that
; violates the guards on primitives.  Until the guards in fn are
; checked, we cannot let raw Common Lisp evaluate fn.

; Intuitively, we think of the Common Lisp programmer intending to defun (fn
; x1...xn) to be b, and is declaring that the raw fn can be called only on
; arguments satisfying g.  The need for guards stems from the fact that there
; are many Common Lisp primitives, such as car and cdr and + and *, whose
; behavior outside of their guarded domains is unspecified.  To use these
; functions in the body of fn one must "guard" fn so that it is never called in
; a way that would lead to the violation of the primitive guards.  Thus, we
; make a formal precondition on the use of the Common Lisp program fn that the
; guard g, along with the tests along the various paths through body b, imply
; each of the guards for every subroutine in b.  We also require that each of
; the guards in g be satisfied.  This is what we mean when we say fn is
; :common-lisp-compliant.

; It is, however, often impossible to check the guards at defun time.  For
; example, if fn calls itself recursively and then gives the result to +, we
; would have to prove that the guard on + is satisfied by fn's recursive
; result, before we admit fn.  In general, induction may be necessary to
; establish that the recursive calls satisfy the guards of their masters;
; hence, it is probably also necessary for the user to formulate general lemmas
; about fn to establish those conditions.  Furthermore, guard checking is no
; longer logically necessary and hence automatically doing it at defun time may
; be a waste of time.

  :program (value nil)
  :raw
  (with-ctx-summarized
   (defun-ctx def-lst state event-form #+:non-standard-analysis std-p)
   (let ((wrld (w state))
         (def-lst0
           #+:non-standard-analysis
           (if std-p
               (non-std-def-lst def-lst)
             def-lst)
           #-:non-standard-analysis
           def-lst)
         (event-form (or event-form (list 'defuns def-lst))))
     (revert-world-on-error
      (er-let*
       ((tuple (ccg-chk-acceptable-defuns def-lst ctx wrld state
                                          #+:non-standard-analysis std-p))
        (fives (chk-defuns-tuples def-lst nil ctx wrld state)))

; Chk-acceptable-defuns puts the 'formals, 'stobjs-in and 'stobjs-out
; properties (which are necessary for the translation of the bodies).
; All other properties are put by the defuns-fn0 call below.

       (cond
        ((eq tuple 'redundant)
         (stop-redundant-event ctx state))
        (t
         (enforce-redundancy
          event-form ctx wrld
          (let ((term-method (nth 1 tuple))
                (names (nth 2 tuple))
                (arglists (nth 3 tuple))
                (docs (nth 4 tuple))
                (pairs (nth 5 tuple))
                (guards (nth 6 tuple))
                (measures (nth 7 tuple))
                (ruler-extenders-lst (nth 8 tuple))
                (mp (nth 9 tuple))
                (rel (nth 10 tuple))
                (hints (nth 11 tuple))
                (guard-hints (nth 12 tuple))
                (std-hints (nth 13 tuple))
                (otf-flg (nth 14 tuple))
                (bodies (nth 15 tuple))
                (symbol-class (nth 16 tuple))
                (normalizeps (nth 17 tuple))
                (reclassifyingp (nth 18 tuple))
                (wrld (nth 19 tuple))
                (non-executablep (nth 20 tuple))
                (guard-debug (nth 21 tuple))
                (measure-debug (nth 22 tuple))
                (split-types-terms (nth 23 tuple))
                (new-lambda$-alist-pairs (nth 24 tuple))
                (guard-simplify (nth 25 tuple))
                (type-prescription-lst (nth 26 tuple))
                (ccms (nth 27 tuple))
                (verbose (nth 28 tuple))
                (time-limit (nth 29 tuple))
                (hierarchy (nth 30 tuple)))
            (er-let*
             ((pair (ccg-defuns-fn0
                     names
                     arglists
                     docs
                     pairs
                     guards
                     term-method
                     measures
                     ccms
                     ruler-extenders-lst
                     mp
                     rel
                     verbose
                     time-limit
                     hierarchy
                     hints
                     guard-hints
                     std-hints
                     otf-flg
                     guard-debug
                     guard-simplify
                     measure-debug
                     bodies
                     symbol-class
                     normalizeps
                     split-types-terms
                     new-lambda$-alist-pairs
                     non-executablep
                     type-prescription-lst
                     #+:non-standard-analysis std-p
                     ctx
                     wrld
                     state)))

; Triple is of the form (term-method wrld . ttree), where term-method is the
; actual termination method used to prove termination.
; Pair is of the form (wrld . ttree).

             ;;--harshrc: As Daron says (where?), I changed code, to force checking a nil ttree
             ;;but ideally we shud accumulate all successful ttrees.

             (er-progn
              (chk-assumption-free-ttree nil;(cdr pair)
                                         ctx state)

              (install-event-defuns names event-form def-lst0 symbol-class
                                    reclassifyingp non-executablep pair ctx wrld
                                    state)

              (if (or (eq symbol-class :program)
                      (ld-skip-proofsp state)
                      (and (null (cdr names))
                           (null (getprop (car names)
                                          'acl2::recursivep
                                          nil
                                          'acl2::current-acl2-world
; harshrc [2014-12-29 Mon] BUGFIX wrld --> (w state)
; Using wrld is wrong, since we need to check this property in the latest world installed in state
                                          (w state)))))
                  (value (cond ((null (cdr names)) (car names))
                               (t names)))
                (defun-make-event
                  names fives symbol-class term-method
                  (car pair) event-form state)))))))))))))

; redefine defuns-fn to "be" (call) ccg-defuns-fn.
;
; redefun is provided by my hacker stuff. -Peter

; Matt K. mod, 2/5/2020: Starting with recent changes to store translate
; cert-data in a .cert file, we can get warnings
;   ".Fast alist discipline violated in HONS-GET."
; for the redefinitions of defuns-fn and defstobj-fn below.  I don't know why,
; but I believe that these are the only such new warnings when running the
; "everything" regression suite; and the fact that we're redefining defuns-fn
; make it rather unsurprising to me that we see such warnings.  So I'll simply
; turn them off!  Of course, anyone maintaining ACL2s who would like to get to
; the bottom of this is welcome to do so!
; Note that we must temporarily go into logic mode so that we don't skip the
; local event below.  (We want it to be local so that we don't export its
; effect.)
(logic) (local (set-slow-alist-action nil)) (program)

(redefun defuns-fn (def-lst state event-form #+:non-standard-analysis std-p)
         (ccg-defuns-fn def-lst state event-form #+:non-standard-analysis std-p))

(progn+touchable
 :all
 (redefun+rewrite
  defstobj-fn
  (:carpat (process-embedded-events %1%
                                    %2%
                                    %3%
                                    %4%
                                    %5%
                                    (append
                                     . %app-cdr%)
                                    . %pee-cdr%)
           :repl (process-embedded-events %1%
                                          %2%
                                          %3%
                                          %4%
                                          %5%
                                          (append
                                           '((set-termination-method :measure))
                                           . %app-cdr%)
                                          . %pee-cdr%)
           :vars (%1% %2% %3% %4% %5% %app-cdr% %pee-cdr%)
           :mult 1)))


; The defxdoc forms below were initially generated automatically from
; legacy documentation strings in this file. Nov. 2014

(include-book "xdoc/top" :dir :system)

(defxdoc ccg
  :parents (acl2-sedan proof-automation)
  :short "A powerful automated termination prover for ACL2"
  :long "<p>In order to see how the CCG analysis works, consider the following
 definition of Ackermann's function from exercise 6.15 in the ACL2
 textbook:</p>

 @({
  (defun ack (x y)
     (if (zp x)
         1
       (if (zp y)
           (if (equal x 1) 2 (+ x 2))
         (ack (ack (1- x) y) (1- y)))))

 })

 <p>ACL2 cannot automatically prove the termination of @('ack') using its
  measure-based termination proof. In order to admit the function, the user
  must supply a measure. An example measure is @('(make-ord 1 (1+ (acl2s-size
  y)) (acl2s-size x))'), which is equivalent to the ordinal @('w * (1+
  (acl2s-size y)) + (acl2s-size x)'), where @('w') is the first infinite
  ordinal.</p>

 <p>The CCG analysis, on the other hand, automatically proves termination as
 follows. Note that there are two recursive calls. These calls, along with
 their rulers (i.e. the conditions under which the recursive call is reached)
 are called <i>calling contexts</i>, or sometimes just <i>contexts</i> (for
 more on rulers, see @(see ruler-extenders)). For @('ack'), these are:</p>

 @({
  1. (ack (1- x) y) with ruler ((not (zp x)) (not (zp y))).
  2. (ack (ack (1- x) y) (1- y)) with ruler ((not (zp x)) (not (zp y))).
 })

 <p>These calling contexts are used to build a <i>calling context graph
 (CCG)</i>, from which our analysis derives its name. This graph has an edge
 from context @('c1') to context @('c2') when it is possible that execution can
 move from context @('c1') to context @('c2') in one ``step'' (i.e. without
 visiting any other contexts). For our example, we get the complete graph, with
 edges from each context to both contexts.</p>

 <p>The analysis next attempts to guess <i>calling context measures (CCMs)</i>,
 or just <i>measures</i>, for each function. These are similar to ACL2
 measures, in that they are ACL2 terms that must provably be able to evaluate
 to an ordinal value (unlike ACL2 measures, CCG currently ignores the current
 well-founded relation setting). However, functions may have multiple CCMs,
 instead of one, like ACL2, and the CCG analysis has some more sophisticated
 heuristics for guessing appropriate measures. However, there is a mechanism
 for supplying measures to the CCG analysis if you need to see @(see
 CCG-XARGS). In our example, the CCG analysis will guess the measures
 @('(acl2s-size x)'), @('(acl2s-size y)'), and @('(+ (acl2s-size x) (acl2s-size
 y))'). This last one turns out to be unimportant for the termination
 proof. However, note that the first two of these measures are components of
 the ordinal measure that we gave ACL2 to prove termination earlier. As one
 might guess, these are important for the success of our CCG analysis.</p>

 <p>Like ACL2's measure analysis, we are concerned with what happens to these
 values when a recursive call is made. However, we are concerned not just with
 decreasing measures, but also non-increasing measures. Thus, we construct
 <i>Calling Context Measure Functions (CCMFs)</i>, which tell us how one
 measure compares to another across recursive calls.</p>

 <p>In our example, note that when the recursive call of the context 1 is made,
 the new value of @('(acl2s-size x)') is less than the original value of
 @('(acl2s-size x)'). More formally, we can prove the following:</p>

 @({
  (implies (and (not (zp x))
                (not (zp y)))
           (o< (acl2s-size (1- x))
               (acl2s-size x)))
 })

 <p>For those of you that are familiar with measure-based termination proofs in
 ACL2, this should look familiar, as it has the same structure as such a
 termination proof. However, we also note the following trivial
 observation:</p>

 @({
  (implies (and (not (zp x))
                (not (zp y)))
           (o<= (acl2s-size y)
                (acl2s-size y)))
 })

 <p>That is, @('y') stays the same across this recursive call. For the other
 context, we similarly note that @('(acl2s-size y)') is decreasing. However, we
 can say nothing about the value of @('(acl2s-size x)'). The CCG algorithm does
 this analysis using queries to the theorem prover that are carefully
 restricted to limit prover time.</p>

 <p>Finally, the CCG analysis uses this local information to do a global
 analysis of what happens to values. This analysis asks the question, for every
 infinite path through our CCG, @('c_1'), @('c_2'), @('c_3'), ..., is there a
 natural number @('N') such that there is an infinite sequence of measures
 @('m_N'), @('m_(N+1)'), @('m_(N+2)'), ... such that each @('m_i') is a measure
 for the context @('c_i') (i.e. a measure for the function containing @('ci')),
 we have proven that the @('m_(i+1)') is never larger than @('m_i'), and for
 infinitely many @('i'), it is the case that we have proven that @('m_i') is
 always larger than @('m_(i+)'). That's a bit of a mouthful, but what we are
 essentially saying is that, for every possible infinite sequence of recursions
 it is the case that after some finite number of steps, we can start picking
 out measures such that they never increase and infinitely often they
 decrease. Since these measures return ordinal values, we then know that there
 can be no infinite recursions, and we are done.</p>

 <p>For our example, consider two kinds of infinite paths through our CCG:
 those that visit context 2 infinitely often, and those that don't. In the
 first case, we know that @('(acl2s-size y)') is never increasing, since a
 visit to context 1 does not change the value of @('y'), and a visit to context
 2 decreases the value of @('(acl2s-size y)'). Furthermore, since we visit
 context 2 infinitely often, we know that @('(acl2s-size y)') is infinitely
 decreasing along this path. Therefore, we have met the criteria for proving no
 such path is a valid computation. In the case in which we do not visit context
 2 infinitely often, there must be a value @('N') such that we do not visit
 context 2 any more after the @('N')th context in the path. After this, we must
 only visit context 1, which always decreases the value of @('(acl2s-size
 x)'). Therefore, no such path can be a valid computation. Since all infinite
 paths through our CCG either visit context 2 infinitely often or not, we have
 proven termination. This analysis of the local data in the global context is
 done automatically by a decision procedure.</p>

 <p>That is a brief overview of the CCG analysis. Note that, can it prove many
 functions terminating that ACL2 cannot. It also does so using simpler
 measures. In the @('ack') example, we did not require any infinite ordinal
 measures to prove termination using CCG. Intuitively, CCG is in a way putting
 together the measures for you so you don't have to think about the ordinal
 structure. Thus, even when the CCG analysis to prove termination, it is often
 easier to give it multiple simple measures and allow it to put together the
 global termination argument than to give ACL2 the entire measure so it can
 prove that it decreases every single step.</p>

 <p>To find out more about interacting and controlling the CCG analysis, see
 the topics included in this section.</p>")

(defxdoc ccg-xargs
  :parents (ccg)
  :short "Giving hints to CCG analysis via See @(see xargs)"
  :long "<p>In addition to the @(tsee xargs) provided by ACL2 for passing @(see
 hints) to function definitions, the CCG analysis enables several others for
 guiding the CCG termination analysis for a given function definition. The
 following example is nonsensical but illustrates all of these xargs:</p>

 @({
  (declare (xargs :termination-method :ccg
                  :consider-ccms ((foo x) (bar y z))
                  :consider-only-ccms ((foo x) (bar y z))
                  :ccg-print-proofs nil
                  :time-limit 120
                  :ccg-hierarchy *ccg-hierarchy-hybrid*))

  General Form:
  (xargs :key1 val1 ... :keyn valn)
 })

 <p>Where the keywords and their respective values are as shown below.</p>

 <p>Note that the :TERMINATION-METHOD @('xarg') is always valid, but the other
 @('xargs') listed above are only valid if the termination method being used
 for the given function is :CCG.</p>

 <p>@(':TERMINATION-METHOD value')<br></br>

 @('Value') here is either @(':CCG') or @(':MEASURE'). For details on the
 meaning of these settings, see the documentation for @(tsee
 set-termination-method). If this @('xarg') is given, it overrides the global
 setting for the current definition. If the current definition is part of a
 @(tsee mutual-recursion), and a @(':termination-method') is provided, it must
 match that provided by all other functions in the @('mutual-recursion').</p>

 <p>@(':CONSIDER-CCMS value') or @(':CONSIDER-ONLY-CCMS value')<br></br>

 @('Value') is a list of terms involving only the formals of the function being
 defined. Both suggest measures for the current function to the CCG
 analysis. ACL2 must be able to prove that each of these terms always evaluate
 to an ordinal see @(see ordinals). ACL2 will attempt to prove this before
 beginning the CCG analysis. The difference between @(':consider-ccms') and
 @(':consider-only-ccms') is that if @(':consider-ccms') is used, the CCG
 analysis will attempt to guess additional measures that it thinks might be
 useful for proving termination, whereas if @(':consider-only-ccms') is used,
 only the measures given will be used for the given function in the CCG
 analysis. These two @('xargs') may not be used together, and attempting to do
 so will result in an error.</p>

 <p>@(':CCG-PRINT-PROOFS value')<br></br>

 @('Value') is either @('t') or @('nil'). This is a local override of the
 @(tsee set-ccg-print-proofs) setting. See this documentation topic for
 details.</p>

 <p>@(':TIME-LIMIT value')<br></br>

 @('Value') is either a positive rational number or nil. This is a local
 override of the @(tsee set-ccg-time-limit) setting. See this documentation
 topic for details.</p>

 <p>@(':CCG-HIERARCHY value')<br></br>

 @('Value') is a CCG hierarchy. This is a local override of the @(tsee
 set-ccg-hierarchy) setting. See this documentation topic for details.</p>")

(defxdoc get-ccg-inhibit-output-lst
  :parents (ccg)
  :short "Returns the list of ``kinds'' of output that will be inhibited during CCG
analysis"
  :long "@({
  Examples:
  (get-ccg-inhibit-output-lst)
  :get-ccg-inhibit-output-lst
 })

 <p>See See @(see set-ccg-inhibit-output-lst).</p>")

(defxdoc get-ccg-print-proofs
  :parents (ccg)
  :short "Returns the setting that controls whether proof attempts are printed during
CCG analysis"
  :long "@({
  Examples:
  (get-ccg-print-proofs)
  :get-ccg-print-proofs
 })

 <p>See See @(see set-ccg-print-proofs) for details.</p>")

(defxdoc get-ccg-time-limit
  :parents (ccg)
  :short "Returns the current default ccg-time-limit setting."
  :long "@({
  Examples:
  (get-ccg-time-limit (w state))
 })

 <p>This will return the time-limit as specified by the current world.</p>

 @({
  General Form:
  (get-time-limit wrld)
 })

 <p>where @('wrld') is a @(see world). For information on the settings and
 their meaning, see @(see set-termination-method).</p>")

(defxdoc get-termination-method
  :parents (ccg)
  :short "Returns the current default termination method."
  :long "@({
  Examples:
  (get-termination-method (w state))
 })

 <p>This will return the termination-method as specified by the current
 world.</p>

 @({
  General Form:
  (get-termination-method wrld)
 })

 <p>where @('wrld') is a @(see world). For information on the settings and
 their meaning, see @(see set-termination-method).</p>")

(defxdoc set-ccg-hierarchy
  :parents (ccg)
  :short "Set the default hierarchy of techniques for CCG-based termination
analysis."
  :long "@({
  (set-ccg-hierarchy ((:built-in-clauses :equal t)
                      (:measure (:induction-depth 1))
                      ((:induction-depth 0) :EQUAL t)
                      ((:induction-depth 1) :EQUAL t)
                      ((:induction-depth 1) :ALL   t)
                      ((:induction-depth 1) :SOME  t)
                      ((:induction-depth 1) :NONE  t)
                      ((:induction-depth 1) :EQUAL nil)
                      ((:induction-depth 1) :ALL   nil)
                      ((:induction-depth 1) :SOME  nil)
                      ((:induction-depth 1) :NONE  nil)))
  :set-ccg-hierarchy ((:built-in-clauses :equal t)
                      ((:induction-depth 0) :EQUAL t)
                      ((:induction-depth 1) :EQUAL t)
                      ((:induction-depth 1) :ALL   t)
                      ((:induction-depth 1) :SOME  t)
                      ((:induction-depth 1) :NONE  t))

  General Form:
  (set-ccg-hierarchy v)
 })

 <p>where @('v') is @(':CCG-ONLY'), @(':CCG-ONLY-CPN'), @(':HYBRID'),
 @(':HYBRID-CPN'), or a non-empty list of hierarchy levels, which either have
 the form @('(pt ccm-cs cpn)') or the form @('(:measure pt)'), where @('pt') is
 either @(':built-in-clauses') or @('(:induction-depth n)') for some natural
 number @('n'), @('ccm-cs') is one of @(':EQUAL'), @(':ALL'), @(':SOME'), or
 @(':NONE'), and @('cpn') is @('t') or @('nil').</p>

 <p>Each level of the hierarchy describes techniques used to prove
 termination. Termination proofs performed after admitting this event will use
 the specified techniques in the order in which they are listed.</p>

 <p>Basically, the CCG analysis as described and illustrated at a high level in
 the documentation for @(see CCG) can potentially be very expensive. In order
 to make the analysis as efficient as possible, we use less expensive (and less
 powerful) techniques first, and resort to more powerful and expensive
 techniques only when these fail.</p>

 <p>There are three ways of varying the CCG analysis, which are represented by
 each of the three elements in a hierarchy level (levels of the form
 @('(:measure pt)') will be explained later).</p>

 <p>@('Pt') tells the CCG analysis how to limit proof attempts. The idea behind
 this is that ACL2 is designed to prove statements that the user thinks are
 true. It therefore does everything it can to prove the conjecture. As ACL2
 useres already know, this can lead to very long, or even non-terminating proof
 attempts. The CCG analysis, on the other hand, sends multiple queries to the
 theorem prover that may or may not be true, in order to improve the accuracy
 of the analysis. It is therefore necessary to reign in ACL2's proof attempts
 to keep them from taking too long. Of course, the trade-off is that, the more
 we limit ACL2's prover, the less powerful it becomes.</p>

 <p>@('Pt') can be @(':built-in-clauses'), which tells ACL2 to use only @(see
 built-in-clause)s analysis. This is a very fast, and surprisingly powerful
 proof technique. For example, the definition of Ackermann's function given in
 the documentation for @(see CCG) is solved using only this proof
 technique.</p>

 <p>@('Pt') can also be of the form @('(:induction-depth n)'), where @('n') is
 a natural number. This uses the full theorem prover, but limits it in two
 ways. First, it stops proof attempts if ACL2 has been working on a subgoal
 with no case splitting or induction for 20 steps (that is, at a goal of the
 form 1.5'20'). It also limits the <i>induction depth</i>, which describes how
 many times we allow induction goals to lead to further induction goals. For
 example, @('(:induction-depth 0)') allows no induction, while
 @('(:induction-depth 1)') allows goals of the form @('*1') or @('*2'), but
 stops if it creates a goal such as @('*1.1') or @('*2.1').</p>

 <p>@('Ccm-cs') limits which CCMs are compared using the theorem
 prover. Consider again the @('ack') example in the documentation for @(see
 CCG). All we needed was to compare the value of @('(acl2s-size x)') before and
 after the recursive call and the value of @('(acl2s-size y)') before and after
 the recursive call. We would learn nothing, and waste time with the theorem
 prover if we compared @('(acl2s-size x)') to @('(acl2s-size y)'). However,
 other times, it is important to compare CCMs with each other, for example,
 when arguments are permuted, or we are dealing with a mutual recursion.</p>

 <p>@('Ccm-cs') can be one of @(':EQUAL'), @(':ALL'), @(':SOME'), or
 @(':NONE'). These limit which CCMs we compare based on the variables they
 mention. Let @('c') be a recursive call in the body of function @('f') that
 calls function @('g'). Let @('m1') be a CCM for @('f') and @('m2') be a CCM
 for @('g'). Let @('v1') be the formals mentioned in @('m1') and @('v2') be the
 formals mentioned in @('m2'') where @('m2'') is derived from @('m2') by
 substituting the formals of @('g') with the actuals of @('c'). For example,
 consider following function:</p>

 @({
  (defun f (x)
    (if (endp x)
        0
      (1+ (f (cdr x)))))
 })

 <p>Now consider the case where @('m1') and @('m2') are both the measure
 @('(acl2s-size x)'). Then if we look at the recursive call @('(f (cdr x))') in
 the body of @('f'), then @('m2'') is the result of replacing @('x') with
 @('(cdr x)') in @('m2'), i.e., @('(acl2s-size (cdr x))').</p>

 <p>If @('ccm-cs') is @(':EQUAL') we will compare @('m1') to @('m2') if @('v1')
 and @('v2') are equal. If @('value') is @(':ALL') we will compare @('m1') to
 @('m2'') if @('v2') is a subset of @('v1'). If @('value') is @(':SOME') we
 will compare @('m1') to @('m2'') if @('v1') and @('v2') intersect. If
 @('value') is @(':NONE') we will compare @('m1') to @('m2') no matter
 what.</p>

 <p>There is one caveat to what was just said: if @('m1') and @('m2') are
 syntactically equal, then regardless of the value of @('ccm-cs') we will
 construct a CCMF that will indicate that @('(o>= m1 m2)').</p>

 <p>@('Cpn') tells us how much ruler information we will use to compare CCMs.
 Unlike ACL2's measure-based termination analysis, CCG has the ability to use
 the rulers from both the current recursive call the next recursive call when
 constructing the CCMFs. That is, instead of asking ``What happens when I make
 recursive call A?'', we can ask, ``What happens when execution moves from
 recursive call A to recursive call B?''. Using this information potentially
 strengthens the termination analysis. For a brief example, consider the
 following code:</p>

 @({
  (defun half (x)
     (if (zp x)
         0
       (1+ (half (- x 2)))))
 })

 <p>Clearly this is terminating. If we choose a measure of @('(nfix x)') we
 know that if @('x') is a positive integer, @('(nfix (- x 2))') is less than
 @('(nfix x)'). But consider the measure @('(acl2s-size x)'). The strange thing
 here is that if @('x') is 1, then @('(acl2s-size (- x 2))') is @('(acl2s-size
 -1)'), which is 1, i.e. the @('acl2s-size') of @('x'). So, the fact that we
 know that @('x') is a positive integer is not enough to show that this measure
 decreases. But notice that if @('x') is 1, we will recur just one more
 time. So, if we consider what happens when we move from the recursive call
 back to itself. In this case we know @('(and (not (zp x)) (not (zp (- x
 2))))').  Under these conditions, it is trivial for ACL2 to prove that
 @('(acl2s-size (- x 2))') is always less than @('(acl2s-size x)').

 However, this can make the CCG analysis much more expensive, since information
 about how values change from step to step are done on a per-edge, rather than
 a per-node basis in the CCG (where the nodes are the recursive calls and the
 edges indicate that execution can move from one call to another in one
 step). Thus, calculating CCMFs (how values change across recursive calls) on a
 per-edge basis rather than a per-node basis can require n^2 instead of n
 prover queries.</p>

 <p>If @('cpn') is @('t'), we will use only the ruler of the current recursive
 call to compute our CCMFs. If it is @('nil'), we will use the much more
 expensive technique of using the rulers of the current and next call.</p>

 <p>Levels of the hierarchy of the form @('(:measure pt)') specify that the CCG
 analysis is to be set aside for a step, and the traditional measure-based
 termination proof is to be attempted. Here, @('pt') has the same meaning as it
 does in a CCG hierarchy level. That is, it limits the measure proof in order
 to avoid prohibitively long termination analyses.</p>

 <p>The user may specify their own hierarchy in the form given above. The main
 restriction is that no level may be subsumed by an earlier level. That is, it
 should be the case at each level of the hierarchy, that it is possible to
 discover new information about the CCG that could help lead to a termination
 proof.</p>

 <p>In addition to constructing his or her own CCG hierarchy, the user may use
 several preset hierarchies:</p>

 @({
  :CCG-ONLY
  ((:built-in-clauses :equal t)
   ((:induction-depth 0) :EQUAL t)
   ((:induction-depth 1) :EQUAL t)
   ((:induction-depth 1) :ALL   t)
   ((:induction-depth 1) :SOME  t)
   ((:induction-depth 1) :NONE  t)
   ((:induction-depth 1) :EQUAL nil)
   ((:induction-depth 1) :ALL   nil)
   ((:induction-depth 1) :SOME  nil)
   ((:induction-depth 1) :NONE  nil))

  :CCG-ONLY-CPN
  ((:built-in-clauses :equal t)
   ((:induction-depth 0) :EQUAL t)
   ((:induction-depth 1) :EQUAL t)
   ((:induction-depth 1) :ALL   t)
   ((:induction-depth 1) :SOME  t)
   ((:induction-depth 1) :NONE  t))

  :HYBRID
  ((:built-in-clauses :equal t)
   (:measure (:induction-depth 1))
   ((:induction-depth 0) :EQUAL t)
   ((:induction-depth 1) :EQUAL t)
   ((:induction-depth 1) :ALL   t)
   ((:induction-depth 1) :SOME  t)
   ((:induction-depth 1) :NONE  t)
   ((:induction-depth 1) :EQUAL nil)
   ((:induction-depth 1) :ALL   nil)
   ((:induction-depth 1) :SOME  nil)
   ((:induction-depth 1) :NONE  nil))

  :HYBRID-CPN
  ((:built-in-clauses :equal t)
   (:measure (:induction-depth 1))
   ((:induction-depth 0) :EQUAL t)
   ((:induction-depth 1) :EQUAL t)
   ((:induction-depth 1) :ALL   t)
   ((:induction-depth 1) :SOME  t)
   ((:induction-depth 1) :NONE  t))
 })

 <p>The default hierarchy for CCG termination analysis is :CCG-ONLY.</p>")

(defxdoc set-ccg-inhibit-output-lst
  :parents (ccg)
  :short "Control output during CCG termination analysis"
  :long "@({
  Examples:
  (set-ccg-inhibit-output-lst '(query))
  (set-ccg-inhibit-output-lst '(build/refine size-change))
  (set-ccg-inhibit-output-lst *ccg-valid-output-names*) ; inhibit all ccg output
  :set-ccg-inhibit-output-lst (build/refine size-change)

  General Form:
  (set-ccg-inhibit-output-lst lst)
 })

 <p>where @('lst') is a form (which may mention @(tsee state)) that evaluates
 to a list of names, each of which is the name of one of the following
 ``kinds'' of output produced by the CCG termination analysis.</p>

 <code> query prints the goal, restrictions, and results of each prover
   query (for a discussion on displaying actual proofs, see
   @('set-ccg-display-proofs')(yet to be documented).  basics the basic CCG
   output, enough to follow along, but concise enough to keep from drowning in
   output performance performance information for the size change analysis
   build/refine the details of CCG construction and refinement size-change the
   details of size change analysis counter-example prints out a counter-example
   that can be useful for debugging failed termination proof attempts.  </code>

 <p>It is possible to inhibit each kind of output by putting the corresponding
 name into @('lst').  For example, if @(''query') is included in (the value of)
 @('lst'), then no information about individual queries is printed during CCG
 analysis.</p>

 <p>The default setting is @(''(query performance build/refine size-change)').
 That is, by default only the basic CCG information and counter-example (in the
 case of a failed proof attempt) are printed. This should hopefully be adequate
 for most users.</p>")

(defxdoc set-ccg-print-proofs
  :parents (ccg)
  :short "Controls whether proof attempts are printed during CCG analysis"
  :long "@({
  Examples:
  (set-ccg-print-proofs t)
  (set-ccg-print-proofs nil)
  :set-ccg-print-proofs t

  General Form:
  (set-ccg-print-proofs v)
 })

 <p>If @('v') is @('nil'), no proof attempts will be printed during CCG
 analysis. This is the default. If @('v') is anything but @('nil'), proofs will
 be displayed. Fair warning: there is potentially a large amount of prover
 output that might be displayed. It is probably better to use See @(see
 set-ccg-inhibit-output-lst) to un-inhibit @(''query') output to figure out
 what lemmas might be needed to get a given query to go through.</p>")

(defxdoc set-ccg-time-limit
  :parents (ccg)
  :short "Set a global time limit for CCG-based termination proofs."
  :long "@({
  Examples:
  (set-ccg-time-limit 120)  ; limits termination proofs to 120 seconds.
  (set-ccg-time-limit 53/2) ; limits termination proofs to 53/2 seconds.
  (set-ccg-time-limit nil)  ; removes any time limit for termination proofs.
 })

 <p>Introduced by the CCG analysis book, this macro sets a global time limit
 for the completion of the CCG analysis. The time limit is given as a rational
 number, signifying the number of seconds to which the CCG analysis should be
 limited, or nil, signifying that there should be no such time limit. If CCG
 has not completed its attempt to prove termination in the number of seconds
 specified, it will immediately throw an error and the definition attempt will
 fail. Note: This is an event!  It does not print the usual event summary but
 nevertheless changes the ACL2 logical @(see world) and is so recorded.</p>

 @({
   General Form:
  (set-ccg-time-limit tl)
 })

 <p>where @('tl') is a positive rational number or nil. The default is nil. If
 the time limit is nil, the CCG analysis will work as long as it needs to in
 order to complete the analysis. If the @('tl') is a positive rational number,
 all CCG analyses will be limited to @('tl') seconds.</p>

 <p>To see what the current time limit is, see @(tsee
 get-ccg-time-limit).</p>")

(defxdoc set-termination-method
  :parents (ccg)
  :short "Set the default means of proving termination."
  :long "@({
  Examples:
  (set-termination-method :ccg)
  (set-termination-method :measure)
 })

 <p>Introduced by the CCG analysis book, this macro sets the default means by
 which ACL2 will prove termination. Note: This is an event!  It does not print
 the usual event summary but nevertheless changes the ACL2 logical @(see world)
 and is so recorded.</p>

 @({
   General Form:
  (set-termination-method tm)
 })

 <p>where @('tm') is @(':CCG') or @(':MEASURE'). The default is @(':MEASURE')
 (chosen to assure compatibility with books created without CCG). The
 recommended setting is @(':CCG'). This macro is equivalent to @('(table
 acl2-defaults-table :termination-method 'tm)'), and hence is @(tsee local) to
 any @(see books) and @(tsee encapsulate) @(see events) in which it occurs; see
 @(see acl2-defaults-table).</p>

 <p>When the termination-method is set to @(':CCG'), a termination proof is
 attempted using the the hierarchical CCG algorithm <a
 href='CCG-hierarchy'>CCG-hierarchy</a>.</p>

 <p>When the termination-method is set to @(':MEASURE'), ACL2 attempts to prove
 termination using its default measure-based method. Thus, in this setting,
 ACL2's behavior is identical to that when the CCG book is not included at
 all.</p>

 <p>To see what the current termination method setting is, use @(tsee
 get-termination-method).</p>")
