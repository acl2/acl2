; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)
(set-state-ok t)

(include-book "xdoc/top" :dir :system)

(defxdoc show-induction-records
  :parents (get-event-data system-utilities)
  :short "Obtain induction data from the most recent event's evaluation"
  :long "<p>Warning: This is a low-level system utility that may change over
 time.  In fact, users are invited to improve it; see @(see community-books)
 file @('books/tools/show-induction-records.lisp')), whose code reveals details
 that may be of use programmatically.</p>

 <p>See @(see get-event-data) for a utility that returns data stored during
 evaluation of the most recent event.  That includes information about the
 inductions performed.  Here we document that information.</p>

 <p>Here is a brief summary of that information, but it may make more sense
 after seeing the example that follows.  Each induction performed during a
 proof includes the following elements.</p>

 <ul>

 <li><b>Pool-name</b>: A message (see @(see msgp)) which, when printed using
 the @('~@') directive for @(tsee fmt), provides the name of the induction
 goal.</li>

 <li><b>Suggested</b>: The term that suggests the induction scheme.</li>

 <li><b>Accommodating</b>: The list of terms which, together with the Suggested
 term, was used in producing the induction scheme.</li>

 <li><b>Runes</b>: The list of @(see rune)s contributing to the induction
 scheme.</li>

 <li><b>P-formula</b>: The expression @('(:P ...)') that represents, in the
 Scheme, the goal to be proved by induction.</li>

 <li><b>Scheme</b>: The induction scheme used.</li>

 </ul>

 <p>Consider the following example.</p>

 @({
 (thm (equal (revappend (append x y) z)
             (revappend y (revappend x z)))) 
 })

 <p>ACL2 does a proof by induction on this goal, which it calls @('*1'). which
 is the Pool-name.  The prover's output includes the following, which clearly
 corresponds to the output of @('(show-induction-records)') displayed further
 below.</p>

 @({
 We will induct according to a scheme suggested by (REVAPPEND X Z),
 while accommodating (APPEND X Y).

 These suggestions were produced using the :induction rules BINARY-APPEND
 and REVAPPEND.  If we let (:P X Y Z) denote *1 above then the induction
 scheme we'll use is
 (AND (IMPLIES (AND (NOT (ENDP X))
                    (:P (CDR X) Y (CONS (CAR X) Z)))
               (:P X Y Z))
      (IMPLIES (ENDP X) (:P X Y Z))).
 })

 <p>Here is the promised output of @('(show-induction-records)').</p>

 @({
 ACL2 !>(show-induction-records)
 ------------------------------
 Pool-name:
   *1
 Suggested:
   (REVAPPEND X Z)
 Accommodating:
   ((APPEND X Y))
 Runes:
   ((:INDUCTION BINARY-APPEND)
    (:INDUCTION REVAPPEND))
 P-formula:
   (:P X Y Z)
 Scheme:
   (AND (IMPLIES (AND (NOT (ENDP X))
                      (:P (CDR X) Y (CONS (CAR X) Z)))
                 (:P X Y Z))
        (IMPLIES (ENDP X) (:P X Y Z)))
 ACL2 !>
 })

 <p>There can be more than one induction performed during a proof.  Each of
 these produces output like that shown above, including the initial horizontal
 line.  Consider for example the following standard definitions of list append
 and reverse functions and a relevant theorem.</p>

 @({
 (defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))
 (defun rev (x) (if (consp x) (app (rev (cdr x)) (cons (car x) nil)) nil))
 (thm (true-listp (rev x)))
 })

 <p>The final @(tsee thm) event produces two inductions: a top-level induction
 called @('*1'), and a sub-induction called @('*1.1').  Below are the relevant
 parts of the proof logs, followed by the corresponding output from
 @('show-induction-records').</p>

 <p>Here is the relevant output for @('*1').</p>

 @({
 We will induct according to a scheme suggested by (REV X).

 This suggestion was produced using the :induction rule REV.  If we
 let (:P X) denote *1 above then the induction scheme we'll use is
 (AND (IMPLIES (NOT (CONSP X)) (:P X))
      (IMPLIES (AND (CONSP X) (:P (CDR X)))
               (:P X))).
 })

 <p>And here is the relevant output for @('*1.1'), which is not printed by
 default but can be retrieved using @(':')@(tsee pso)..</p>

 @({
 We will induct according to a scheme suggested by (APP RV (LIST X1)),
 while accommodating (TRUE-LISTP RV).

 These suggestions were produced using the :induction rules APP and
 TRUE-LISTP.  If we let (:P RV X1) denote *1.1 above then the induction
 scheme we'll use is
 (AND (IMPLIES (NOT (CONSP RV)) (:P RV X1))
      (IMPLIES (AND (CONSP RV) (:P (CDR RV) X1))
               (:P RV X1))).
 })

 <p>And finally, here are displays for the two inductions.</p>

 @({
 ACL2 !>(show-induction-records)
 ------------------------------
 Pool-name:
   *1
 Suggested:
   (REV X)
 Accommodating:
   NIL
 Runes:
   ((:INDUCTION REV))
 P-formula:
   (:P X)
 Scheme:
   (AND (IMPLIES (NOT (CONSP X)) (:P X))
        (IMPLIES (AND (CONSP X) (:P (CDR X)))
                 (:P X)))
 ------------------------------
 Pool-name:
   *1.1
 Suggested:
   (APP RV (LIST X1))
 Accommodating:
   ((TRUE-LISTP RV))
 Runes:
   ((:INDUCTION TRUE-LISTP)
    (:INDUCTION APP))
 P-formula:
   (:P RV X1)
 Scheme:
   (AND (IMPLIES (NOT (CONSP RV)) (:P RV X1))
        (IMPLIES (AND (CONSP RV) (:P (CDR RV) X1))
                 (:P RV X1)))
 ACL2 !>
 })")

(defun show-induction-record (rec chan state)
  (declare (xargs :guard (weak-induction-record-p rec))) ; incomplete guard
  (fms "Pool-name:~%  ~@0~|~
        Suggested:~%  ~y1~
        Accommodating:~%  ~y2~
        Runes:~%  ~y3~
        P-formula:~%  ~y4~
        Scheme:~%  ~y5"
       (list (cons #\0 (access induction-record rec :pool-name))
             (cons #\1 (access induction-record rec :suggested))
             (cons #\2 (access induction-record rec :accommodating))
             (cons #\3 (access induction-record rec :runes))
             (cons #\4 (access induction-record rec :p-formula))
             (cons #\5 (access induction-record rec :scheme)))
       chan state nil))

(defun show-induction-record-lst (recs chan sep state)
  (cond ((endp recs) (value :invisible))
        (t (pprogn (if sep (princ$ sep chan state) state) ; separator
                   (show-induction-record (car recs) chan state)
                   (show-induction-record-lst (cdr recs) chan sep state)))))

(defmacro show-induction-records (&optional
                                  (chan '(standard-co state))
                                  (sep '"------------------------------"))
  `(show-induction-record-lst
    (reverse (cdr (assoc-eq 'induction-records
                            (f-get-global 'last-event-data state))))
    ,chan ,sep state))
