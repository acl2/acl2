(in-package "ACL2")

#|

 german.lisp
 ~~~~~~~~~~~

Author: Sandip Ray
Date: Wed Oct  5 01:37:01 2005

This book represents my efforts to model the German protocol and reason about
it with ACL2.

Prelude
=======

Background
----------

Anna Slobodova recently was trying to model the German protocol an use ACL2 to
prove it correct.  That revived my interest in the protocol.  (Thanks, Anna.)
I had a version of the Murphy code of the protocol, and Rob and I had earlier
modeled it very abstractly earlier to apply predicate abstractions.  There we
wanted to see how to automate the proof.  But when Anna was doing it I thought
I might as well model the protocol as close to the Murphy code as possible and
see how much effort it is to do it in ACL2.

Note on using Quantification
----------------------------

Many of the predicates necessary for the proof of coherence [including the
property of coherence itself] can be stated easily via quantification.  But use
of quantification requires that we be prepared to use hints in the right
places.  It is unclear whether it is better to use quantification or recursive
functions in this project.  I use quantification in most places since I was
trying to get more practice at using quantifiers, in part as I plan to talk to
Matt and J about how I believe more support should be added to the use of
quantifiers.  It should be noted that although the use of quantification
requires hints, the hints were extremely mechanical.  [More comments at where I
do quantification proofs.]  I have used recursive functions for a couple of
predicates, but I only used them when using it was natural, for example when I
was only quantifying over one process index and so I could write only one
recursive function to capture the property I posit.  [I do not like to write a
number of functions defining a property if I can state the property using one
defun-sk.]  The one place where I only allow recursive functions is in defining
the functions involved in the state transition of the system.  I do so since I
expect that one might want to simulate [execute] the model and hence using
quantification appears to be "wrong" in the context.  Either way, I do not want
to advocate anything specific but the proof shows several examples of how to do
either.

Effort
------

I started modeling the protocol on Friday September 30, 2005.  I did not have
time to work on the protocol proof on Saturday.  I started the proof on Sunday,
and worked about 5 hours.  I then spent Monday October 3, and Tuesday October 4
on the proof, working about 8-9 hours each day, doing the proof and the
documentation in real time.  I was frustrated on Tuesday evening when I saw
that I had missed one subtlety of the protocol which is listed in Section 3.23.
Then I spent the night of Tuesday, from 11:30p.m. to 1:30a.m. (Wednesday) and
finished the proof.

I wrote the documentation of the prelude (that is, this part) after the proof.
The rest of the documentation was done real time while doing the proof.  The
reason I did it that way was that I wanted to document my thoughts, both so
that the script is understandable and so that if I did shelve the proof I could
get back to it easily.

After the proof was done I changed all the defthm events not involving coherent
to local so that at least including the book will work perfectly fast.  To
replay the proof do (certify-book "german") at the ACL2 prompt in an empty ACL2
session.  To include the book after certification, do (include-book
"german").  The latter should be very fast at least.


|#

; Here is the murphy code for the protocol that I had once gotten from Thomas
; Wahl.  I suspect that it is different from the code that Anna showed me,
; since see showed me properties called ctrlpropinv and datapropinv which I
; dont see in this version.  But I think possibly the basics of the two codes
; are similar in the description of the protocols.


; Const
;   n: 30;

; Type
;   Msg:   enum { null, req_sh, req_ex, inv, inv_ack, gr_sh, gr_ex };
;   State: enum { I, S, E };
;   ID:    Scalarset(n);

; Var
;   ch1: array[ID] of Msg;                  /* channel 1 */
;   ch2: array[ID] of Msg;                  /* channel 2 */
;   ch3: array[ID] of Msg;                  /* channel 3 */
;   hsl: array[ID] of boolean;              /* home_shared_list */
;   hil: array[ID] of boolean;              /* home_invalidate_list */
;   heg: boolean;                           /* home_exclusive_granted */
;   hcm: Msg;                               /* home_current_command */
;   hcc: ID;                                /* home_current_client */
;   c:   array[ID] of State;                /* distributed cache state */


; Ruleset i: ID do

;   rule "1" /* client requests shared access */
;   c[i] = I & ch1[i] = null ==>
;   begin
;     ch1[i] := req_sh;
;   end;

;   rule "2" /* client requests exclusive access */
;   c[i] = I & ch1[i] = null ==>
;   begin
;     ch1[i] := req_ex;
;   end;

;   rule "3" /* home picks new request */
;   hcm = null & ch1[i] != null ==>
;   begin
;     hcm := ch1[i];
;     ch1[i] := null;
;     hcc := i;
;     for j: ID do
;       hil[j] := hsl[j];
;     end;
;   end;

;   rule "4" /* home sends invalidate message */
;   hil[i] & ch2[i] = null & ((hcm = req_sh & heg) | hcm = req_ex) ==>
;   begin
;     ch2[i] := inv;
;     hil[i] := false;
;   end;

;   rule "5" /* home receives invalidate acknowledgement */
;   hcm != null & ch3[i] = inv_ack ==>
;   begin
;     hsl[i] := false;
;     heg := false;
;     ch3[i] := null;
;   end;

;   rule "6" /* sharer invalidates cache */
;   ch2[i] = inv & ch3[i] = null ==>
;   begin
;     ch2[i] := null;
;     ch3[i] := inv_ack;
;     c[i] := I;
;   end;

;   rule "7" /* client receives shared grant */
;   ch2[i] = gr_sh ==>
;   begin
;     c[i] := S;
;     ch2[i] := null;
;   end;

;   rule "8" /* client receives exclusive grant */
;   ch2[i] = gr_ex ==>
;   begin
;     c[i] := E;
;     ch2[i] := null;
;   end;

; end; /* ruleset */

; rule "9" /* home grants share */
;   hcm = req_sh & !heg & ch2[hcc] = null ==>
;   begin
;     hsl[hcc] := true;
;     hcm := null;
;     ch2[hcc] := gr_sh;
;   end;

; rule "10" /* home grants exclusive */
;   hcm = req_ex & (forall i: ID do hsl[i] = false end) & ch2[hcc] = null ==>
;   begin
;     hsl[hcc] := true;
;     hcm := null;
;     heg := true;
;     ch2[hcc] := gr_ex;
;   end;


; startstate
;   begin
;     for i: ID do
;       ch1[i] := null;
;       ch2[i] := null;
;       ch3[i] := null;
;       c[i] := I;
;       hsl[i] := false;
;       hil[i] := false;
;     end;
;     hcm := null;
;     hcc := undefined;
;     heg := false;
;   end;

; Invariant
;   forall i: ID do
;     c[i] = E ->
;       forall j: ID do
;         j != i -> c[j] = I
;       end
;   end


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Starting Macros and Other stuff                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now let us begin. I use the records book all over the place as it allows us
;; to conveniently model states and vectors.

(include-book "misc/records" :dir :system)

;; I define the predicate memberp below since I hate the fact that ACL2's
;; member function is not a boolean, that is, does not always return T or
;; NIL. But this might not be important anyways. I am doing it more out of
;; habit than anything else.

(defun memberp (e x)
  (cond ((endp x) NIL)
        ((equal e (first x)) T)
        (t (memberp e (rest x)))))

;; I think of the input as a record of two things, namely the index of the
;; process taking the next step, and the action to be taken by the
;; process. That is, it says which process index is being processed and which
;; action is being taken on behalf of that process.

(defmacro pid (stimulus) `(g :pid ,stimulus))
(defmacro action (stimulus) `(g :action ,stimulus))

;; I have several local variables that I need to access. I hate having to write
;; g in my code, so I define some macros to hide g. This also allows me to sort
;; of "declare" variables.

(defmacro clients (st) `(g :clients ,st))
(defmacro ch1 (st) `(g :ch1 ,st))
(defmacro ch2 (st) `(g :ch2 ,st))
(defmacro ch3 (st) `(g :ch3 ,st))
(defmacro hcm (st) `(g :hcm ,st))
(defmacro hil (st) `(g :hil ,st))
(defmacro hsl (st) `(g :hsl ,st))
(defmacro heg (st) `(g :heg ,st))
(defmacro hcc (st) `(g :hcc ,st))

;; I created this macro update for specifically allowing me to write chains to
;; s. I want to be able to write such a chain and still be able to read it!!

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))

(defmacro >st (&rest upds) `(update st ,@upds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Modeling the German Protocol                          ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Here are some functions. These are used for updating all indices together
;; when that is appropriate.

(defun set-hil-hsl (keys hil hsl)
  (if (endp keys) hil
    (s (first keys)
       (g (first keys) hsl)
       (set-hil-hsl (rest keys) hil hsl))))

(defun all-false (keys hsl)
  (if (endp keys) T
    (and (not (g (first keys) hsl))
         (all-false (rest keys) hsl))))


;; The constant constrained function (keys) below specifies the set of process
;; indices. I have left it as a constrained function so that I can conveniently
;; add hypothesis on keys as necessary (for example we might have to add that
;; keys does not contain nil, or that it is a set of natural numbers, or
;; whatever). But my goal is to prove the protocol imposing as few constraints
;; on keys as possible. To that end, whenever we need to add a constraint I
;; should add an explanatory note saying why the constraint is necessary.

(encapsulate
 (((keys) => *))
 (local (defun keys () nil)))

;; Here is the state transition function for the protocol. In the original
;; Murphy version (as per my understanding) there were rules which were akin to
;; guarded commands. That is, an action could be taken if the guard for the
;; action was satisfied. In ACL2 we model that as follows. I name each action
;; (the names being based on the comments in the Murphy code and somewhat
;; arbitrary). An input stimulus specifies what action is to be taken. That is,
;; it specifies the name of the action that the system should execute. If the
;; action's guards are satisfied then the action is taken. Otherwise the
;; execution of the action is identity.

(defun german-step (st stimulus)
  (let* ((action (action stimulus))
         (pid (pid stimulus))
         (keys (keys))
         (clients (clients st))
         (ch1 (ch1 st))
         (ch2 (ch2 st))
         (ch3 (ch3 st))
         (hcm (hcm st))
         (hsl (hsl st))
         (hil (hil st))
         (heg (heg st))
         (hcc (hcc st)))
    (if (not (memberp pid keys))
        ;; The reader might be surprised by this condition. I allow the
        ;; external stimulus to ask *any* process to take a step. In particular
        ;; that means I allow "garbage" processes. But since we are not
        ;; modeling processes joining the protocol, I am assuming that this
        ;; means when I ask a garbage process to make a step then the result is
        ;; a no-op.
        st
    (cond (;; Rule 1:
           (and (equal action :request-shared-access)
                (equal (g pid clients) :idle)
                (not ch1))
           (>st :ch1
                (s pid :req-shared-access ch1)))
          (;; Rule 2:
           (and (equal action :request-exclusive-access)
                (equal (g pid clients) :idle)
                (not ch1))
           (>st :ch1 (s pid :req-exclusive-access ch1)))
          (;; Rule 3:
           (and (equal action :pick-new-request)
                (not hcm)
                (g pid ch1))
           (>st :hcm (g pid ch1)
                :ch1 (s pid NIL ch1)
                :hcc pid
                :hil (set-hil-hsl keys hil hsl)))
          (;; Rule 4:
           (and (equal action :home-sends-invalidate)
                (g pid hil)
                (not (g pid ch2))
                (or (and (equal hcm :req-shared-access)
                         heg)
                    (equal hcm :req-exclusive-access)))
           (>st :ch2 (s pid :invalidate ch2)
                :hil (s pid NIL hil)))
          (;; Rule 5:
           (and (equal action :home-receives-invalidate)
                hcm
                (equal (g pid ch3) :invalidate-ack))
           (>st :hsl (s pid NIL hsl)
                :heg NIL
                :ch3 (s pid NIL ch3)))
          (;; Rule 6:
           (and (equal action :sharer-invalidate-cache)
                (equal (g pid ch2) :invalidate)
                (not (g pid ch3)))
           (>st :ch2 (s pid NIL ch2)
                :ch3 (s pid :invalidate-ack ch3)
                :clients (s pid :idle clients)))
          (;; Rule 7:
           (and (equal action :client-receives-shared)
                (equal (g pid ch2) :grant-shared))
           (>st :clients (s pid :shared clients)
                :ch2 (s pid NIL ch2)))
          (;; Rule 8:
           (and (equal action :client-receives-exclusive)
                (equal (g pid ch2) :grant-exclusive))
           (>st :clients (s pid :exclusive clients)
                :ch2 (s pid NIL ch2)))
          (;; Rule 9:
           (and (equal action :home-grants-shared)
                (equal hcm :req-shared-access)
                (not heg)
                (not (g hcc ch2)))
           (>st :hsl (s hcc T hsl)
                :hcm NIL
                :ch2 (s hcc :grant-shared ch2)))
          (;; Rule 10
           (and (equal action :home-grants-exclusive)
                (equal hcm :req-exclusive-access)
                (all-false keys hsl)
                (not (g hcc ch2)))
           (>st :hsl (s hcc T hsl)
                :hcm nil
                :heg T
                :ch2 (s hcc :grant-exclusive ch2)))
          (t st)))))

;; And finally the initial state (init).  All state variables are nil other
;; than the clients which are all :idle.  I dont know if this latter
;; restriction is important or not, but I tried to model it as per the Murphy
;; definition.

(defun initial-clients (keys)
  (if (endp keys) nil
    (let ((clients (initial-clients (rest keys))))
      (s (first keys) :idle clients))))

(defthm initial-clients-idle
  (implies (memberp i keys)
           (equal (g i (initial-clients keys)) :idle)))

(defun init () (s :clients (initial-clients (keys)) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: The Coherence predicate and Its proof                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OK so we have now modeled the german protocol (at least as best as I could
;; based on my interpretation of the Murphy code above).  We will now prove
;; that the german protocol has coherence.  To do so, I will define a predicate
;; called coherent and show that it is an invariant of the model.


;; How do we define coherent?  One way might be to define recursive functions
;; and such.  Since the recursive functions do not seem to provide too much
;; additional simplicity, I prefer to define it as a person doing hand-proof
;; would naturally do, namely via quantification.  Note that the predicate is
;; exactly a formalization in ACL2 of the Murphy description of the invariant.


(defun-sk coherent-processes (keys clients)
  (forall (i j)
          (implies (and (memberp i keys)
                        (memberp j keys)
                        (not (equal i j))
                        (equal (g i clients) :exclusive))
                   (equal (g j clients) :idle))))

(defun coherent (st) (coherent-processes (keys) (clients st)))

(local (defthm |initial state is coherent| (coherent (init))))

;; coherent as defined above is an invariant (or so I believe) but is of course
;; not an inductive invariant.  For example consider rule 8.  The transition
;; following rule 8 does preserve coherence, but assuming coherent for the
;; state from which the transition occurs is not sufficient.  We need more.
;; Here is how I will do it.  I will start with a set of predicates (initially
;; only the predicate coherent).  For each predicate P, in order to prove (P
;; (german-step s i)), we probably might need to assume (and (P s) (Q s)).
;; Then I have added Q to my set of predicates.  I continue this process until
;; no other predicate needs to be added to the set.  My final inductive
;; invariant then is a conjunction of all the predicates I have created so far.

;; Note: When I define a predicate we immediately prove that the predicate
;; holds for the initial state init.  This is a sanity check and also takes
;; care of the base cases of the inductive invariant proof on the fly.

;; For each predicate that I handle I will divide the proof of its invariance
;; in three parts.  The first part is what I call "default cases".  The
;; predicate holds in these cases merely since the state components which
;; govern the predicate are not modified by german-step.  For example, one
;; default case for every predicate we consider is the case where the action is
;; not a legal action.  Then according to the protocol above the system state
;; does not change.  Thus the predicate holds after the step simply because it
;; used to hold before.

;; The second case involves some property of the predicate we are checking.
;; For example, consider the situation of coherence when the sharer invalidates
;; cache.  It sets its the client to idle and hence coherence cannot change.
;; This depends on the property of coherence that setting something to :idle or
;; :shared does not change it.  I will prove this property and then handle this
;; case.

;; The third case is when the predicate P holds after a step from s principally
;; because not only P but some other predicate Q holds in s.  I will then
;; define Q (and show it holds for the initial state) and then prove this case.
;; This is the toughest part of all in an invariant proof and of course it is
;; possible that the predicates I come up with are not optimal and I realize
;; that later.  I will try to minimize the roll-back as much as possible
;; principally because I do not want to spend too much time on this system and
;; I am doing this principally to document how such a proof is done in ACL2, so
;; that the particular predicates are possibly of less importance here.

;; All right back to work.  Whenever I define something using quantification I
;; disable the definition and all associated lemmas that were introduced,
;; because I want to have control on how they are used in a proof process.  For
;; example I dont want to see a "witness" until I am ready and understand what
;; the witness means in a context.  So I deal with quantifiers principally via
;; :use hints.

(local (in-theory (disable coherent-processes coherent-processes-necc)))

;; default cases are pretty simple.
(local
 (defthm |coherent default cases|
   (implies (and (coherent st)
                 (not (equal (action stimulus) :sharer-invalidate-cache))
                 (not (equal (action stimulus) :client-receives-shared))
                 (not (equal (action stimulus) :client-receives-exclusive)))
            (coherent (german-step st stimulus)))))

;; We are now left with 6, 7, and 8.  Now 6 is easy.  In 6, a client simply
;; sets itself to :idle.  If the processes were coherent before then they would
;; still be coherent.


;; Note: This proof is a classic example of how (universal) quantification
;; proofs go.  I assume coherence and want to show that it holds after setting
;; i to :idle.  How do we do that? To understand this, let us understand
;; clearly how a (universal) quantification works.  To prove a universal
;; quantification of a property I must prove that the property holds for an
;; arbitrary object called the witness of the property.  Here the witness is a
;; pair of process indices, and what I must show is that if one is :exclusive
;; then the other is :idle.  Thus, it is convenient to think of it this way:
;; ACL2 is presenting us with two process indices and daring us to show that
;; the above property holds after I set i to :idle.  Now I of course know that
;; before setting this index coherence was holding (since I am proving an
;; implication).  Thus *before setting idle* for any two processes p and q if
;; one were exclusive then the other was idle.  Now I will basically do the
;; following.  I will ask if the index being set, that is, i, is one of the two
;; indices that acl2 is going to present me with.  If not then ACL2 is giving
;; us two other indices and thus if one is exclusive the other is shared by
;; virtue of coherence before setting.  That leaves us with two cases.  First,
;; ACL2 can claim that i is the index of an :exclusive process and dare us to
;; show that every other j is :idle.  I can dispatch this case by saying that
;; since I have just set i to :idle, i cannot be :exclusive in the first place.
;; The second is that ACL2 can claim that there is some process which is
;; exclusive and say that show that i is :idle.  This case also leaves nothing
;; to be done since I know that i is :idle.

;; The above analysis might appear to be too tedious and difficult to do every
;; time.  But it is indeed pretty mechanical.  I proved the theorem with the
;; hints below even before I really thought why I gave those hints.  The rule
;; of the thumb is as follows.  If you know that some property holds before
;; setting a process index to something then do a :cases hint on whether the
;; witness *after* the setting is the index that has been just set.  If there
;; are more than one witnesses then do a case hint on each.  For each of the
;; cases, just use the definition of the property as a hint and use the -necc
;; lemma for the previous state, setting the quantified variables (i and j in
;; this case) to be the corresponding witnesses for the variables after the
;; update.

(local
 (defthm coherent-after-setting-idle
   (implies (coherent-processes keys clients)
            (coherent-processes keys (s i :idle clients)))
   :hints
   (("Goal"
     :cases
    ((equal
      i
      (mv-nth 1
              (coherent-processes-witness keys (s i :idle clients))))
     (equal i (car (coherent-processes-witness keys (s i :idle clients))))))
    ("Subgoal 1"
    :in-theory (enable coherent-processes)
    :use
    ((:instance
      coherent-processes-necc
      (i (car (coherent-processes-witness keys (s i :idle clients))))
      (j (mv-nth 1 (coherent-processes-witness keys (s i :idle clients)))))))
    ("Subgoal 2"
     :in-theory (enable coherent-processes)
     :use
     ((:instance
       coherent-processes-necc
       (i (car (coherent-processes-witness keys (s i :idle clients))))
       (j (mv-nth 1 (coherent-processes-witness keys (s i :idle clients)))))))
    ("Subgoal 3"
     :use
     ((:instance (:definition coherent-processes)
                 (clients (s i :idle clients)))
      (:instance
       coherent-processes-necc
       (i (car (coherent-processes-witness keys (s i :idle clients))))
       (j (mv-nth 1 (coherent-processes-witness keys
                                                (s i :idle clients))))))))))


(local
 (defthm |coherent after rule 6|
   (implies (and (coherent st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (coherent (german-step st stimulus)))))


;; So we are now left with rules 7 and 8.  We need to look carefully at these
;; rules.  If the action is :client-receives-shared then why is coherent
;; preserved? The reason is that in the state when a system can execute rule 7,
;; (that is, when the channel 2 has :grant-shared in it for some client), all
;; clients are either :idle or :shared (or at least I hope so).  This fact can
;; be codified by the predicate ch2-client-invariant below.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk ch2-client-shared (ch2 keys clients)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (equal (g i ch2) :grant-shared))
                    (or (equal (g j clients) :shared)
                        (equal (g j clients) :idle))))))

(local
 (defun ch2-client-shared-invariant (st)
   (ch2-client-shared (ch2 st) (keys) (clients st))))

(local (defthm |init has ch2-shared| (ch2-client-shared-invariant (init))))

(local (in-theory (disable ch2-client-shared ch2-client-shared-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following theorem saves us some :use hints since we would often be
;; checking if a client is :exclusive.

(local
 (defthm ch2-client-shared-implies-not-exclusive
   (implies (and (ch2-client-shared ch2 keys clients)
                 (memberp i keys)
                 (memberp j keys)
                 (equal (g i ch2) :grant-shared))
            (equal (equal (g j clients) :exclusive) NIL))
   :hints (("Goal"
            :use ch2-client-shared-necc))))

(local
 (defthm coherent-after-setting-shared
   (implies (and (ch2-client-shared ch2 keys clients)
                 (memberp i keys)
                 (equal (g i ch2) :grant-shared))
            (coherent-processes keys (s j :shared clients)))
   :hints (("Goal"
            :in-theory (enable coherent-processes)
            :cases ((equal j
                           (car (coherent-processes-witness
                                 keys (s j :shared clients))))))
           ("Subgoal 2"
            :use ((:instance (:definition coherent-processes)
                             (clients (s j :shared clients))))))))

;; OK so now we can prove that execution of rule 7 gives us a coherent state.

(local
 (defthm |coherent after rule 7|
   (implies (and (ch2-client-shared-invariant st)
                 (coherent st)
                 (equal (action stimulus) :client-receives-shared))
            (coherent (german-step st stimulus)))))


;; I define the similar predicate ch2-client-exclusive-invariant that lets us
;; show coherent for rule 8.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk ch2-client-exclusive (ch2 keys clients)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (equal (g i ch2) :grant-exclusive))
                    (equal (g j clients) :idle)))))

(local
 (defun ch2-client-exclusive-invariant (st)
   (ch2-client-exclusive (ch2 st) (keys) (clients st))))
(local
 (defthm |init has ch2-exclusive| (ch2-client-exclusive-invariant (init))))

(local
 (in-theory (disable ch2-client-exclusive ch2-client-exclusive-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm ch2-exclusive-means-idle
   (implies (and (ch2-client-exclusive ch2 keys clients)
                 (memberp i keys)
                 (memberp j keys)
                 (equal (g i ch2) :grant-exclusive))
            (equal (g j clients) :idle))

   :hints (("Goal"
            :use ch2-client-exclusive-necc))))

(local
 (defthm ch2-exclusive-means-set-idle
   (implies (and (ch2-client-exclusive ch2 keys clients)
                 (memberp i keys)
                 (memberp m keys)
                 (memberp n keys)
                 (equal (g i ch2) :grant-exclusive))
            (equal (g m (s n v clients)) (if (equal m n) v :idle)))))

(local
 (defthm |ch2-exclusive causes coherence|
   (implies (and (ch2-client-exclusive ch2 keys clients)
                 (memberp i keys)
                 (equal (g i ch2) :grant-exclusive))
            (coherent-processes keys (s j :exclusive clients)))
   :hints (("Goal"
            :in-theory (enable coherent-processes)
            :cases
            ((equal
              j
              (car (coherent-processes-witness
                    keys (s j :exclusive clients)))))))))

;; Now of course rule 8 should just go through.

(local
 (defthm |coherent after rule 8|
   (implies (and (ch2-client-exclusive-invariant st)
                 (coherent st)
                 (equal (action stimulus) :client-receives-exclusive))
            (coherent (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of Coherence                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Of course we have now done the coherence, but we now have two other
;; predicates that we need to prove as invariants.  They are
;; ch2-client-shared-invariant and ch2-client-exclusive-invariant.  I must now
;; prove that these persist too, and in the process add more predicates.  I
;; will have a section for each predicate I prove (rather a subsection to
;; Section 3), and each proof will end with a comment "End Proof of ....".
;; This is principally so that I can efficiently search in emacs for the proofs
;; of the predicates I have done.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.1: Proof of ch2-client-shared-invariant                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The default cases as usual.

(local
 (defthm |ch2 shared default cases|
   (implies (and (ch2-client-shared-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (ch2-client-shared-invariant (german-step st stimulus)))))

;; Let us now first take care of sharer-invalidate-cache.  This works because
;; if I set something to :idle then nothing changes in terms of what has
;; shared.

(local
 (defthm ch2-shared-if-idle
   (implies (and (ch2-client-shared ch2 keys clients)
                 (not (equal val :grant-shared)))
            (ch2-client-shared (s i val ch2) keys (s j :idle clients)))
   :hints
   (("Goal"
     :cases
     ((equal
       i
       (car (ch2-client-shared-witness
             (s i val ch2) keys (s j :idle clients))))
      (equal
       j
       (mv-nth 1 (ch2-client-shared-witness (s i val ch2) keys
                                            (s j :idle clients))))))
    ("Subgoal 2"
     :in-theory (enable ch2-client-shared))
    ("Subgoal 1"
     :in-theory (enable ch2-client-shared))
    ("Subgoal 3"
     :use
     ((:instance (:definition ch2-client-shared)
                 (clients (s j :idle clients))
                 (ch2 (s i val ch2)))
      (:instance
       ch2-client-shared-necc
       (i (car (ch2-client-shared-witness (s i val ch2) keys
                                          (s j :idle clients))))
       (j  (mv-nth 1 (ch2-client-shared-witness (s i val ch2)
                                                keys
                                                (s j :idle clients))))))))))

(local
 (defthm |ch2-shared if sharer-invalidate|
   (implies (and (ch2-client-shared-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (ch2-client-shared-invariant (german-step st stimulus)))))

;; Now let us take the other cases in turn.  For the case
;; :home-sends-invalidate for example, we know that ch2-client-shared-invariant
;; still holds after the action if it held before.  This is because if we
;; change ch2 to something other than :grant-shared the
;; ch2-client-shared-invariant does not change.  Let us first prove this fact.

(local
 (defthm ch2-client-shared-after-arbitrary
   (implies (and (not (equal val :grant-shared))
                 (ch2-client-shared ch2 keys clients))
            (ch2-client-shared (s pid val ch2) keys clients))
   :hints (("Goal"
            :cases
            ((equal
              (car (ch2-client-shared-witness (s pid val ch2) keys clients))
              pid)))
           ("Subgoal 2"
            :use
            ((:instance (:definition ch2-client-shared)
                        (ch2 (s pid val ch2)))
             (:instance
              ch2-client-shared-necc
              (i (car (ch2-client-shared-witness (s pid val ch2) keys
                                                 clients)))
              (j (mv-nth 1 (ch2-client-shared-witness (s pid val ch2) keys
                                                      clients))))))
           ("Subgoal 1"
            :use
            ((:instance (:definition ch2-client-shared)
                        (ch2 (s pid val ch2)))
             (:instance
              ch2-client-shared-necc
              (i (car (ch2-client-shared-witness (s pid val ch2) keys
                                                 clients)))
              (j (mv-nth 1 (ch2-client-shared-witness (s pid val ch2) keys
                                                      clients)))))))))


;; While we are at it, we might also prove that if a client is set to :shared
;; then the invariant remains.

(local
 (defthm |ch2-client-shared after setting shared|
   (implies (and (ch2-client-shared ch2 keys clients)
                 (equal (g i ch2) :grant-shared))
            (ch2-client-shared ch2 keys (s j :shared clients)))
   :hints (("Goal"
            :cases
            ((equal
              j
              (mv-nth 1
                      (ch2-client-shared-witness
                       ch2 keys (s j :shared clients))))))
           ("Subgoal 2"
            :use
            ((:instance
              (:definition ch2-client-shared)
              (clients (s j :shared clients)))
             (:instance
              ch2-client-shared-necc
              (i (car (ch2-client-shared-witness
                       ch2 keys (s j :shared clients))))
              (j (mv-nth
                  1 (ch2-client-shared-witness
                     ch2
                     keys (s j :shared clients)))))))
           ("Subgoal 1"
            :use
            ((:instance
              (:definition ch2-client-shared)
              (clients (s j :shared clients)))
             (:instance
              ch2-client-shared-necc
              (i (car (ch2-client-shared-witness
                       ch2 keys (s j :shared clients))))
              (j (mv-nth
                  1 (ch2-client-shared-witness
                     ch2
                     keys (s j :shared clients))))))))))

;; OK this takes care of three of the 5 non-trivial cases of the
;; ch2-client-shared-invariant as shown below.

(local
 (defthm |ch2 shared invariant after no grants-shared set|
   (implies (and (ch2-client-shared-invariant st)
                 (memberp (action stimulus) '(:home-grants-exclusive
                                              :client-receives-shared
                                              :home-sends-invalidate)))
            (ch2-client-shared-invariant (german-step st stimulus)))))

;; That leaves us with two cases, namely :home-grants-shared and
;; :client-receives-exclusive.  Let us look at :home-grants-shared.  Why is
;; this going to satisfy ch2-client-shared-invariant? The reason is that when
;; heg is nil every client has status shared or idle.

;; I add this fact as another predicate, since this is a new fact about the
;; system that is not covered by the predicates we have created so far.  The
;; predicate is specified below.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk not-heg-clients-shared (heg keys clients)
   (forall i
           (implies (and (not heg)
                         (memberp i keys))
                    (or (equal (g i clients) :shared)
                        (equal (g i clients) :idle))))))

(local
 (defun not-heg-clients-shared-invariant (st)
   (not-heg-clients-shared (heg st) (keys) (clients st))))

(local
 (defthm |init has not-heg-shared|
   (not-heg-clients-shared-invariant (init))))

(local
 (in-theory (disable not-heg-clients-shared not-heg-clients-shared-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; And clearly if this predicate holds then ch2-client-shared holds trivially.

(local
 (defthm not-heg-clients-shared-implies-ch2-shared
   (implies (and (not-heg-clients-shared heg keys clients)
                (not heg))
            (ch2-client-shared ch2 keys clients))
   :hints (("Goal"
            :use
            ((:instance (:definition ch2-client-shared))
             (:instance
              not-heg-clients-shared-necc
              (i (mv-nth 1 (ch2-client-shared-witness ch2 keys clients)))))))))
(local
 (defthm |ch2 shared invariant after home grants shared|
   (implies (and (ch2-client-shared-invariant st)
                 (not-heg-clients-shared-invariant st)
                 (equal (action stimulus) :home-grants-shared))
            (ch2-client-shared-invariant (german-step st stimulus)))))

;; The question of grant-exclusive is more interesting.  What do we want in
;; this case? We want to say that in case of a :grant-exclusive all other
;; channels have nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk channel-nil-exclusive (ch2 keys)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (not (equal i j))
                         (equal (g i ch2) :grant-exclusive))
                    (equal (g j ch2) nil)))))

(local
 (defun channel-nil-exclusive-invariant (st)
   (channel-nil-exclusive (ch2 st) (keys))))

(local
 (defthm |init has channel-nil-exclusive|
   (channel-nil-exclusive-invariant (init))))

(local
 (in-theory (disable channel-nil-exclusive
                     channel-nil-exclusive-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Why does channel-nil-invariant allow us to prove
;; ch2-client-shared-invariant? Well, the point is that if ch2-nil-invariant
;; holds then there is no channel that has value :grant-shared.  Let us prove
;; this.

(local
 (defthm channel-nil-for-exclusiv-implies-not-anything-else
   (implies (and (channel-nil-exclusive ch2 keys)
                 (memberp i keys)
                 (equal (g i ch2) :grant-exclusive)
                 (memberp j keys))
            (equal (g j ch2)
                   (if (equal i j) :grant-exclusive nil)))
   :hints (("Goal"
            :use channel-nil-exclusive-necc))))

(local
 (defthm channel-nil-implies-ch2-client-shared
   (implies (and (channel-nil-exclusive ch2 keys)
                 (memberp i keys)
                 (not (equal a :grant-shared))
                 (equal (g i ch2) :grant-exclusive))
            (ch2-client-shared (s j a ch2)
                               keys
                               (s j b clients)))
   :hints (("Goal"
            :cases ((equal j (car (ch2-client-shared-witness
                                   (s j a ch2)
                                   keys
                                   (s j b clients))))))
           ("Subgoal 1"
            :in-theory (enable ch2-client-shared))
           ("Subgoal 2"
            :in-theory (enable ch2-client-shared)))))

(local
 (defthm  |ch2-shared after client-receives-exclusive|
   (implies (and (ch2-client-shared-invariant st)
                 (channel-nil-exclusive-invariant st)
                 (equal (action stimulus) :client-receives-exclusive))
            (ch2-client-shared-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of ch2-client-shared-invariant                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.2: Proof of ch2-client-exclusive-invariant             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |ch2 exclusive default cases|
   (implies (and (ch2-client-exclusive-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :sharer-invalidate-cache
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (ch2-client-exclusive-invariant (german-step st stimulus)))))

;; Now here is a property of ch2-client-exclusive.  If it holds for a state
;; then I can set ch2 of any process to a value other than :grant-exclusive and
;; set any client to :idle and the predicate is still going to hold.  This
;; takes care of sharer-invalidate-cache when I set ch2 to nil and the client
;; to :idle.

(local
 (defthm ch2-exclusive-if-idle
   (implies (and (ch2-client-exclusive ch2 keys clients)
                 (not (equal val :grant-exclusive)))
            (ch2-client-exclusive (s i val ch2) keys (s j :idle clients)))
   :hints
   (("Goal"
     :cases
     ((equal
       i
       (car (ch2-client-exclusive-witness
             (s i val ch2) keys (s j :idle clients))))
      (equal
       j
       (mv-nth 1 (ch2-client-exclusive-witness (s i val ch2) keys
                                               (s j :idle clients))))))
    ("Subgoal 2"
     :in-theory (enable ch2-client-exclusive))
    ("Subgoal 1"
     :in-theory (enable ch2-client-exclusive))
    ("Subgoal 3"
     :use
     ((:instance (:definition ch2-client-exclusive)
                 (clients (s j :idle clients))
                 (ch2 (s i val ch2)))
      (:instance
       ch2-client-exclusive-necc
       (i (car (ch2-client-exclusive-witness (s i val ch2) keys
                                             (s j :idle clients))))
       (j  (mv-nth 1 (ch2-client-exclusive-witness (s i val ch2)
                                                   keys
                                                   (s j :idle clients))))))))))


(local
 (defthm |ch2-exclusive if sharer-invalidate|
   (implies (and (ch2-client-exclusive-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (ch2-client-exclusive-invariant (german-step st stimulus)))))


;; Notice however, that the property above does not let us prove things for
;; (say) home-sends-invalidate.  This is because in that condition the client
;; is not changed.  So we will prove also the lemma that says that we are fine
;; if the client is not changed.  This is in fact an easier property than the
;; one we proved before, but we need to prove it anyways.  Maybe I could have
;; generalized the property above a little bit and saved myself this lemma.
;; But I dont bother since I am lazy.

(local
 (defthm ch2-client-exclusive-after-arbitrary
   (implies (and (not (equal val :grant-exclusive))
                 (ch2-client-exclusive ch2 keys clients))
            (ch2-client-exclusive (s pid val ch2) keys clients))
   :hints
   (("Goal"
     :cases
     ((equal
       (car (ch2-client-exclusive-witness (s pid val ch2) keys clients))
       pid)))
    ("Subgoal 2"
     :use
     ((:instance (:definition ch2-client-exclusive)
                 (ch2 (s pid val ch2)))
      (:instance
       ch2-client-exclusive-necc
       (i (car (ch2-client-exclusive-witness (s pid val ch2) keys clients)))
       (j  (mv-nth 1 (ch2-client-exclusive-witness
                      (s pid val ch2) keys clients))))))
    ("Subgoal 1"
     :use
     ((:instance (:definition ch2-client-exclusive)
                 (ch2 (s pid val ch2)))
      (:instance
       ch2-client-shared-necc
       (i (car (ch2-client-exclusive-witness (s pid val ch2) keys clients)))
       (j (mv-nth 1 (ch2-client-exclusive-witness
                     (s pid val ch2) keys clients)))))))))

;; This now allows us to prove that ch2-client-exclusive-invariant holds under
;; the actions :home-grants-shared and :home-sends-invalidate.

(local
 (defthm |ch2 exclusive for invalidate and shared|
   (implies (and (ch2-client-exclusive-invariant st)
                 (memberp (action stimulus)
                          '(:home-grants-shared
                            :home-sends-invalidate)))
            (ch2-client-exclusive-invariant (german-step st stimulus)))))

;; Now we are left with three cases, namely client-receives-shared,
;; client-receives-exclusive, and home-grants-exclusive.  Why do these cases
;; work? For the first I will use the property that if there is a
;; :grant-exclusive in a channel then all others have nil.  In other words I
;; would make use of the channel-nil-exclusive-invariant that I had already
;; defined.

;; Let us first do the case where client is getting shared.  Now why does
;; ch2-client-exclusive-invariant hold in this case? Well, there are two cases.
;; Suppose that there was an index having :grant-exclusive in the channel.
;; Then I know that no other channel has :grant-shared (and thus the system
;; does not take a step) so we are done.  Otherwise, there is no
;; :grant-exclusive, and thus after taking a step there is still no
;; grant-exclusive and hence we are done.

;; The analysis above suggests that we can define a predicate called
;; no-grant-exclusive to check if there is no grant-exclusive or not, and then
;; use that to prove the persistence of ch2-client-exclusive-invariant.  Notice
;; that we are defining this predicate to simplify our reasoning, but this
;; predicate follows in our cases for channel-nil-exclusive.  So this is not a
;; new predicate that goes in the definition of the inductive invariant.
;; Indeed, if I am willing to think harder and type more I can get rid of the
;; definition as well.

(local
 (defun-sk no-grant-exclusive (keys ch2)
   (forall i
           (implies (memberp i keys)
                    (not (equal (g i ch2) :grant-exclusive))))))

(local (in-theory (disable no-grant-exclusive no-grant-exclusive-necc)))

;; Now we first prove that if there is no grant-exclusive then
;; ch2-client-exclusive-invariant holds.

(local
 (defthm no-grant-exclusive-implies-ch2-exclusive
   (implies (no-grant-exclusive keys ch2)
            (ch2-client-exclusive ch2 keys clients))
   :hints
   (("Goal"
     :in-theory (enable ch2-client-exclusive)
     :use
     ((:instance
       no-grant-exclusive-necc
       (i (car (ch2-client-exclusive-witness ch2 keys clients)))))))))

;; Now we will show that if no-grant-exclusive does not hold that is, if there
;; is some process with :grant-exclusive and there is some other which has some
;; other value then ch2-client-exclusive-invariant does not hold.

(local
 (defthm not-grant-exclusive-and-something-implies-not-invariant
   (implies (and (not (no-grant-exclusive keys ch2))
                 (g i ch2)
                 (memberp i keys)
                 (not (equal (g i ch2) :grant-exclusive)))
            (equal (channel-nil-exclusive ch2 keys) NIL))
   :hints (("Goal"
            :in-theory (enable no-grant-exclusive)
            :use ((:instance channel-nil-exclusive-necc
                             (i (no-grant-exclusive-witness keys ch2))
                             (j i)))))))

;; Finally, no-grant-exclusive must mean that after setting a channel to NIL,
;; we still have that property.

(local
 (defthm no-grant-after-setting-channel
   (implies (no-grant-exclusive keys ch2)
            (no-grant-exclusive keys (s i nil ch2)))
   :hints
   (("Goal"
     :use
     ((:instance (:definition no-grant-exclusive)
                 (ch2 (s i nil ch2)))
      (:instance
       no-grant-exclusive-necc
       (i (no-grant-exclusive-witness keys (s i nil ch2))))))
    ("Goal'"
     :cases
     ((equal i (no-grant-exclusive-witness keys (s i nil ch2))))))))

;; Now of course I am done by simply splitting the two cases about whether
;; no-grants-exclusive holds or not.

(local
 (defthm |ch2 exclusive for client sharing|
   (implies (and (ch2-client-exclusive-invariant st)
                 (channel-nil-exclusive-invariant st)
                 (equal (action stimulus) :client-receives-shared))
            (ch2-client-exclusive-invariant (german-step st stimulus)))
   :hints (("Goal"
            :cases ((no-grant-exclusive (keys) (ch2 st)))))))


;; Now we are down to the two cases, which are home-grants-exclusive and
;; client-receives-exclusive.  I look at client-receives-exclusive first since
;; that is simpler.  Now when client-receives-exclusive, it sets channel to
;; nil, and client to exclusive.  We need to ensure that for all channel i if i
;; has the value :grant-exclusive then every client is :idle.  But since we are
;; setting every channel to nil, there is no channel with :grant-exclusive, and
;; therefore the invariant is trivial.

(local
 (defthm ch2-exclusive-after-ch2-nil
   (implies (and (channel-nil-exclusive ch2 keys)
                 (memberp i keys)
                 (memberp j keys)
                 (equal (g i ch2) :grant-exclusive))
            (equal (g j (s i nil ch2)) NIL))
   :hints (("Goal"
            :cases ((equal j i))))))

(local
 (defthm ch2-exclusive-after-ch2-nil-2
   (implies (and (channel-nil-exclusive ch2 keys)
                 (equal (g j ch2) :grant-exclusive)
                 (memberp j keys))
            (ch2-client-exclusive (s j nil ch2) keys (s m val clients)))
   :hints
   (("Goal"
     :cases
     ((equal
       j
       (car (ch2-client-exclusive-witness
             (s i nil ch2) keys (s m val clients))))))
    ("Subgoal 2"
     :in-theory (enable ch2-client-exclusive))
    ("Subgoal 1"
     :in-theory (enable ch2-client-exclusive)))))

(local
 (defthm |ch2 exclusive for client exclusive|
   (implies (and (ch2-client-exclusive-invariant st)
                 (channel-nil-exclusive-invariant st)
                 (equal (action stimulus) :client-receives-exclusive))
            (ch2-client-exclusive-invariant (german-step st stimulus)))))

;; The last case, namely home-grants-exclusive.  To do this one, what we need
;; to decide how home can manage to send an :invalidate in channel 2.  Of
;; course this means that all processes must have channel 2 NIL.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hsl-client (keys clients hsl)
   (if (endp keys) T
     (and (implies (not (equal (g (first keys) clients) :idle))
                   (equal (g (first keys) hsl) T))
          (hsl-client (rest keys) clients hsl)))))

(local
 (defun hsl-client-invariant (st) (hsl-client (keys) (clients st) (hsl st))))

(local
 (defthm hsl-client-set
   (implies (hsl-client keys clients hsl)
            (hsl-client keys (s i :idle clients) hsl))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm hsl-client-initial-client
   (hsl-client keys (initial-clients keys) hsl)))

(local
 (defthm |init has hsl-client|
   (hsl-client-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm hsl-ch2-and-all-false
   (implies (and (hsl-client keys clients hsl)
                 (all-false keys hsl)
                 (memberp i keys))
            (equal (g i clients) :idle))))

(local
 (defthm hsl-client-implies-ch2-exclusive
   (implies (and (hsl-client keys clients hsl)
                 (all-false keys hsl))
            (ch2-client-exclusive (s i v ch2) keys clients))
   :hints (("Goal"
            :in-theory (enable ch2-client-exclusive)))))

(local
 (defthm |ch2-exclusive for home-grants-exclusive|
   (implies (and (hsl-client-invariant st)
                 (ch2-client-exclusive-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (ch2-client-exclusive-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of ch2-client-exclusive-invariant                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right.  One more gone.  The next predicate is
;; not-heg-clients-shared-invariant.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.3: Proof of not-heg-clients-shared-invariant           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |not heg shared default cases|
   (implies (and (not-heg-clients-shared-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-exclusive))))
            (not-heg-clients-shared-invariant (german-step st stimulus)))))

;; Now comes the analysis.  At home-receives-invalidate, the heg is set to nil.
;; So why is the invariant holding here? The reason is that we can claim that
;; if ch3 has invalidate-ack then all clients are either :idle or :shared.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(local
 (defun-sk invalidate-ack-clients (clients ch3 keys)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (equal (g i ch3) :invalidate-ack))
                    (or (equal (g j clients) :idle)
                        (equal (g j clients) :shared))))))

(local
 (defun invalidate-ack-clients-invariant (st)
   (invalidate-ack-clients (clients st) (ch3 st) (keys))))

(local
 (defthm |init has invariant-ack-ch3|
   (invalidate-ack-clients-invariant (init))))

(local
 (in-theory (disable invalidate-ack-clients invalidate-ack-clients-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now I can claim that if invalidate-ack holds then
;; not-heg-clients-shared-invariant holds.

(local
 (defthm invalidate-ack-implies-not-heg
   (implies (and (invalidate-ack-clients clients ch3 keys)
                 (memberp i keys)
                 (equal (g i ch3) :invalidate-ack))
            (not-heg-clients-shared val keys clients))
   :hints
   (("Goal"
     :use
     ((:instance (:definition not-heg-clients-shared)
                 (heg val))
      (:instance
       invalidate-ack-clients-necc
       (j (not-heg-clients-shared-witness val keys clients))))))))

(local
 (defthm |heg-shared after home-receives-invalidate|
   (implies (and (not-heg-clients-shared-invariant st)
                 (invalidate-ack-clients-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (not-heg-clients-shared-invariant (german-step st stimulus)))))

;; The next case is when client receives shared.  This works because client of
;; course can receive as much shared as it wants, and nothing will happen to
;; this predicate.

(local
 (defthm not-heg-clients-shared-remains-with-shared
   (implies (and (not-heg-clients-shared heg keys clients)
                 (or (equal val :shared)
                     (equal val :idle)))
            (not-heg-clients-shared heg keys (s i val clients)))
   :hints
   (("Goal"
     :use
     ((:instance (:definition not-heg-clients-shared)
                 (clients (s i val clients)))
      (:instance
       not-heg-clients-shared-necc
       (i (not-heg-clients-shared-witness heg keys (s i val clients))))))
    ("Goal'"
     :cases
     ((equal i
             (not-heg-clients-shared-witness heg keys
                                             (s i val clients))))))))
 ;; So this should give me the case of client-receives-shared.

(local
 (defthm |heg-shared after client-receives-shared|
   (implies (and (not-heg-clients-shared-invariant st)
                 (memberp (action stimulus) '(:sharer-invalidate-cache
                                              :client-receives-shared)))
            (not-heg-clients-shared-invariant (german-step st stimulus)))))


;; What happens when client-receives-exclusive?  What I need here is that when
;; ch2 has grant-exclusive then heg is T

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(local
 (defun-sk heg-exclusive (heg keys ch2)
   (forall i
           (implies (and (memberp i keys)
                         (equal (g i ch2) :grant-exclusive))
                    heg))))

(local
 (defun heg-exclusive-invariant (st) (heg-exclusive (heg st) (keys) (ch2 st))))

(local
 (defthm |init has heg-exclusive| (heg-exclusive-invariant (init))))

(local (in-theory (disable heg-exclusive heg-exclusive-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm heg-exclusive-and-grant-implies-not-heg
   (implies (and (heg-exclusive heg keys ch2)
                 (memberp i keys)
                 (equal (g i ch2) :grant-exclusive))
            (not-heg-clients-shared heg keys (s j val clients)))
   :hints (("Goal"
            :use ((:instance (:definition not-heg-clients-shared)
                             (clients (s j val clients)))
                  (:instance heg-exclusive-necc))))))

(local
 (defthm |heg shared after client-receives-exclusive|
   (implies (and (not-heg-clients-shared-invariant st)
                 (heg-exclusive-invariant st)
                 (equal (action stimulus) :client-receives-exclusive))
            (not-heg-clients-shared-invariant (german-step st stimulus)))))

;; One more to go.  This is when home-grants-exclusive.  This is the most
;; trivial of the lot.  This holds because when home-grants-exclusive it sets
;; heg to T.

(local
 (defthm heg-implies-anything-fine
   (implies heg
            (not-heg-clients-shared heg keys clients))
   :hints (("Goal"
            :in-theory (enable not-heg-clients-shared)))))

(local
 (defthm |heg shared after home-grants-exclusive|
   (implies (and (not-heg-clients-shared-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (not-heg-clients-shared-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of ch2-client-exclusive-invariant                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right so I am done with not-heg-clients-shared-invariant.  Now I come to
;; channel-nil-exclusive-invariant.  This says that if one of the channels has
;; grant-exclusive then all other channels must be nil.  To an extent this is a
;; pretty strong statement and almost is the statement of coherence stated in
;; terms of channels.  So doing this is going to take some effort.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.4: Proof of channel-nil-exclusive-invariant            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |channel-nil-exclusive default cases|
   (implies (and (channel-nil-exclusive-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (channel-nil-exclusive-invariant (german-step st stimulus)))))

;; The next cases to consider are those in which the channel is set to nil.
;; Obviously if a channel is set to nil then nothing can change.

(local
 (defthm channel-set-to-nil-implies-channel-nil
   (implies (channel-nil-exclusive ch2 keys)
            (channel-nil-exclusive (s i nil ch2) keys))
   :hints
   (("Goal"
     :cases
     ((equal i (car (channel-nil-exclusive-witness (s i nil ch2)
                                                   keys)))
      (equal i (mv-nth 1 (channel-nil-exclusive-witness (s i nil ch2)
                                                        keys)))))
    ("Subgoal 2"
     :in-theory (enable channel-nil-exclusive))
    ("Subgoal 1"
     :in-theory (enable channel-nil-exclusive))
    ("Subgoal 3"
     :use
     ((:instance
       channel-nil-exclusive-necc
       (i  (car (channel-nil-exclusive-witness (s i nil ch2)
                                               keys)))
       (j (mv-nth 1 (channel-nil-exclusive-witness (s i nil ch2)
                                                   keys))))
      (:instance (:definition channel-nil-exclusive)
                 (ch2 (s i nil ch2))))))))

(local
 (defthm |channels-nil when ch2 set to nil|
   (implies (and (channel-nil-exclusive-invariant st)
                 (memberp (action stimulus)
                          '(:sharer-invalidate-cache
                            :client-receives-shared
                            :client-receives-exclusive)))
            (channel-nil-exclusive-invariant (german-step st stimulus)))))

;; Now comes the three interesting cases.  First is when home-grants-exclusive.
;; I should then know that all channels are nil.  This works because I know
;; that all keys are false in hsl.  As a result, all channels must be nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hsl-ch2 (hsl keys ch2)
   (if (endp keys) T
     (and (implies (g (first keys) ch2)
                   (equal (g (first keys) hsl) T))
          (hsl-ch2 hsl (rest keys) ch2)))))

(local
 (defun hsl-ch2-invariant (st) (hsl-ch2 (hsl st) (keys) (ch2 st))))

(local
 (defthm hsl-ch2-nil (hsl-ch2 nil keys nil)))

(local (defthm |init has hsl-ch2| (hsl-ch2-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm hsl-ch2-and-all-false-implies-nil
   (implies (and (hsl-ch2 hsl keys ch2)
                 (memberp i keys)
                 (all-false keys hsl))
            (equal (g i ch2) nil))))

(local
 (defthm hsl-ch2-implies-channel-nil-exclusive
   (implies (and (hsl-ch2 hsl keys ch2)
                 (all-false keys hsl))
            (channel-nil-exclusive (s i :grant-exclusive ch2) keys))
   :hints (("Goal"
            :cases ((equal i (car (channel-nil-exclusive-witness
                                   (s i :grant-exclusive ch2) keys)))))
           ("Subgoal 2"
            :in-theory (enable channel-nil-exclusive))
           ("Subgoal 1"
            :in-theory (enable channel-nil-exclusive)))))

(local
 (defthm |channel-nil-exclusive grant-exclusive|
   (implies (and (channel-nil-exclusive-invariant st)
                 (hsl-ch2-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (channel-nil-exclusive-invariant (german-step st stimulus)))))


;; What happens when home-grants-shared? We know (not heg).  Thus we
;; automatically know that there is no :grants-exclusive.  Hence we have
;; nothing to prove.

(local
 (defthm heg-exclusive-and-not-heg-implies-no-exclusive
   (implies (and (heg-exclusive heg keys ch2)
                 (not heg)
                 (not (equal val :grant-exclusive)))
            (channel-nil-exclusive (s i val ch2) keys))
   :hints (("Goal"
            :cases ((equal i (car (channel-nil-exclusive-witness
                                   (s i val ch2) keys)))))
          ("Subgoal 2"
           :use ((:instance heg-exclusive-necc
                            (heg nil)
                            (i (car (channel-nil-exclusive-witness
                                     (s i val ch2) keys)))))
           :in-theory (enable channel-nil-exclusive))
          ("Subgoal 1"
           :use ((:instance heg-exclusive-necc
                            (heg nil)
                            (i (car (channel-nil-exclusive-witness
                                     (s i val ch2) keys)))))
           :in-theory (enable channel-nil-exclusive)))))

(local
 (defthm |channel-nil-exclusive grant-shared|
   (implies (and (channel-nil-exclusive-invariant st)
                 (heg-exclusive-invariant st)
                 (equal (action stimulus) :home-grants-shared))
            (channel-nil-exclusive-invariant (german-step st stimulus)))))

;; A more interesting case, and in fact the last case for this predicate, will
;; come up now.  This is when home-sends-invalidate.  Now I should again know
;; that if (g i hil) holds and heg is T then for all j!=i (g j ch2) = NIL.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk hil-heg (keys hil ch2 heg)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (g i hil)
                         (not (equal i j))
                         heg)
                    (equal (g j ch2) nil)))))

;; BTW I believe this predicate can be generalized and made prettier.  But I am
;; trying to write it in the most brain-dead way possible, since I am too tired
;; to think too much about it....:->

(local
 (defun hil-heg-invariant (st) (hil-heg (keys) (hil st) (ch2 st) (heg st))))

(local (defthm |init has hil-heg| (hil-heg-invariant (init))))

(local (in-theory (disable hil-heg hil-heg-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm hil-heg-set-reduction
   (implies (and (hil-heg keys hil ch2 heg)
                 heg
                 (g i hil)
                 (memberp i keys)
                 (memberp j keys))
            (equal (g j (s i val ch2))
                   (if (equal i j) val nil)))
   :hints (("Goal"
            :use hil-heg-necc))))

(local
 (defthm hil-heg-channels-nil
   (implies (and (hil-heg keys hil ch2 heg)
                 heg
                 (g i hil)
                 (not (equal val :grant-exclusive))
                 (memberp i keys))
            (channel-nil-exclusive (s i val ch2) keys))
   :hints (("Goal"
            :cases ((equal i (car (channel-nil-exclusive-witness
                                   (s i val ch2) keys)))))
           ("Subgoal 1"
            :in-theory (enable channel-nil-exclusive))
           ("Subgoal 2"
            :in-theory (enable channel-nil-exclusive)))))

;; The above takes care of invalidation when heg is T.  But what do we do when
;; heg is nil? In that case we know that there is no grant-exclusive.  Thus
;; there is nothing to do.

(local
 (defthm |channels-nil for invalidate|
   (implies (and (channel-nil-exclusive-invariant st)
                 (hil-heg-invariant st)
                 (heg-exclusive-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (channel-nil-exclusive-invariant (german-step st stimulus)))
   :hints (("Goal"
            :cases ((heg st))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of channel-nil-exclusive-invariant                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Done with this predicate.  Now we move on to hsl-client-invariant.  This
;; says that for all keys if the client is not idle then hsl has the value T.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.5: Proof of hsl-client-invariant                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hsl-client default cases|
   (implies (and (hsl-client-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hsl-client-invariant (german-step st stimulus)))))

;; Of course the way hsl-client has been defined it does not matter if given
;; some hsl-client we set hsl to T.

(local
 (defthm hsl-set-reduction
   (implies (hsl-client keys clients hsl)
            (hsl-client keys clients (s i t hsl)))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

;; This takes care of cases where hsl is set to T

(local
 (defthm |hsl-clients if hsl set to T|
   (implies (and (hsl-client-invariant st)
                 (memberp (action stimulus)
                          '(:home-grants-shared
                            :home-grants-exclusive)))
            (hsl-client-invariant (german-step st stimulus)))))

;; Now we come to thhe non-trivial cases.  These are the cases in which either
;; hsl is being set to NIL or client is being set.  In either case we require
;; more predicates to show that hsl-client-invariant holds.

;; So why does the predicate hold after home-receives-invalidate? It holds
;; because if I set client to :idle I can do anything.

(local
 (defthm hsl-idle-reduction
   (implies (hsl-client keys clients hsl)
            (hsl-client keys (s i :idle clients) hsl))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-clients if clients idle|
   (implies (and (hsl-client-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (hsl-client-invariant (german-step st stimulus)))))

;; The second about when home sets hsl to nil.  Here I must carry around as
;; invariant that the corresponding client was idle.  But first let us prove
;; that if some client is idle then I can set any value to hsl.

(local
 (defthm hsl-idle-reduction-2
   (implies (and (hsl-client keys clients hsl)
                 (equal (g i clients) :idle))
            (hsl-client keys clients (s i v hsl)))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

;; Now I must posit a predicate that stipulates that the client is idle.  Why
;; do we know that? I must know that if some process has :invalidate-ack in
;; channel 3, then that client is idle.  Notice that we had previously
;; specified that *all* clients are :shared or :idle in that case.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk invalidate-ack-idle (clients keys ch3)
   (forall i
           (implies (and (memberp i keys)
                         (equal (g i ch3) :invalidate-ack))
                    (equal (g i clients) :idle)))))

(local
 (defun invalidate-ack-idle-invariant (st)
   (invalidate-ack-idle (clients st) (keys) (ch3 st))))

(local
 (defthm |init has invalidate-ack-idle|
   (invalidate-ack-idle-invariant (init))))

(local
 (in-theory (disable invalidate-ack-idle invalidate-ack-idle-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now why do I know that the client was idle? This is specified by
;; invalidate-ack.  One of the things that invalidate-ack-clients was telling
;; us is that the client which has sent invalidate-ack is :idle.

(local
 (defthm invalidate-ack-hsl
   (implies (and (invalidate-ack-idle clients keys ch3)
                 (memberp i keys)
                 (equal (g i ch3) :invalidate-ack)
                 (hsl-client keys clients hsl))
            (hsl-client keys clients (s i v hsl)))
   :hints (("Goal"
            :use ((:instance invalidate-ack-idle-necc))))))

(local
 (defthm |hsl-clients if hsl set|
   (implies (and (invalidate-ack-idle-invariant st)
                 (hsl-client-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hsl-client-invariant (german-step st stimulus)))))

;; All right now down to two more cases for this predicate.  These are cases
;; where the client receives a value either shared or exclusive.  Now in these
;; cases I know that hsl-ch2 covers me.

(local
 (defthm hsl-ch2-set-reduction
   (implies (and (hsl-ch2 hsl keys ch2)
                 (memberp i keys)
                 (g i ch2))
            (equal (g i hsl) t))))

;; I should look into this proof carefully later if time.  The proof works but
;; it does double induction, and I dont like double induction.  So there might
;; be something I can do about it.  Need to look at subgoal *1/2.

(local
 (defthm hsl-ch2-set
   (implies (and (equal (g i hsl) t)
                 (memberp i keys)
                 (hsl-client keys clients hsl))
            (hsl-client keys (s i v clients) hsl))
   :hints (("Subgoal *1/5"
            :cases ((equal i (car keys)))))))

(local
 (defthm hsl-hsl-client-packaged
   (implies (and (hsl-ch2 hsl keys ch2)
                 (hsl-client keys clients hsl)
                 (memberp i keys)
                 (g i ch2))
            (hsl-client keys (s i v clients) hsl))))

(local
 (defthm |hsl-client for client-receives|
   (implies (and (hsl-client-invariant st)
                 (hsl-ch2-invariant st)
                 (memberp (action stimulus) '(:client-receives-shared
                                              :client-receives-exclusive)))
            (hsl-client-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hsl-client-invariant                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Done with this one.  Now we move on to invalidate-ack-clients-invariant.  To
;; be honest this is is a little dicey as a predicate.  I probably should have
;; broken it up into two.  But I give it an old college try anyways.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.6: Proof of invalidate-ack-clients-invariant           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |ch3-client default cases|
   (implies (and (invalidate-ack-clients-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive))))
            (invalidate-ack-clients-invariant (german-step st stimulus)))))

;; All right now back to work.  What home does on receiving an invalidate-ack
;; is remove it.  This activity does not change the predicate.  So the first
;; case is pretty trivial.

(local
 (defthm invalidate-ack-does-not-change-if-set
   (implies (and (invalidate-ack-clients clients ch3 keys)
                 (not (equal v :invalidate-ack)))
            (invalidate-ack-clients clients (s i v ch3) keys))
   :hints
   (("Goal"
     :cases
     ((equal i
             (car (invalidate-ack-clients-witness clients (s i v ch3) keys)))))
    ("Subgoal 1"
     :in-theory (enable invalidate-ack-clients))
    ("Subgoal 2"
     :use
     ((:instance (:definition invalidate-ack-clients)
                 (ch3 (s i v ch3)))
      (:instance
       invalidate-ack-clients-necc
       (i (car (invalidate-ack-clients-witness clients (s i v ch3) keys)))
       (j (mv-nth 1 (invalidate-ack-clients-witness clients (s i v ch3)
                                                    keys)))))))))


;; This lets us prove the case of home-receives-invalidate
(local
 (defthm |invalidate-ack for home-receives-invalidate|
   (implies (and (invalidate-ack-clients-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (invalidate-ack-clients-invariant (german-step st stimulus)))))

;; All right, now how about sharer-invalidate-cache? Well, in this case we are
;; simply setting a client to idle and hence nothing can change in terms of
;; clients.  But the problem is that we are introducing an :invalidate-ack.  We
;; will do this one case at a time.  If there were an invalidate-ack around
;; then we would have no problem.  But it is now possible that there is no
;; invalidate-ack-around, and thus someone might be exclusive.  But then if I
;; do send an invalidate it should be to the exclusive guy, right? So let us
;; say that as a predicate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun invalidate-clients (ch2 clients keys)
   (if (endp keys) T
     (and (implies (equal (g (first keys) ch2) :invalidate)
                   (or (equal (g (first keys) clients) :shared)
                       (equal (g (first keys) clients) :exclusive)))
          (invalidate-clients ch2 clients (rest keys))))))

(local
 (defun invalidate-clients-invariant (st)
   (invalidate-clients (ch2 st) (clients st) (keys))))

(local
 (defthm invalidate-clients-for-nil
   (invalidate-clients nil clients keys)))

(local
 (defthm |init has invalidate-clients|
   (invalidate-clients-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now let us concentrate on what this predicate together with
;; invalidate-ack-clients tells us.  It tells us that the guy to which an
;; invalidate is sent must be shared or exclusive.  Let us prove this.

(local
 (defthm invalidate-clients-implies-shared-or-exclusive
   (implies (and (invalidate-clients ch2 clients keys)
                 (memberp i keys)
                 (equal (g i ch2) :invalidate))
            (or (equal (g i clients) :shared)
                (equal (g i clients) :exclusive)))
   :rule-classes :forward-chaining))

(local
 (defthm invalidate-and-exclusive-implies-invalidate-exclusive
   (implies (and (coherent-processes keys clients)
                 (invalidate-clients ch2 clients keys)
                 (memberp i keys)
                 (memberp j keys)
                 (equal (g i clients) :exclusive)
                 (equal (g j ch2) :invalidate))
            (equal i j))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :use ((:instance coherent-processes-necc))))))

;; Now if the guy to which invalidate is sent was exclusive then coherent will
;; kick in and show that all other processes are shared or idle.  Thus when we
;; set this to anything like idle or shared I should be in great shape.

(local
 (defthm invalidate-clients-and-coherent-implies-invalidate-ack
   (implies (and (coherent-processes keys clients)
                 (equal (g i clients) :exclusive)
                 (memberp i keys)
                 (or (equal v :shared)
                     (equal v :idle)))
            (invalidate-ack-clients (s i v clients)
                                    (s i u ch3)
                                    keys))
   :hints
   (("Goal"
     :cases ((equal i (mv-nth 1 (invalidate-ack-clients-witness (s i v clients)
                                                                (s i u ch3)
                                                                keys)))))
    ("Subgoal 1"
     :in-theory (enable invalidate-ack-clients))
    ("Subgoal 2"
     :use
     ((:instance (:definition invalidate-ack-clients)
                 (clients (s i v clients))
                 (ch3 (s i u ch3)))
      (:instance coherent-processes-necc
                 (j (mv-nth 1 (invalidate-ack-clients-witness (s i v clients)
                                                              (s i u ch3)
                                                              keys)))))))))

;; I want to now say that if invalidate-clients holds and coherent-processes
;; holds then invalidate-ack-clients holds irrespective of which client is
;; being set.  This is just packaging up the previous theorems.

(local
 (defthm invalidate-clients-and-coherent-for-exclusive
   (implies (and (invalidate-clients ch2 clients keys)
                 (coherent-processes keys clients)
                 (memberp i keys)
                 (memberp j keys)
                 (equal (g j ch2) :invalidate)
                 (equal (g i clients) :exclusive)
                 (or (equal v :shared)
                     (equal v :idle)))
            (invalidate-ack-clients (s j v clients)
                                    (s j u ch3)
                                    keys))))


;; All right, now if it is exclusive then we are done.  But it can be shared.
;; If it is shared then what do I know? Well, I should know that there is no
;; exclusive at all, from coherent-processes.  But that is not sufficient.
;; Because I need to say that if there is nothing that is exclusive then all
;; are shared or idle.  And that is not a predicate I have defined yet.  So I
;; define the predicate valid-status below to take care of that.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun valid-status (clients keys)
   (if (endp keys)
       T
     (and (or (equal (g (first keys) clients) :idle)
              (equal (g (first keys) clients) :shared)
              (equal (g (first keys) clients) :exclusive))
          (valid-status clients (rest keys))))))

(local
 (defun valid-status-invariant (st) (valid-status (clients st) (keys))))

(local
 (defthm setting-valid-does-not-change-status
   (implies (and (valid-status clients keys)
                 (or (equal v :idle)
                     (equal v :shared)
                     (equal v :exclusive)))
            (valid-status (s i v clients) keys))
   :hints (("Subgoal *1/3"
            :cases ((equal i (car keys)))))))

(local
 (defthm valid-status-in-initial (valid-status (initial-clients keys) keys)))

(local
 (defthm |init has valid status| (valid-status-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now I should know that if valid-status holds and no process has exclusive
;; then all are idle or shared.  To simplify the reasoning let us define a
;; function saying that no process is exclusive.  Of course this is not an
;; invariant.

(local
 (defun no-exclusive (keys clients)
   (if (endp keys)
       T
     (and (not (equal (g (first keys) clients) :exclusive))
          (no-exclusive (rest keys) clients)))))

;; So no-exclusive means that all are idle or shared.

(local
 (defthm no-exclusive-implies-all-idle-shared
   (implies (and (no-exclusive keys clients)
                 (valid-status clients keys)
                 (memberp i keys))
            (or (equal (g i clients) :shared)
                (equal (g i clients) :idle)))
   :rule-classes :forward-chaining))

;; And if no-exclusive does not hold then we have some process that is
;; exclusive.  Notice now how we need to (and can) define a recursive function
;; that produces the corresponding witness.  It is this witness that comes for
;; free if we do quantification.  But I have been using quantification and
;; induction in any way whatsoever depending on my mood while quantifying over
;; only one index.  So I need to "create" the witness in this case.

(local
 (defun exclusive-witness (keys clients)
   (if (endp keys) nil
     (if (equal (g (first keys) clients) :exclusive)
         (first keys)
       (exclusive-witness (rest keys) clients)))))

;; This theorem shows one way of using the witness function.  This is
;; essentially how we use existential quantifiers.  I am saying that if
;; no-exclusive does not hold then there is an index which is exclusive, in
;; particular, exclusive-witness.  This is a standard trick of simulating
;; existential quantification using recursive functions.  Later we will
;; (hopefully) see a way of using recursive functions to simulate universal
;; quantification.  The method is the same, namely define a witness for the
;; property (for a universal quantification we look for a negation of the
;; property).  Then we say that if the witness has the property then every
;; object does.  The theorem is proved using induction, and then serves to be
;; used exactly as we used the witnesses for defun-sk.

(local
 (defthm exclusive-implies-exclusive-witness
   (implies (not (no-exclusive keys clients))
            (and (memberp (exclusive-witness keys clients) keys)
                 (equal (g (exclusive-witness keys clients) clients)
                        :exclusive)))
   :rule-classes :forward-chaining))

;; Now we show that if no-exclusive holds then invalidate-ack-clients holds.

(local
 (defthm no-exclusive-implies-invalidate-ack-clients
   (implies (and (no-exclusive keys clients)
                 (valid-status clients keys)
                 (or (equal v :shared)
                     (equal v :idle)))
            (invalidate-ack-clients (s i v clients)
                                    (s i u ch3)
                                    keys))
   :hints
   (("Goal"
     :cases
     ((equal i (mv-nth 1 (invalidate-ack-clients-witness (s i v clients)
                                                         (s i u ch3)
                                                         keys)))))
    ("Subgoal 1"
     :in-theory (enable invalidate-ack-clients))
    ("Subgoal 2"
     :in-theory (enable invalidate-ack-clients)))))


;; And this solves it.

(local
 (defthm invalidate-coherent-valid-status-invalidate-ack
   (implies (and  (invalidate-clients ch2 clients keys)
                  (equal (g j ch2) :invalidate)
                  (memberp j keys)
                  (coherent-processes keys clients)
                  (valid-status clients keys)
                  (or (equal v :idle)
                      (equal v :shared)))
            (invalidate-ack-clients (s j v clients) (s j u ch3) keys))
   :hints (("Goal"
            :cases ((no-exclusive keys clients))))))

;; All right, finally done:

(local
 (defthm |invalidate-ack-clients for sharer-invalidate-cache|
   (implies (and (invalidate-ack-clients-invariant st)
                 (invalidate-clients-invariant st)
                 (coherent st)
                 (valid-status-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (invalidate-ack-clients-invariant (german-step st stimulus)))))

;; Now why does invalidate-ack-clients hold when we have a grant-shared? The
;; reason is ch2-shared-invariant which says that everybody is shared or idle
;; anyways.

(local
 (defthm ch2-shared-implies-invalidate-ack-clients
   (implies (and (ch2-client-shared ch2 keys clients)
                 (equal (g i ch2) :grant-shared)
                 (memberp i keys)
                 (or (equal v :shared)
                     (equal v :idle)))
            (invalidate-ack-clients (s i v clients) ch3 keys))
   :hints
  (("Goal"
    :cases
    ((equal i (mv-nth 1 (invalidate-ack-clients-witness (s i v clients)
                                                        ch3
                                                        keys)))))
   ("Subgoal 1"
    :in-theory (enable invalidate-ack-clients))
   ("Subgoal 2"
    :in-theory (enable invalidate-ack-clients)
    :use
    ((:instance ch2-client-shared-necc
                (j (mv-nth 1 (invalidate-ack-clients-witness (s i v clients)
                                                             ch3
                                                             keys)))))))))

(local
 (defthm |invalidate-ack-clients for grant-shared|
   (implies (and (invalidate-ack-clients-invariant st)
                 (ch2-client-shared-invariant st)
                 (equal (action stimulus) :client-receives-shared))
            (invalidate-ack-clients-invariant (german-step st stimulus)))))

;; Now the last case, which is client-receives-exclusive.  I dont like to think
;; about this one right now --- I am tired after doing the rest of the cases.
;; But I am pretty sure that if there is an invalidate-ack somewhere then there
;; cannot be a :grant-exclusive.  So for now I posit that as a predicate and go
;; on.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk invalidate-exclusive (ch3 ch2 keys)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (equal (g i ch3) :invalidate-ack))
                    (not (equal (g j ch2) :grant-exclusive))))))

(local
 (defun invalidate-exclusive-invariant (st)
   (invalidate-exclusive (ch3 st) (ch2 st) (keys))))

(local
 (defthm |init has invalidate-exclusive|
   (invalidate-exclusive-invariant (init))))

(local
 (in-theory (disable invalidate-exclusive invalidate-exclusive-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; And this predicate is going to throw away the remaining case.  Admittedly
;; this is not something I recommend.  People should analyze things carefully
;; before positing a predicate like the above.  But, well, what the heck, I
;; will do it, since I am pretty confident this is an invariant.

(local
 (defthm invalidate-exclusive-implies-grant-exclusive
   (implies (and (invalidate-exclusive ch3 ch2 keys)
                 (memberp i keys)
                 (equal (g i ch2) :grant-exclusive))
            (invalidate-ack-clients clients ch3 keys))
   :hints
   (("Goal"
     :in-theory (enable invalidate-ack-clients)
     :use
     ((:instance
       invalidate-exclusive-necc
       (j i)
       (i (car (invalidate-ack-clients-witness clients ch3 keys)))))))))

(local
 (defthm |invalidate-ack-clients after client-receives-exclusive|
   (implies (and (invalidate-ack-clients-invariant st)
                 (invalidate-exclusive-invariant st)
                 (equal (action stimulus) :client-receives-exclusive))
            (invalidate-ack-clients-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of invalidate-ack-clients-invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OK now I am just making a slight change in the order since it is night and I
;; want to do an easy predicate without thinking too much.  So I will now prove
;; valid-status-invariant first.  I will get back to the normal order of other
;; predicates tomorrow.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.7: Proof of valid-status-invariant                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |valid-status default cases|
   (implies (and (valid-status-invariant st)
                 (not (memberp (action stimulus)
                               '(:sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive))))
            (valid-status-invariant (german-step st stimulus)))))

;; I ought to have proven some lemma about non-default cases here, but I have
;; already proved that lemma while proving that valid-status holds for the
;; initial states.  Thus the rest will go thru as well.  I might as well have
;; done the whole thing in one theorem.  But I am sticking to the habit of
;; splitting proofs into default and non-default cases.

(local
 (defthm |valid-status non-default cases|
   (implies (and (valid-status-invariant st)
                 (memberp (action stimulus)
                          '(:sharer-invalidate-cache
                            :client-receives-shared
                            :client-receives-exclusive)))
            (valid-status-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of valid-status-invariant                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; That was really fast!! I will try one more for tonight then.  Let us move on
;; now to heg-exclusive-invariant.  This says that if there is a
;; :grant-exclusive in a channel then heg holds.  This one is particularly
;; easy.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.8: Proof of heg-exclusive-invariant                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |heg-exclusive defaults cases|
   (implies (and (heg-exclusive-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (heg-exclusive-invariant (german-step st stimulus)))))

;; What happens for home-grants-exclusive? This is simple.  I know that it sets
;; heg to T.  Thus nothing has to be done any more.

(local
 (defthm heg-exclusive-if-heg-T
   (implies heg
            (heg-exclusive heg keys ch2))
   :hints (("Goal"
            :in-theory (enable heg-exclusive)))))

(local
 (defthm |heg exclusive home-grants-exclusive|
   (implies (and (heg-exclusive-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (heg-exclusive-invariant (german-step st stimulus)))))

;; More interesting is the bunch of cases where ch2 is set.  The good thing is
;; that when ch2 is set to anything other than grant-exclusive we can claim
;; that the predicate simply persists.

(local
 (defthm heg-exclusive-if-channel-set
   (implies (and (heg-exclusive heg keys ch2)
                 (not (equal v :grant-exclusive)))
            (heg-exclusive heg keys (s i v ch2)))
   :hints
   (("Goal"
     :cases ((equal i (heg-exclusive-witness heg keys (s i v ch2)))))
    ("Subgoal 1"
     :in-theory (enable heg-exclusive))
    ("Subgoal 2"
     :use
     ((:instance (:definition heg-exclusive)
                 (ch2 (s i v ch2)))
      (:instance
       heg-exclusive-necc
       (i (heg-exclusive-witness heg keys (s i v ch2)))))))))

;; And this will take care of most of the cases for us.

(local
 (defthm |heg-exclusive for ch2 set|
   (implies (and (heg-exclusive-invariant st)
                 (memberp (action stimulus)
                          '(:home-sends-invalidate
                            :sharer-invalidate-cache
                            :client-receives-shared
                            :client-receives-exclusive
                            :home-grants-shared
                            :home-grants-exclusive)))
            (heg-exclusive-invariant (german-step st stimulus)))))

;; The only thorny case is when home actually gets an invalidate.  Then it sets
;; heg to nil.  Why is this ok? This is ok since we have just by serendipity
;; added the predicate invalidate-exclusive which says that there is no
;; invalidate-ack and grant-exclusive together.  Let us prove that it does it.

(local
 (defthm invalidate-exclusive-implies-not-heg-is-fine
   (implies (and (invalidate-exclusive ch3 ch2 keys)
                 (memberp i keys)
                 (equal (g i ch3) :invalidate-ack))
            (heg-exclusive heg keys ch2))
   :hints (("Goal"
            :in-theory (enable heg-exclusive)
            :use ((:instance invalidate-exclusive-necc
                             (j (heg-exclusive-witness heg keys ch2))))))))

(local
 (defthm |heg-exclusive for home-receives-invalidate|
   (implies (and (heg-exclusive-invariant st)
                 (invalidate-exclusive-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (heg-exclusive-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of heg-exclusive-invariant                          ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right, so heg-exclusive out of the way.  We get to hsl-ch2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.9: Proof of hsl-ch2-invariant                          ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hsl-ch2 default cases|
   (implies (and (hsl-ch2-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hsl-ch2-invariant (german-step st stimulus)))))

;; Here is what one has to do when recursive functions are defined (rather than
;; quantified predicates).  I am proving that hsl-ch2 holds after setting i to
;; T in clients and v in ch2.  If we defined this predicate using
;; quantification we would have used the cases hint and applied the
;; instantiation of the necc lemma on the first with the witness of the second.
;; But here we prove it using induction.  The cases hint we gave can be easily
;; understood by looking at the failed proof.  But I dont go into that here.

(local
 (defthm hsl-ch2-after-setting-hsl
   (implies (hsl-ch2 hsl keys ch2)
            (hsl-ch2 (s i T hsl) keys (s i v ch2)))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-ch2 after home sets|
   (implies (and (hsl-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:home-grants-shared
                            :home-grants-exclusive)))
            (hsl-ch2-invariant (german-step st stimulus)))))

(local
 (defthm hsl-ch2-after-ch2-nil
   (implies (hsl-ch2 hsl keys ch2)
            (hsl-ch2 hsl keys (s i nil ch2)))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-ch2 after client sets|
   (implies (and (hsl-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:sharer-invalidate-cache
                            :client-receives-shared
                            :client-receives-exclusive)))
            (hsl-ch2-invariant (german-step st stimulus)))))

;; All right now down to the two non-trivial cases for this predicate, namely
;; that home-sends-invalidate and home-receives-invalidate.  These two cases
;; involve the following consideration.  In home-sends-invalidate I add a
;; :invalidate to ch2.  So it must be that hsl is not nil.  Why is this true?
;; The reason is that the index is in hil.  So we must know that if something
;; is in hil, then it is in hsl.  This is true because the hil is set from hsl,
;; and hil is reset *before* hsl.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hil-hsl (hil hsl keys)
   (if (endp keys) T
     (and (implies (g (first keys) hil)
                   (equal (g (first keys) hsl) t))
          (hil-hsl hil hsl (rest keys))))))

(local
 (defun hil-hsl-invariant (st) (hil-hsl (hil st) (hsl st) (keys))))

(local
 (defthm hil-hsl-for-nil (hil-hsl nil nil keys)))

(local (defthm |init has hil-hsl| (hil-hsl-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; How does this work? I first know that if hil-hsl holds then every index in
;; hil must have hsl t.  When home-sends-invalidate, the hil is t and hence hsl
;; is t.  Since hsl is T anyways I dont have to think about what is added to
;; ch2.

(local
 (defthm hil-hsl-and-hil-implies-hsl
   (implies (and (hil-hsl hil hsl keys)
                 (g i hil)
                 (memberp i keys))
            (equal (g i hsl) t))))

(local
 (defthm hsl-hil-ch2
   (implies (and (hil-hsl hil hsl keys)
                 (hsl-ch2 hsl keys ch2)
                 (memberp i keys)
                 (g i hil))
            (hsl-ch2 hsl keys (s i v ch2)))
   :hints (("Subgoal *1/6"
            :cases ((equal i (car keys)))))))

;; Now I can deal with home-sends-invalidate

(local
 (defthm |hsl-ch2 after home-sends-invalidate|
   (implies (and (hsl-ch2-invariant st)
                 (hil-hsl-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hsl-ch2-invariant (german-step st stimulus)))))

;; Now I need to deal with home receives invalidate.  What this amounts to is
;; the following.  If home receives an invalidate-ack in ch3, that means that
;; the ch2 of that process is nil.  This lets us prove this.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun invalidate-ack-ch2 (ch2 ch3 keys)
   (if (endp keys) T
     (and (implies (equal (g (first keys) ch3) :invalidate-ack)
                   (not (g (first keys) ch2)))
          (invalidate-ack-ch2 ch2 ch3 (rest keys))))))

(local
 (defun invalidate-ack-ch2-invariant (st)
   (invalidate-ack-ch2 (ch2 st) (ch3 st) (keys))))

(local
 (defthm invalidate-ack-ch2-nil (invalidate-ack-ch2 nil nil keys)))

(local
 (defthm |init has invalidate-ack-ch2|
   (invalidate-ack-ch2-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Notice how I am proving these theorems by induction now.  I believe
;; induction and quantification really require the same thought and insight,
;; but ACL2 needs a little more support for quantifiers.

(local
 (defthm invalidate-ack-ch2-implies-can-set-hsl
   (implies (and (invalidate-ack-ch2 ch2 ch3 keys)
                 (hsl-ch2 hsl keys ch2)
                 (equal (g i ch3) :invalidate-ack)
                 (memberp i keys))
            (hsl-ch2 (s i v hsl) keys ch2))
   :hints (("Subgoal *1/6"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-ch2 after home receives invalidate|
   (implies (and (hsl-ch2-invariant st)
                 (invalidate-ack-ch2-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hsl-ch2-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hsl-ch2-invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now done with hsl-ch2-invariant.  On to hil-heg-invariant.  This says that
;; if heg holds and somebody is in the invalidate list then every other channel
;; must have nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.10: Proof of hil-heg-invariant                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hil-heg default cases|
   (implies (and (hil-heg-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hil-heg-invariant (german-step st stimulus)))))

;; Now the first thing we should know is that if heg is set to nil then there
;; is nothing to prove.

(local
 (defthm heg-nil-to-hil-heg
   (implies (not heg)
            (hil-heg keys hil ch2 heg))
   :hints (("Goal"
            :in-theory (enable hil-heg)))))

;; That takes care of some of the cases.

(local
 (defthm |hil-heg for receive invalidate|
   (implies (and (hil-heg-invariant st)
                 (memberp (action stimulus) '(:home-receives-invalidate
                                              :home-grants-shared)))
            (hil-heg-invariant (german-step st stimulus)))))

;; The next thing which covers a lot of cases is the statement that if I set
;; ch2 of any process to nil then hil-heg cannot be violated.

(local
 (defthm hil-heg-ch2-nil
   (implies (hil-heg keys hil ch2 heg)
            (hil-heg keys hil (s i nil ch2) heg))
   :hints
   (("Goal"
     :cases
     ((equal i (mv-nth 1 (hil-heg-witness keys hil (s i nil ch2) heg)))))
    ("Subgoal 1"
     :in-theory (enable hil-heg))
    ("Subgoal 2"
     :use
     ((:instance (:definition hil-heg)
                 (ch2 (s i nil ch2)))
      (:instance
       hil-heg-necc
       (i (car (hil-heg-witness keys hil (s i nil ch2) heg)))
       (j (mv-nth 1 (hil-heg-witness keys hil (s i nil ch2) heg)))))))))

;; This will let us prove many of the cases, in particular all that involve
;; client.

(local
 (defthm |hil-heg for clients|
   (implies (and (hil-heg-invariant st)
                 (memberp (action stimulus) '(:sharer-invalidate-cache
                                              :client-receives-shared
                                              :client-receives-exclusive)))
            (hil-heg-invariant (german-step st stimulus)))))

;; Now the more non-trivial cases which involve home picking a request, home
;; sending an invalidate, and home granting an exclusive.  Let us look at
;; home-sends-invalidate.  Suppose heg is true and no index other than one with
;; hil has ch2.  Now home sets the hil of index i to be nil.  Why is the
;; invariant ok then? It is ok since we should know at this point that no other
;; index had hil T.  But that has not been posited as a predicate yet, so I do
;; so.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk unique-hil (hil heg keys)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (g i hil)
                         (not (equal i j))
                         heg)
                    (not (g j hil))))))

(local
 (defun unique-hil-invariant (st) (unique-hil (hil st) (heg st) (keys))))

(local
 (defthm |init has unique-hil|
   (unique-hil-invariant (init))))

(local
 (in-theory (disable unique-hil unique-hil-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now I know that under heg if there is an index in hil then it is a unique
;; index.  So I should be able to set this index to anything and set the
;; corresponding channel to anything without violating the hil-heg condition.
;; Now let us come back to hil-heg.  We now want to set hil to nil under heg,
;; and know that we do not have any other index with a dangling hil.

(local
 (defthm unique-hil-implies-can-set-hil
   (implies (and (unique-hil hil heg keys)
                 (hil-heg keys hil ch2 heg)
                 heg
                 (memberp i keys)
                 (g i hil))
            (hil-heg keys (s i v hil) (s i u ch2) heg))
   :hints
   (("Goal"
     :cases
     ((equal
       i
       (car (hil-heg-witness keys (s i v hil) (s i u ch2) heg)))))
    ("Subgoal 2"
     :in-theory (enable hil-heg)
     :use
     ((:instance
       unique-hil-necc
       (j (car (hil-heg-witness keys (s i v hil) (s i u ch2) heg))))))
    ("Subgoal 1"
     :use
     ((:instance (:definition hil-heg)
                 (hil (s i v hil))
                 (ch2 (s i u ch2)))
      (:instance
       hil-heg-necc
       (i (car (hil-heg-witness keys (s i v hil) (s i u ch2) heg)))
       (j (mv-nth 1 (hil-heg-witness keys (s i v hil) (s i u ch2) heg))))
      (:instance
       unique-hil-necc
       (i (car (hil-heg-witness keys (s i v hil) (s i u ch2) heg)))
       (j (mv-nth 1 (hil-heg-witness keys (s i v hil) (s i u ch2) heg)))))))))

;; All right, now we can prove the hil-heg invariance for
;; home-sends-invalidate.

(local
 (defthm |hil-heg when home sends invalidate|
   (implies (and (hil-heg-invariant st)
                 (unique-hil-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hil-heg-invariant (german-step st stimulus)))
   :hints (("Goal"
            :cases ((heg st))))))

;; What happens when home-grants-exclusive?  Here home is setting heg to T so
;; it better damn well know that there is no non-nil value in hil.  Now home
;; knows there is no non-nil hil since there is no non-nil hsl and we have
;; hil-hsl as an invariant.

(local
 (defthm hil-hsl-and-all-false-to-not-hil
   (implies (and (hil-hsl hil hsl keys)
                 (all-false keys hsl)
                 (memberp i keys))
            (equal (g i hil) nil))))

(local
 (defthm hil-hsl-implies-hil-heg
   (implies (and (hil-hsl hil hsl keys)
                 (all-false keys hsl)
                 (memberp i keys))
            (hil-heg keys hil ch2 heg))
   :hints (("Goal"
            :in-theory (enable hil-heg)))))

(local
 (defthm |hil-heg home grants exclusive|
   (implies (and (hil-hsl-invariant st)
                 (hil-heg-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (hil-heg-invariant (german-step st stimulus)))))


;; What happens for home picking a request?  We want to say that if someone is
;; in hsl, and if heg is true then that someone must be the only one.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk hsl-heg (hsl heg keys)
   (forall (i j)
           (implies (and (memberp i keys)
                         (memberp j keys)
                         (not (equal i j))
                         heg
                         (g i hsl))
                    (not (g j hsl))))))

(local
 (defun hsl-heg-invariant (st) (hsl-heg (hsl st) (heg st) (keys))))

(local
 (defthm |init has hsl-heg-invariant|
   (hsl-heg-invariant (init))))

(local (in-theory (disable hsl-heg hsl-heg-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm hsl-ch2-set-hsl-reduction
   (implies (memberp i keys)
            (equal (g i (set-hil-hsl keys hil hsl))
                   (g i hsl)))
   :hints (("Subgoal *1/3"
            :cases ((equal i (car keys)))))))

(local
 (defthm hsl-heg-and-set-hsl-to-hil-heg
   (implies (and (hsl-heg hsl heg keys)
                 (hsl-ch2 hsl keys ch2)
                 (hil-heg keys hil ch2 heg)
                 heg)
            (hil-heg keys (set-hil-hsl keys hil hsl) ch2 heg))
   :hints
   (("Goal"
     :use
     ((:instance (:definition hil-heg)
                 (hil (set-hil-hsl keys hil hsl)))
      (:instance
       hsl-heg-necc
       (i (car (hil-heg-witness keys (set-hil-hsl keys hil hsl)
                                ch2 heg)))
       (j (mv-nth 1 (hil-heg-witness keys (set-hil-hsl keys hil hsl)
                                     ch2 heg))))
      (:instance
       hil-heg-necc
       (i (car (hil-heg-witness keys
                                (set-hil-hsl keys hil hsl)
                                ch2 heg)))
       (j (mv-nth 1 (hil-heg-witness keys
                                     (set-hil-hsl keys hil hsl)
                                     ch2 heg)))))))))


(local
 (defthm |hil-heg after home-picks-request|
   (implies (and (hil-heg-invariant st)
                 (hsl-ch2-invariant st)
                 (hsl-heg-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (hil-heg-invariant (german-step st stimulus)))
   :hints (("Goal"
            :cases ((heg st))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hil-heg-invariant                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right, so we are done with hil-heg.  This took me surprisingly longer
;; than I thought it would require.  Partly this is because I had never thought
;; of pick-new-request as anything worth consideration.  But well, nothing is
;; trivial in a protocol after all.

;; Now on to invalidate-ack-idle-invariant.  This is actually one of the more
;; trivial ones.  Let us try it.  Best to start with a simple predicate in the
;; morning.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.11: Proof of invalidate-ack-idle                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |invalidate-ack-idle default cases|
   (implies (and (invalidate-ack-idle-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive))))
            (invalidate-ack-idle-invariant (german-step st stimulus)))))

;; All right now if home makes changes ch3 nothing can happen to this
;; predicate.

(local
 (defthm invalidate-ack-idle-if-other-than-invalidate
   (implies (and (invalidate-ack-idle clients keys ch3)
                 (not (equal v :invalidate-ack)))
            (invalidate-ack-idle clients keys (s i v ch3)))
   :hints
   (("Goal"
     :cases ((equal i (invalidate-ack-idle-witness clients keys (s i v ch3)))))
    ("Subgoal 2"
     :use
     ((:instance (:definition invalidate-ack-idle)
                 (ch3 (s i v ch3)))
      (:instance
       invalidate-ack-idle-necc
       (i (invalidate-ack-idle-witness clients keys (s i v ch3))))))
    ("Subgoal 1"
     :use
     ((:instance (:definition invalidate-ack-idle)
                 (ch3 (s i v ch3)))
      (:instance
       invalidate-ack-idle-necc
       (i (invalidate-ack-idle-witness clients keys (s i v ch3)))))))))

(local
 (defthm |home-receives invalidate correctly|
   (implies (and (invalidate-ack-idle-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (invalidate-ack-idle-invariant (german-step st stimulus)))))

;; Now what happens when an invalidate-ack is introduced? This is rather
;; trivial since it happens only simultaneously with setting the client to
;; idle.  So let us prove this case.

(local
 (defthm invalidate-ack-idle-set-idle
   (implies (invalidate-ack-idle clients keys ch3)
            (invalidate-ack-idle (s i :idle clients) keys
                                 (s i :invalidate-ack ch3)))
   :hints
   (("Goal"
     :cases
     ((equal i (invalidate-ack-idle-witness (s i :idle clients)
                                            keys
                                            (s i :invalidate-ack ch3)))))
    ("Subgoal 2"
     :use
     ((:instance (:definition invalidate-ack-idle)
                 (clients (s i :idle clients))
                 (ch3 (s i :invalidate-ack ch3)))
      (:instance
       invalidate-ack-idle-necc
       (i (invalidate-ack-idle-witness (s i :idle clients)
                                       keys
                                       (s i :invalidate-ack ch3))))))
    ("Subgoal 1"
     :in-theory (enable invalidate-ack-idle)))))


(local
 (defthm |invalidate-ack-idle after sharer invalidates|
   (implies (and (invalidate-ack-idle-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (invalidate-ack-idle-invariant (german-step st stimulus)))))

;; Now what happens for grant shared and exclusive? We now set something to
;; shared or exclusive so this is relevant.  This is saved for us by
;; invalidate-ack-ch2.

(local
 (defthm invalidate-ack-ch2-does-it
   (implies (and (invalidate-ack-ch2 ch2 ch3 keys)
                 (g i ch2)
                 (memberp i keys))
            (equal (equal (g i ch3) :invalidate-ack) nil))))

(local
 (defthm not-invalidate-ack-implies-set-anything
   (implies (and (not (equal (g i ch3) :invalidate-ack))
                 (invalidate-ack-idle clients keys ch3))
            (invalidate-ack-idle (s i v clients) keys ch3))
   :hints
   (("Goal"
     :cases ((equal i (invalidate-ack-idle-witness (s i v clients) keys ch3))))
    ("Subgoal 1"
     :in-theory (enable invalidate-ack-idle))
    ("Subgoal 2"
     :use
     ((:instance (:definition invalidate-ack-idle)
                 (clients (s i v clients)))
      (:instance
       invalidate-ack-idle-necc
       (i (invalidate-ack-idle-witness (s i v clients) keys ch3))))))))

;; And putting the above two lemmas together here is the final one.

(local
 (defthm invalidate-ack-ch2-reduction
   (implies (and (invalidate-ack-ch2 ch2 ch3 keys)
                 (g i ch2)
                 (memberp i keys)
                 (invalidate-ack-idle clients keys ch3))
            (invalidate-ack-idle (s i v clients) keys ch3))))

(local
 (defthm |invalidate-ack-idle for clients|
   (implies (and (invalidate-ack-idle-invariant st)
                 (invalidate-ack-ch2-invariant st)
                 (memberp (action stimulus) '(:client-receives-shared
                                              :client-receives-exclusive)))
            (invalidate-ack-idle-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of invalidate-ack-idle-invariant                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ha ha ha.  Done with one more.  On to invalidate-ack-exclusive.  Thi states
;; that if one channel has invalidate-ack then no channel has grant-exclusive.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.12: Proof of invalidate-exclusive-invariant            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |invalidate-exclusive default cases|
   (implies (and (invalidate-exclusive-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (invalidate-exclusive-invariant (german-step st stimulus)))))

;; Now of course as long as we do not set ch2 to grant-exclusive, I can set ch2
;; to any value and it should not matter.

(local
 (defthm invalidate-exclusive-for-not-grant-exclusive
   (implies (and (invalidate-exclusive ch3 ch2 keys)
                 (not (equal v :grant-exclusive)))
            (invalidate-exclusive ch3 (s i v ch2) keys))
   :hints
   (("Goal"
     :cases ((equal i (mv-nth 1 (invalidate-exclusive-witness ch3 (s i v ch2)
                                                              keys)))))
    ("Subgoal 1"
     :use
     ((:instance (:definition invalidate-exclusive)
                 (ch2 (s i v ch2)))))
    ("Subgoal 2"
     :use
     ((:instance (:definition invalidate-exclusive)
                 (ch2 (s i v ch2)))
      (:instance
       invalidate-exclusive-necc
       (i (car (invalidate-exclusive-witness ch3 (s i v ch2) keys)))
       (j (mv-nth 1 (invalidate-exclusive-witness ch3 (s i v ch2) keys)))))))))


;; And this takes care of a number of cases, in particular all cases other than
;; home-receives-invalidate grant-exclusive and invalidate-cache.  At least so
;; I believe.  Let us see if I am right.

(local
 (defthm |invalidate-exclusive for not ch2 exclusive|
   (implies (and (invalidate-exclusive-invariant st)
                 (memberp (action stimulus)
                          '(:home-sends-invalidate
                            :client-receives-shared
                            :client-receives-exclusive
                            :home-grants-shared)))
            (invalidate-exclusive-invariant (german-step st stimulus)))))


;; Now why does it work when home receives invalidate? This is also trivial.  I
;; can set ch3 to anything other than :invalidate-ack and not violate the
;; invariant.  This is what home is doing....

(local
 (defthm invalidate-exclusive-after-not-exclusive
   (implies (and (invalidate-exclusive ch3 ch2 keys)
                 (not (equal v :invalidate-ack)))
            (invalidate-exclusive (s i v ch3) ch2 keys))
   :hints
   (("Goal"
     :cases
     ((equal i (car (invalidate-exclusive-witness (s i v ch3) ch2 keys)))))
    ("Subgoal 1"
     :use
    ((:instance (:definition invalidate-exclusive)
                (ch3 (s i v ch3)))))
    ("Subgoal 2"
     :use
     ((:instance (:definition invalidate-exclusive)
                 (ch3 (s i v ch3)))
      (:instance
       invalidate-exclusive-necc
       (i (car (invalidate-exclusive-witness (s i v ch3) ch2 keys)))
       (j (mv-nth 1 (invalidate-exclusive-witness (s i v ch3) ch2 keys)))))))))

(local
 (defthm |invalidate-exclusive after home receives invalidate|
   (implies (and (invalidate-exclusive-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (invalidate-exclusive-invariant (german-step st stimulus)))))

;; What happens when sharer invalidates the cache?  I have to claim that no
;; channel now has grant exclusive.  Why is that? Because I know that if
;; somebody does have it, then all channels have to be nil.  But all channels
;; are not nil since at least one has :invalidate.

(local
 (defthm channel-nil-exclusive-implies-invalidate-exclusive
   (implies (and (channel-nil-exclusive ch2 keys)
                 (memberp i keys)
                 (not (equal u :grant-exclusive))
                 (g i ch2))
            (invalidate-exclusive (s i v ch3) (s i u ch2) keys))
   :hints
   (("Goal"
     :cases
     ((equal i (car (invalidate-exclusive-witness (s i v ch3)
                                                  (s i u ch2)
                                                  keys)))))
    ("Subgoal 2"
     :cases ((equal i (mv-nth 1 (invalidate-exclusive-witness (s i v ch3)
                                                              (s i u ch2)
                                                              keys)))))
    ("Subgoal 2.1"
     :in-theory (enable invalidate-exclusive))
    ("Subgoal 2.2"
     :in-theory (enable invalidate-exclusive)
     :use
     ((:instance channel-nil-exclusive-necc
                 (j (car (invalidate-exclusive-witness (s i v ch3)
                                                       (s i u ch2)
                                                       keys))))))
    ("Subgoal 1"
     :cases
     ((equal i (mv-nth 1 (invalidate-exclusive-witness (s i v ch3)
                                                       (s i u ch2)
                                                       keys)))))
    ("Subgoal 1.1"
     :in-theory (enable invalidate-exclusive))
    ("Subgoal 1.2"
     :in-theory (enable invalidate-exclusive)
     :use
     ((:instance
       channel-nil-exclusive-necc
       (i (car (invalidate-exclusive-witness (s i v ch3)
                                             (s i u ch2)
                                             keys)))
       (j (mv-nth 1 (invalidate-exclusive-witness (s i v ch3)
                                                  (s i u ch2)
                                                  keys)))))))))

(local
 (defthm |invalidate-exclusive for sharer invalidate cache|
   (implies (and (invalidate-exclusive-invariant st)
                 (channel-nil-exclusive-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (invalidate-exclusive-invariant (german-step st stimulus)))))

;; Now let us consider the last case which is when somebody is granted
;; exclusive.  Why is it ok do do so and know that there was accidentally no
;; invalidate-ack around in channel 3?  The reason is that the sharer list is
;; empty.  This means that I must have another predicate, which says that if
;; somebody has something in ch3 then hsl has it recorded.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hsl-ch3 (hsl ch3 keys)
   (if (endp keys) T
     (and (implies (g (first keys) ch3)
                   (equal (g (first keys) hsl) t))
          (hsl-ch3 hsl ch3 (rest keys))))))

(local
 (defun hsl-ch3-invariant (st) (hsl-ch3 (hsl st) (ch3 st) (keys))))

(local
 (defthm hsl-ch3-for-nil (hsl-ch3 nil nil keys)))

(local
 (defthm |init has hsl-ch3-invariant|
   (hsl-ch3-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This argument is just going to go on and it is a simple argument.  It says
;; that whenever I have all-false then I am ok.  I probably have to have more
;; predicates like that all working with all-false.

(local
 (defthm hsl-ch3-all-false-to-not-ch3
   (implies (and (hsl-ch3 hsl ch3 keys)
                 (all-false keys hsl)
                 (memberp i keys))
            (equal (g i ch3) nil))))

(local
 (defthm hsl-ch3-all-false-implies-invalidate-exclusive
   (implies (and (hsl-ch3 hsl ch3 keys)
                 (all-false keys hsl))
            (invalidate-exclusive ch3 ch2 keys))
   :hints (("Goal"
            :in-theory (enable invalidate-exclusive)))))

;; So finally we get invalidate-exclusive.

(local
 (defthm |invalidate-exclusive for granting exclusive|
   (implies (and (hsl-ch3-invariant st)
                 (invalidate-exclusive-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (invalidate-exclusive-invariant (german-step st stimulus)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of invalidate-exclusive-invariant                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right now on to hil-hsl.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.13: Proof of hil-hsl-invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hil-hsl default cases|
   (implies (and (hil-hsl-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-sends-invalidate
                                 :home-receives-invalidate
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hil-hsl-invariant (german-step st stimulus)))))


;; Now consider the situation when set-hil-hsl happens.  For this to go thru, I
;; need the fact that everything in hil is a boolean.  This is because I just
;; said that the index in hil is not nil, but required that the index in hsl is
;; t.  The reason why I chose this is because home checks if (g i hil) but not
;; if (equal (g i hil) T) on certain occasions.  Anyhow the predicate is not
;; difficult to define and I do not want to belabor the point.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hsl-boolean (hsl keys)
   (if (endp keys) T
     (and (booleanp (g (first keys) hsl))
          (hsl-boolean hsl (rest keys))))))

(local
 (defun hsl-boolean-invariant (st) (hsl-boolean (hsl st) (keys))))

(local
 (defthm hsl-boolean-for-nil (hsl-boolean nil keys)))

(local
 (defthm |init has hsl-boolean| (hsl-boolean-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; And now some obvious theorems to get the proof to go thru for
;; pick-new-request.

(local
 (defthm hil-hsl-memberp
   (implies (and (memberp i keys)
                 (hsl-boolean hsl keys)
                 (equal v (g i hsl))
                 (hil-hsl hil hsl keys))
            (hil-hsl (s i v hil) hsl keys))
   :hints (("Subgoal *1/6"
            :cases ((equal i (car keys)))))))


(local
 (defthm hil-hsl-not-memberp
   (implies (and (not (memberp i keys))
                 (hil-hsl hil hsl keys))
            (hil-hsl (s i v hil) hsl keys))))

(local
 (defthm hil-hsl-set-hil-hsl
   (implies (and (hil-hsl hil hsl keys)
                 (hsl-boolean hsl keys))
            (hil-hsl (set-hil-hsl keys hil hsl) hsl keys))
   :hints (("Subgoal *1/4"
            :cases ((memberp (car keys) (cdr keys)))))))

;; Now I can do the pick new request.

(local
 (defthm |hil-hsl after picking request|
   (implies (and (hil-hsl-invariant st)
                 (hsl-boolean-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (hil-hsl-invariant (german-step st stimulus)))))

;; Let us do home-sends-invalidate now.  This involves showing that if hil is
;; set to nil then hil-hsl does not change.

(local
 (defthm hil-hsl-after-hil-nil
   (implies (hil-hsl hil hsl keys)
            (hil-hsl (s i nil hil) hsl keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-hsl after invalidating|
   (implies (and (hil-hsl-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hil-hsl-invariant (german-step st stimulus)))))

;; How about when home receives an invalidate? Here I must know that the index
;; we are talking about is not in hil in the first place and therefore it does
;; not matter that we set hsl to nil.  For this we need a new predicate that
;; says that if something has invalidate-ack then its hil is nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hil-invalidate (hil ch3 keys)
   (if (endp keys) T
     (and (implies (equal (g (first keys) ch3) :invalidate-ack)
                   (not (g (first keys) hil)))
          (hil-invalidate hil ch3 (rest keys))))))

(local
 (defun hil-invalidate-invariant (st)
   (hil-invalidate (hil st) (ch3 st) (keys))))

(local
 (defthm hil-invalidate-for-nil (hil-invalidate nil nil keys)))

(local
 (defthm |init has hil invalidate| (hil-invalidate-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now why does it work out for home receiving an invalidate? The reason is
;; rather odd.  I know that ch3 is not nil.  Thus hsl must be T and hence it
;; does not matter what I set hil to.

(local
 (defthm hil-hsl-after-setting-hil
   (implies (and (hil-hsl hil hsl keys)
                 (hil-invalidate hil ch3 keys)
                 hcm
                 (equal (g i ch3) :invalidate-ack))
            (hil-hsl hil (s i v hsl) keys))
   :hints (("Goal"
            :do-not '(eliminate-destructors generalize fertilize))
           ("Subgoal *1/5"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-hsl after home-receives-invalidate|
   (implies (and (hil-hsl-invariant st)
                 (hil-invalidate-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hil-hsl-invariant (german-step st stimulus)))))

;; And finally to the last cases of hil-hsl.  These are when hsl is set to T.
;; All I care about is that if I set hsl to T then nothing changes.

(local
 (defthm hil-hsl-after-setting-hsl
   (implies (hil-hsl hil hsl keys)
            (hil-hsl hil (s i T hsl) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-hsl after granting|
   (implies (and (hil-hsl-invariant st)
                 (memberp (action stimulus)
                          '(:home-grants-shared
                            :home-grants-exclusive)))
            (hil-hsl-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hil-hsl-invariant                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right.  Now we are done with hil-hsl.  Let us move on to
;; invalidate-ack-ch2.  This says that when we have an invalidate-ack in a ch3
;; then ch2 is nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.14: Proof of invalidate-ack-ch2-invariant              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |invalidate-ack-ch2 default cases|
   (implies (and (invalidate-ack-ch2-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (invalidate-ack-ch2-invariant (german-step st stimulus)))))

;; Of course if we set ch2 to nil then we have this trivially, unless of course
;; we also set ch3.  This will take care of most cases.

(local
 (defthm invalidate-ack-ch2-when-ch2-nil
   (implies (invalidate-ack-ch2 ch2 ch3 keys)
            (invalidate-ack-ch2 (s i nil ch2) ch3 keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm invalidate-ack-ch2-when-ch2-nil-and-ch3-anything
   (implies (invalidate-ack-ch2 ch2 ch3 keys)
            (invalidate-ack-ch2 (s i nil ch2) (s i v ch3) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |invalidate-ack-ch2 after ch2 nil|
   (implies (and (invalidate-ack-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:client-receives-shared
                            :sharer-invalidate-cache
                            :client-receives-exclusive)))
            (invalidate-ack-ch2-invariant (german-step st stimulus)))))

;; Now what happens with the remaining cases?  When home-receives-invalidate it
;; is fine since we are setting ch3 to nil.

(local
 (defthm invalidate-ack-after-ch3-set
   (implies (and (invalidate-ack-ch2 ch2 ch3 keys)
                 (not (equal v :invalidate-ack)))
            (invalidate-ack-ch2 ch2 (s i v ch3) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |invalidate-ack after receiving invalidate|
   (implies (and (invalidate-ack-ch2-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (invalidate-ack-ch2-invariant (german-step st stimulus)))))

;; The remaining cases now are home-grants-shared and home-grants-exclusive.
;; Why does this predicate hold after home-grants-shared?  The reason is as
;; follows.  In this situation I know that hcm is req-shared and (not heg) is
;; true.  In this condition no invalidate-ack is there since no invalidate is
;; sent out.  I posit that as a new predicate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk hcm-invalidate-ack (hcm heg ch3 keys)
   (forall i
           (implies (and (memberp i keys)
                         (equal (g i ch3) :invalidate-ack))
                    (or (equal hcm :req-exclusive-access)
                        (and (equal hcm :req-shared-access)
                             heg))))))

(local
 (defun hcm-invalidate-ack-invariant (st)
   (hcm-invalidate-ack (hcm st) (heg st) (ch3 st) (keys))))

(local
 (defthm |init has hcm-invalidate-ack|
   (hcm-invalidate-ack-invariant (init))))

(local
 (in-theory (disable hcm-invalidate-ack hcm-invalidate-ack-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here we see the use of a witness function to do universal quantification.  I
;; define a witness for the negation of the property I care about and then
;; prove that if the witness has the property then everything has the property.
;; When I do this sort of reasoning I feel like I should have defined the
;; predicate using defun-sk directly, but for waht it is worth this is useful
;; for demonstration.

(local
 (defun invalidate-ack-ch2-witness (ch2 ch3 keys)
   (if (endp keys) nil
     (if (and (equal (g (first keys) ch3) :invalidate-ack)
              (g (first keys) ch2))
         (first keys)
       (invalidate-ack-ch2-witness ch2 ch3 (rest keys))))))

(local
 (defthm invalidate-ack-from-witness
   (implies (or (not (memberp (invalidate-ack-ch2-witness ch2 ch3 keys) keys))
                (not (equal (g (invalidate-ack-ch2-witness ch2 ch3 keys) ch3)
                            :invalidate-ack))
                (not (g (invalidate-ack-ch2-witness ch2 ch3 keys) ch2)))
            (invalidate-ack-ch2 ch2 ch3 keys))))

(local
 (defthm hcm-invalidate-invalidate-ack
   (implies (and (hcm-invalidate-ack hcm heg ch3 keys)
                 (not heg)
                 (equal hcm :req-shared-access))
            (invalidate-ack-ch2 ch2 ch3 keys))
   :hints
   (("Goal"
     :use ((:instance hcm-invalidate-ack-necc
                      (i (invalidate-ack-ch2-witness ch2 ch3 keys))))))))

(local
 (defthm |invalidate-ack-ch2 when home-grants-shared|
   (implies (and (invalidate-ack-ch2-invariant st)
                 (hcm-invalidate-ack-invariant st)
                 (equal (action stimulus) :home-grants-shared))
            (invalidate-ack-ch2-invariant (german-step st stimulus)))))

;; Let us now look at home-grants-exclusive.  Why is this predicate ok?  I know
;; that if home grants exclusive then all hsl entries are nil.  But if all of
;; them are nil then hsl-ch3 tells me that all ch3 are nil.  If all ch3 are
;; nil, then of course the predicate holds trivially.

(local
 (defthm hsl-ch3-and-all-false-implies-ok
   (implies (and (hsl-ch3 hsl ch3 keys)
                 (all-false keys hsl))
            (invalidate-ack-ch2 (s i v ch2) ch3 keys))))

(local
 (defthm |invalidate-ack after granting invalidate|
   (implies (and (hsl-ch3-invariant st)
                 (invalidate-ack-ch2-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (invalidate-ack-ch2-invariant (german-step st stimulus)))))

;; And what happens after home-sends-invalidate? This is taken care of by
;; saying that if someone is in hil then it does not contain
;; invalidate-ack.  This, together with the guard that the current process
;; is in hil says that the process does not have invalidate-ack in ch3.  This
;; means we can set anything to ch2 and get away with it.

(local
 (defthm hil-invalidate-invalidate-ack-ch2
   (implies (and (hil-invalidate hil ch3 keys)
                 (memberp i keys)
                 (g i hil)
                 (invalidate-ack-ch2 ch2 ch3 keys))
            (invalidate-ack-ch2 (s i v ch2) ch3 keys))
   :hints (("Subgoal *1/6"
            :cases ((equal i (car keys)))))))

(local
 (defthm |invalidate-ack-ch2 after home-sends-invalidate|
   (implies (and (invalidate-ack-ch2-invariant st)
                 (hil-invalidate-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (invalidate-ack-ch2-invariant (german-step st stimulus)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of invalidate-ack-ch2-invariant                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right done with one more.  Now let us think about what unique-hil.  This
;; predicate says that if heg is true then there is at most one index with hil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.15: Proof of unique-hil-invariant                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |unique-hil default cases|
   (implies (and (unique-hil-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-sends-invalidate
                                 :home-receives-invalidate
                                 :home-grants-exclusive))))
            (unique-hil-invariant (german-step st stimulus)))))

;; I will start with home-sends-invalidate.  Why is unique-hil an invariant in
;; this case?  If a state is unique-nil then setting a particular index to nil
;; does not change the situation.

(local
 (defthm unique-hil-implies-so-after-hil-nil
   (implies (unique-hil hil heg keys)
            (unique-hil (s i nil hil) heg keys))
   :hints
   (("Goal"
     :cases ((equal i (car (unique-hil-witness (s i nil hil) heg keys)))
             (equal i (mv-nth 1 (unique-hil-witness (s i nil hil) heg keys)))))
    ("Subgoal 1"
     :in-theory (enable unique-hil))
    ("Subgoal 2"
     :in-theory (enable unique-hil))
    ("Subgoal 3"
     :use
     ((:instance (:definition unique-hil)
                 (hil (s i nil hil)))
      (:instance
       unique-hil-necc
       (i (car (unique-hil-witness (s i nil hil) heg keys)))
       (j (mv-nth 1 (unique-hil-witness (s i nil hil) heg keys)))))))))


;; Well, that kind of does it for home-sends-invalidate.  Here is the proof.

(local
 (defthm |unique-hil after home-sends-invalidate|
   (implies (and (unique-hil-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (unique-hil-invariant (german-step st stimulus)))))

;; What about home-receives-invalidate? This works because we are now setting
;; heg to hil.

(local
 (defthm not-heg-implies-unique-hil
   (implies (not heg)
            (unique-hil hil heg keys))
   :hints (("Goal"
            :in-theory (enable unique-hil)))))

(local
 (defthm |unique-hil after home-receives-invalidate|
   (implies (and (unique-hil-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (unique-hil-invariant (german-step st stimulus)))))

;; This of course does not work for home-grants-exclusive, since here we *are*
;; setting heg.  But we know something in this case that will help us out.
;; What do I know?  I know all-false holds.  This says (together with the
;; predicate hil-hsl that there is no hil at all.  So this case does not arise.

(local
 (defthm hil-hsl-implies-unique-hil
   (implies (and (hil-hsl hil hsl keys)
                 (all-false keys hsl))
            (unique-hil (s i v hil) heg keys))
   :hints
   (("Goal"
     :in-theory (enable unique-hil)
     :cases ((equal i (car (unique-hil-witness (s i v hil) heg keys)))))
    ("Subgoal 1"
     :cases
     ((equal i (mv-nth 1 (unique-hil-witness (s i v hil) heg keys))))))))


;; And of course unique-hil remains if hil is not set at all.

(local
 (defthm hil-hsl-implies-unique-hil-not-set
   (implies (and (hil-hsl hil hsl keys)
                 (all-false keys hsl))
            (unique-hil hil heg keys))
   :hints (("Goal"
            :in-theory (enable unique-hil)))))

;; So we can now get this grant-exclusive case thru.

(local
 (defthm |unique-hil after home grants exclusive|
   (implies (and (unique-hil-invariant st)
                 (hil-hsl-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (unique-hil-invariant (german-step st stimulus)))))

;; What happens when home picks a new request?  The issue here is that we need
;; to claim unique-hil for set-hil-hsl.  Now this is true because hsl has the
;; same predicate holding, and after set-hil-hsl therefore hil will have the
;; same predicate.

(local
 (defthm hsl-heg-implies-unique-hil
   (implies (hsl-heg hsl heg keys)
            (unique-hil (set-hil-hsl keys hil hsl)
                        heg keys))
   :hints
   (("Goal"
     :use
     ((:instance (:definition unique-hil)
                 (hil (set-hil-hsl keys hil hsl)))
      (:instance
       hsl-heg-necc
       (i (car (unique-hil-witness (set-hil-hsl keys hil hsl)
                                   heg keys)))
       (j (mv-nth 1 (unique-hil-witness (set-hil-hsl keys hil hsl)
                                        heg keys)))))))))

(local
 (defthm |unique-hil after picking new request|
   (implies (and (unique-hil-invariant st)
                 (hsl-heg-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (unique-hil-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of unique-hil-invariant                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right now to hsl-heg-invariant.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.16: Proof of hsl-heg-invariant                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hsl-heg default cases|
   (implies (and (hsl-heg-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-receives-invalidate
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hsl-heg-invariant (german-step st stimulus)))))

;; Now this works for home receiving invalidate since heg is being set to nil.

(local
 (defthm hsl-heg-after-heg-nil
   (implies (not heg)
            (hsl-heg hsl heg keys))
   :hints (("Goal"
            :in-theory (enable hsl-heg)))))

(local
 (defthm |hsl-heg after home receives invalidate|
   (implies (and (hsl-heg-invariant st)
                 (memberp (action stimulus) '(:home-grants-shared
                                              :home-receives-invalidate)))
            (hsl-heg-invariant (german-step st stimulus)))))

;; Only left now is when home grants exclusive.  Now I know that all other
;; clients are nil.  And it is therefore known that we can set anything to hsl.

(local
 (defthm all-false-implies-false
   (implies (and (all-false keys hsl)
                 (memberp i keys))
            (equal (g i hsl) nil))))

(local
 (defthm hsl-can-be-set-when-all-false
   (implies (all-false keys hsl)
            (hsl-heg (s i v hsl) heg keys))
   :hints
   (("Goal"
     :in-theory (enable hsl-heg)
     :cases ((equal i (car (hsl-heg-witness (s i v hsl) heg keys)))
             (equal i (mv-nth 1 (hsl-heg-witness (s i v hsl) heg keys))))))))

(local
 (defthm |hsl-heg after home-grants-exclusive|
   (implies (and (hsl-heg-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (hsl-heg-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hsl-heg-invariant                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; hsl-ch3-invariant now.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.17: Proof of hsl-ch3-invariant                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hsl-ch3 default cases|
   (implies (and (hsl-ch3-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hsl-ch3-invariant (german-step st stimulus)))))

;; Of course it is easy to do the granting of exclusive and shared.  All that
;; it is, is that we can set hsl to T as much as we want.

(local
 (defthm hsl-T-does-not-change-hsl-ch3
   (implies (hsl-ch3 hsl ch3 keys)
            (hsl-ch3 (s i T hsl) ch3 keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-ch3 does not change on grant|
   (implies (and (hsl-ch3-invariant st)
                 (memberp (action stimulus) '(:home-grants-shared
                                              :home-grants-exclusive)))
            (hsl-ch3-invariant (german-step st stimulus)))))

;; Similarly if ch3 is set to nil then nothing happens.

(local
 (defthm hsl-ch3-if-ch3-nil
   (implies (hsl-ch3 hsl ch3 keys)
            (hsl-ch3 (s i v hsl) (s i nil ch3) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-ch3 after receiving invalidation|
   (implies (and (hsl-ch3-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hsl-ch3-invariant (german-step st stimulus)))))

;; The only critical case here is when the client is sending acknowledgement of
;; invalidation to the server.  This is because now we must say that the index
;; was already T in hsl.  This holds because of hsl-ch2, and the fact that we
;; know that ch2 now containts :invalidate.

(local
 (defthm hsl-ch3-for-not-member
   (implies (and (hsl-ch3 hsl ch3 keys)
                 (not (memberp i keys)))
            (hsl-ch3 hsl (s i v ch3) keys))))

(local
 (defthm hsl-ch2-implies-hsl-ch3-after-set
   (implies (and (hsl-ch2 hsl keys ch2)
                 (hsl-ch3 hsl ch3 keys)
                 (memberp i keys)
                 (g i ch2))
            (hsl-ch3 hsl (s i v ch3) keys))
   :hints (("Goal"
            :do-not '(eliminate-destructors generalize fertilize))
           ("Subgoal *1/6"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-ch3 after sharer invalidates|
   (implies (and (hsl-ch3-invariant st)
                 (hsl-ch2-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (hsl-ch3-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hsl-ch3-invariant                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; hsl-boolean-invariant now.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.18: Proof of hsl-boolean-invariant                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This one is particularly trivial, as indeed are most others which have to do
;; with types.  In fact it is an inductive invariant in itself.

(local
 (defthm |hsl-boolean default cases|
   (implies (and (hsl-boolean-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-receives-invalidate
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hsl-boolean-invariant (german-step st stimulus)))))

(local
 (defthm hsl-boolean-if-boolean-val-set
   (implies (and (hsl-boolean hsl keys)
                 (booleanp v))
            (hsl-boolean (s i v hsl) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-boolean other cases|
   (implies (and (hsl-boolean-invariant st)
                 (memberp (action stimulus)
                          '(:home-receives-invalidate
                            :home-grants-shared
                            :home-grants-exclusive)))
            (hsl-boolean-invariant (german-step st stimulus)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hsl-boolean-invariant                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.19: Proof of hil-invalidate-invariant                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hil-invalidate default cases|
   (implies (and (hil-invalidate-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache))))
            (hil-invalidate-invariant (german-step st stimulus)))))

;; Now if home sends an invalidate it sets hil to nil and thus it works out.

(local
 (defthm hil-invalidate-on-nil
   (implies (hil-invalidate hil ch3 keys)
            (hil-invalidate (s i nil hil) ch3 keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-invalidate on home-sends-invalidate|
   (implies (and (hil-invalidate-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hil-invalidate-invariant (german-step st stimulus)))))

;; Now it must also be ok when home receives it.  Now it sets ch3 to something
;; other than invalidate-ack so I dont have to prove anything.

(local
 (defthm hil-invalidate-ack-set
   (implies (and (hil-invalidate hil ch3 keys)
                 (not (equal v :invalidate-ack)))
            (hil-invalidate hil (s i v ch3) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-invalidate when home receives invalidate|
   (implies (and (hil-invalidate-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hil-invalidate-invariant (german-step st stimulus)))))

;; But what happens when the sharer actually inserts an invalidate-ack in ch3?
;; This is the third case we consider.  Now what the heck do we know about this
;; situation?  Why does this predicate hold?  We know that the ch2 is having an
;; :invalidate.  So we must know that when ch2 has :invalidate then hil must be
;; nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hil-invalidate-ch2 (hil ch2 keys)
   (if (endp keys) T
     (and (implies (equal (g (first keys) ch2) :invalidate)
                   (not (g (first keys) hil)))
          (hil-invalidate-ch2 hil ch2 (rest keys))))))

(local
 (defun hil-invalidate-ch2-invariant (st)
   (hil-invalidate-ch2 (hil st) (ch2 st) (keys))))

(local
 (defthm hil-invalidate-ch2-for-nil (hil-invalidate-ch2 nil nil keys)))

(local
 (defthm |init has hil-invalidate-ch2| (hil-invalidate-ch2-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(local
 (defthm hil-invalidate-ch2-implies-invalidate
   (implies (and (hil-invalidate-ch2 hil ch2 keys)
                 (hil-invalidate hil ch3 keys)
                 (memberp i keys)
                 (equal (g i ch2) :invalidate))
            (hil-invalidate hil (s i v ch3) keys))
   :hints (("Subgoal *1/6"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-invalidate after sharer-invalidate-cache|
   (implies (and (hil-invalidate-invariant st)
                 (hil-invalidate-ch2-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (hil-invalidate-invariant (german-step st stimulus)))))

;; The condition for picking new request is a bit more interesting.  I have to
;; claim that at this point there is no invalidate-ack around.  But how do we
;; know that?  Do I know that anything from hsl does not have invalidate-ack?
;; Clearly not.  But what I do know is that if invalidate-ack is true of
;; something then hcm is true.  This is from hcm-invalidate-ack.

;; Now I will prove that hcm-invalidate-ack implies hil-invalidate.  This is an
;; interesting exercise since I am proving something about a recursive function
;; using a quantified property.  To do this I will invoke the so-called
;; "witness function" approach.

(local
 (defun hil-invalidate-witness (hil ch3 keys)
   (if (endp keys) nil ;; dont care
     (if (and (equal (g (first keys) ch3) :invalidate-ack)
              (g (first keys) hil))
         (first keys)
       (hil-invalidate-witness hil ch3 (rest keys))))))

(local
 (defthm hil-invalidate-witness-implies-hil-invalidate
   (implies (or (not (equal (g (hil-invalidate-witness hil ch3 keys) ch3)
                            :invalidate-ack))
                (not (memberp (hil-invalidate-witness hil ch3 keys)
                              keys))
                (not (g (hil-invalidate-witness hil ch3 keys) hil)))
            (hil-invalidate hil ch3 keys))))

(local
 (defthm hcm-ch3-implies-hil-invalidate
   (implies (and (hcm-invalidate-ack hcm heg ch3 keys)
                 (not hcm))
            (hil-invalidate hil ch3 keys))
   :hints (("Goal"
            :use ((:instance hcm-invalidate-ack-necc
                             (i (hil-invalidate-witness hil ch3 keys))))))))

(local
 (defthm |hil-invalidate when pick-new-request|
   (implies (and (hil-invalidate-invariant st)
                 (hcm-invalidate-ack-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (hil-invalidate-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hil-invalidate-invariant                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now let us get to this predicate hil-invalidate-ch2.  I have a premonition
;; that it would involve specifying something about hcm.  We will see.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.20: Proof of hil-invalidate-ch2-invariant              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hil-invalidate-ch2 default cases|
   (implies (and (hil-invalidate-ch2-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-sends-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hil-invalidate-ch2-invariant (german-step st stimulus)))))

;; Of course the standard thing is that if ch2 is set to nil then we are in
;; great shape.

(local
 (defthm hil-invalidate-ch2-when-ch2-nil
   (implies (hil-invalidate-ch2 hil ch2 keys)
            (hil-invalidate-ch2 hil (s i nil ch2) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-invalidate-ch2 when ch2 is reset|
   (implies (and (hil-invalidate-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:sharer-invalidate-cache
                            :client-receives-shared
                            :client-receives-exclusive)))
            (hil-invalidate-ch2-invariant (german-step st stimulus)))))

;; And as usual setting hil to nil does not matter.  So we use that to do the
;; sending of invalidate.

(local
 (defthm hil-invalidate-ch2-set-hil-nil
   (implies (hil-invalidate-ch2 hil ch2 keys)
            (hil-invalidate-ch2 (s i nil hil) (s i v ch2) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-invalidate-ch2 home-sends-invalidate|
   (implies (and (hil-invalidate-ch2-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hil-invalidate-ch2-invariant (german-step st stimulus)))))

;; And it does not matter if I set anything other than :invalidate in ch2.

(local
 (defthm hil-invalidate-other-than-invalidate
   (implies (and (hil-invalidate-ch2 hil ch2 keys)
                 (not (equal v :invalidate)))
            (hil-invalidate-ch2 hil (s i v ch2) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-invalidate-ch2 for grant|
   (implies (and (hil-invalidate-ch2-invariant st)
                 (memberp (action stimulus) '(:home-grants-shared
                                              :home-grants-exclusive)))
            (hil-invalidate-ch2-invariant (german-step st stimulus)))))

;; And finally the non-trivial case, namely :pick-new-request.  What do we know
;; here?  I would have loved to say that if ch2 has invalidate then hsl is nil.
;; But that is not true!!!  In fact it is exactly the opposite that is true.  I
;; definitely know that if ch2 has an invalidate then hsl *is* true.  Why does
;; it work out then?  It works out because when hcm is nil ch2 is nil,
;; :grant-exclusive, or :grant-shared.  Why?  Because home receives some
;; request and works on it and goes on working on it until it can finish
;; processing.  During that time the hcm is always holding the command given.
;; It is only after the command has been completely processed that hcm is set
;; to nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun-sk hcm-ch2 (hcm heg ch2 keys)
   (forall i (implies (and (memberp i keys)
                           (equal (g i ch2) :invalidate))
                      (or (and (equal hcm :req-shared-access)
                               heg)
                          (equal hcm :req-exclusive-access))))))

(local
 (defun hcm-ch2-invariant (st) (hcm-ch2 (hcm st) (heg st) (ch2 st) (keys))))

(local
 (defthm |init has hcm-ch2| (hcm-ch2-invariant (init))))

(local
 (in-theory (disable hcm-ch2 hcm-ch2-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm not-hcm-implies-not-invalidate
   (implies (and (hcm-ch2 hcm heg ch2 keys)
                 (not hcm)
                 (memberp i keys))
            (equal (equal (g i ch2) :invalidate) nil))
   :hints (("Goal"
            :use hcm-ch2-necc))))

;; And here I see how we can mimic quantification with recursion.

(local
 (defun hil-invalidate-rwitness (hil ch2 keys)
   (if (endp keys) nil ;; dont care
     (if (and (equal (g (first keys) ch2) :invalidate)
              (g (first keys) hil))
         (first keys)
       (hil-invalidate-rwitness hil ch2 (rest keys))))))

(local
 (defthm hil-invalidate-rwitness-invalidate
   (implies (or (not (equal (g (hil-invalidate-rwitness hil ch2 keys) ch2)
                            :invalidate))
                (not (g (hil-invalidate-rwitness hil ch2 keys) hil))
                (not (memberp (hil-invalidate-rwitness hil ch2 keys) keys)))
            (hil-invalidate-ch2 hil ch2 keys))))

(local
 (defthm not-hcm-implies-hil-invalidate
   (implies (and (hcm-ch2 hcm heg ch2 keys)
                 (not hcm))
            (hil-invalidate-ch2 hil ch2 keys))
   :hints (("Goal"
            :in-theory (disable hil-invalidate-rwitness-invalidate)
            :use hil-invalidate-rwitness-invalidate))))

(local
 (defthm |hil-invalidate on pick-new-request|
   (implies (and (hil-invalidate-ch2-invariant st)
                 (hcm-ch2-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (hil-invalidate-ch2-invariant (german-step st stimulus)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hil-invalidate-ch2-invariant                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; hcm-ch2-invariant

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.21: Proof of hcm-ch2-invariant                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hcm-ch2 default cases|
   (implies (and (hcm-ch2-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hcm-ch2-invariant (german-step st stimulus)))))

;; Now what happens when there is an invalidate-ack?  Why is the predicate
;; going to be ok here?  There should be no other invalidate-ack.  I know this
;; as follows.  hsl-heg tells me that if heg is true then there is at most one
;; hsl.  hsl-ch3 then tells me that there is at most one ch3.  This ch3 is the
;; invalidate-ack I am seeing.  Thus if I set this to nil there is no ch3, and
;; hence I am done.  And of course if heg was already nil then there is nothing
;; to do.

;; All right, let us do this.

(local
 (defthm hsl-ch3-and-ch3-to-hsl
   (implies (and (hsl-ch3 hsl ch3 keys)
                 (memberp i keys)
                 (g i ch3))
            (g i hsl))))

(local
 (defthm hsl-heg-hsl-ch3-implies-only-one
   (implies (and (hsl-heg hsl heg keys)
                 (hsl-ch3 hsl ch3 keys)
                 (hsl-ch2 hsl keys ch2)
                 (memberp i keys)
                 (memberp j keys)
                 heg
                 (g j ch2)
                 (g i ch3))
            (equal i j))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :use hsl-heg-necc))))

;; Now I will claim that all right I know all this, and I also know from
;; invalidate-ack-ch2 that the guy which has invalidate-ack in ch3 does not
;; have a ch2.  This will show that there is no ch2 at all.

(local
 (defthm hsl-heg-hsl-ch3-implies-none
   (implies (and (hsl-heg hsl heg keys)
                 (hsl-ch3 hsl ch3 keys)
                 (invalidate-ack-ch2 ch2 ch3 keys)
                 (hsl-ch2 hsl keys ch2)
                 (memberp i keys)
                 (memberp j keys)
                 heg
                 (equal (g i ch3) :invalidate-ack))
            (equal (g j ch2) nil))
   :hints (("Goal"
            :cases ((equal i j))))))

;; And therefore I have it when heg.

(local
 (defthm hcm-ch2-when-heg
   (implies (and (hsl-heg hsl heg keys)
                 (hsl-ch3 hsl ch3 keys)
                 (invalidate-ack-ch2 ch2 ch3 keys)
                 (memberp i keys)
                 (equal (g i ch3) :invalidate-ack)
                 (hsl-ch2 hsl keys ch2)
                 heg)
            (hcm-ch2 hcm v ch2 keys))
   :hints (("Goal"
            :in-theory (enable hcm-ch2)))))

;; For the final theorem I will case-split on whether heg is true.

(local
 (defthm |hcm-ch2 when home-receives-invalidate|
   (implies (and (hcm-ch2-invariant st)
                 (hsl-heg-invariant st)
                 (hsl-ch3-invariant st)
                 (invalidate-ack-ch2-invariant st)
                 (hsl-ch2-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hcm-ch2-invariant (german-step st stimulus)))
   :hints (("Goal" :cases ((heg st))))))

;; The argument for picking a request is kind of cute.  It says that if hcm is
;; not one of the approved values then there is no invalidate, and since there
;; is no invalidate I am now allowed to make hcm anything!  Isn't it cute?

(local
 (defthm hcm-ch2-and-not-hcm-implies-hcm-anything
   (implies (and (hcm-ch2 hcm heg ch2 keys)
                 (not (equal hcm :req-exclusive-access))
                 (or (not (equal hcm :req-shared-access))
                     (not heg)))
            (hcm-ch2 v u ch2 keys))
   :hints (("Goal"
            :use ((:instance (:definition hcm-ch2)
                             (hcm v)
                             (heg u))
                  (:instance hcm-ch2-necc
                             (i (hcm-ch2-witness v u ch2 keys))))))))

(local
 (defthm |hcm-ch2 for pick-new-request|
   (implies (and (hcm-ch2-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (hcm-ch2-invariant (german-step st stimulus)))))

;; For granting shared a similar argument is necessary but now we also set
;; ch2.

(local
 (defthm hcm-ch2-and-not-hcm-implies-hcm-anything-with-ch2
   (implies (and (hcm-ch2 hcm heg ch2 keys)
                 (not (equal hcm :req-exclusive-access))
                 (not (equal w :invalidate))
                 (or (not (equal hcm :req-shared-access))
                     (not heg)))
            (hcm-ch2 v u (s i w ch2) keys))
   :hints (("Goal"
            :cases ((equal i (hcm-ch2-witness v u (s i w ch2) keys))))
           ("Subgoal 1"
            :in-theory (enable hcm-ch2))
           ("Subgoal 2"
            :use ((:instance (:definition hcm-ch2)
                             (hcm v)
                             (ch2 (s i w ch2))
                             (heg u))
                  (:instance hcm-ch2-necc
                             (i (hcm-ch2-witness v u (s i w ch2) keys))))))))

(local
 (defthm |hcm-ch2 after home-grants-shared|
   (implies (and (hcm-ch2-invariant st)
                 (equal (action stimulus) :home-grants-shared))
            (hcm-ch2-invariant (german-step st stimulus)))))


;; And home-sends-invalidate is rather trivial since the definition of hcm is
;; done with this predicate in mind.

(local
 (defthm hcm-ch2-if-the-right-things-set
   (implies (or (and (equal hcm :req-shared-access)
                     heg)
                (equal hcm :req-exclusive-access))
            (hcm-ch2 hcm heg ch2 keys))
   :hints (("Goal"
            :in-theory (enable hcm-ch2)))))

(local
 (defthm |hcm-ch2 when home-sends-invalidate|
   (implies (and (hcm-ch2-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hcm-ch2-invariant (german-step st stimulus)))))

;; As in fact it does not matter if I set ch2 to something other than
;; :invalidate.

(local
 (defthm hcm-ch2-after-setting-ch2
   (implies (and (hcm-ch2 hcm heg ch2 keys)
                 (not (equal v :invalidate)))
            (hcm-ch2 hcm heg (s i v ch2) keys))
   :hints (("Goal"
            :cases ((equal i (hcm-ch2-witness hcm heg (s i v ch2) keys))))
           ("Subgoal 2"
            :use ((:instance (:definition hcm-ch2)
                             (ch2 (s i v ch2)))
                  (:instance hcm-ch2-necc
                             (i (hcm-ch2-witness hcm heg (s i v ch2) keys)))))
           ("Subgoal 1"
            :in-theory (enable hcm-ch2)))))

(local
 (defthm |hcm-ch2 after client sets|
   (implies (and (hcm-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:sharer-invalidate-cache
                            :client-receives-shared
                            :client-receives-exclusive)))
            (hcm-ch2-invariant (german-step st stimulus)))))

;; And the exclusive of course just requires that we have hsl-ch2 which we do.

(local
 (defthm hsl-ch2-and-all-false-implies-hcm
   (implies (and (hsl-ch2 hsl keys ch2)
                 (not (equal v :invalidate))
                 (all-false keys hsl))
            (hcm-ch2 hcm heg (s i v ch2) keys))
   :hints (("Goal"
            :cases ((equal i (hcm-ch2-witness hcm heg (s i v ch2) keys))))
           ("Subgoal 1"
            :in-theory (enable hcm-ch2))
           ("Subgoal 2"
            :in-theory (enable hcm-ch2)))))

(local
 (defthm |hsm-ch2 when grants exclusive|
   (implies (and (hcm-ch2-invariant st)
                 (hsl-ch2-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (hcm-ch2-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hcm-ch2-invariant                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now I handle the hcm-invalidate-ack-invariant.  This says that if (not heg)
;; and hcm is equal to :req-shared-access then there is no invalidate-ack.
;; This should be pretty trivial since under these conditions we dont send an
;; invalidate at all.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.22: Proof of hcm-invalidate-ack-invariant              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hcm-invalidate-ack default cases|
   (implies (and (hcm-invalidate-ack-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hcm-invalidate-ack-invariant (german-step st stimulus)))))

;; Now what happens when we pick a new request?  We know hcm is nil.  And then
;; there is nothing to prove.  This is the same cute trick that we invoked for
;; hcm-ch2.

(local
 (defthm hcm-ack-and-not-hcm-implies-hcm-anything
   (implies (and (hcm-invalidate-ack hcm heg ch3 keys)
                 (not (equal hcm :req-exclusive-access))
                 (or (not (equal hcm :req-shared-access))
                     (not heg)))
            (hcm-invalidate-ack v u ch3 keys))
   :hints
   (("Goal"
     :use ((:instance (:definition hcm-invalidate-ack)
                      (hcm v)
                      (heg u))
           (:instance hcm-invalidate-ack-necc
                      (i (hcm-invalidate-ack-witness v u ch3 keys))))))))

(local
 (defthm |hcm-invalidate-ack for pick-new-request|
   (implies (and (hcm-invalidate-ack-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (hcm-invalidate-ack-invariant (german-step st stimulus)))))

;; And the same trick for grant-shared.

(local
 (defthm hcm-ch3-and-not-hcm-implies-hcm-anything-with-ch2
   (implies (and (hcm-invalidate-ack hcm heg ch3 keys)
                 (not (equal hcm :req-exclusive-access))
                 (not (equal w :invalidate-ack))
                 (or (not (equal hcm :req-shared-access))
                     (not heg)))
            (hcm-invalidate-ack v u (s i w ch3) keys))
   :hints
   (("Goal"
     :cases ((equal i (hcm-invalidate-ack-witness v u (s i w ch3) keys))))
    ("Subgoal 1"
     :in-theory (enable hcm-invalidate-ack))
    ("Subgoal 2"
     :use
     ((:instance (:definition hcm-invalidate-ack)
                 (hcm v)
                 (ch3 (s i w ch3))
                 (heg u))
      (:instance hcm-invalidate-ack-necc
                 (i (hcm-invalidate-ack-witness v u (s i w ch3) keys))))))))

(local
 (defthm |hcm-invalidate-ack after home-grants-shared|
   (implies (and (hcm-invalidate-ack-invariant st)
                 (equal (action stimulus) :home-grants-shared))
            (hcm-invalidate-ack-invariant (german-step st stimulus)))))

;; As I well realize now this predicate is kind of a mirror image of hcm-ch2.
;; So home-receives-invalidate is going to have a problem.  And indeed exactly
;; the same problem as hcm-ch2.  And the solution is exactly the same too!

(local
 (defthm hsl-heg-hsl-ch3-implies-only-one-ch3
   (implies (and (hsl-heg hsl heg keys)
                 (hsl-ch3 hsl ch3 keys)
                 (memberp i keys)
                 (memberp j keys)
                 heg
                 (g j ch3)
                 (g i ch3))
            (equal i j))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :use hsl-heg-necc))))

;; Now I can prove that if I set ch3 to something else I would be done.

(local
 (defthm hcm-ch3-when-heg
   (implies (and (hsl-heg hsl heg keys)
                 (hsl-ch3 hsl ch3 keys)
                 (memberp i keys)
                 (not (equal u :invalidate-ack))
                 (equal (g i ch3) :invalidate-ack)
                 heg)
            (hcm-invalidate-ack hcm v (s i u ch3) keys))
   :hints
   (("Goal"
     :in-theory (enable hcm-invalidate-ack)
     :cases ((equal i (hcm-invalidate-ack-witness hcm v (s i u ch3) keys)))))))

;; Well in this case we need to do something for not-heg as well just because I
;; am setting ch3.  Now what happens if heg is actually not true.  Now in this
;; case the hcm is req-shared-access and since I am not changing hcm it still
;; remains req-shared-access and I have nothing to prove.

(local
 (defthm not-heg-invalidate-ack-implies-invalidate-ack
   (implies (and (hcm-invalidate-ack hcm heg ch3 keys)
                 (not heg)
                 (memberp i keys)
                 (equal (g i ch3) :invalidate-ack))
            (hcm-invalidate-ack hcm v u keys))
   :hints (("Goal"
            :use ((:instance (:definition hcm-invalidate-ack)
                             (heg v)
                             (ch3 u))
                  (:instance hcm-invalidate-ack-necc))))))

(local
 (defthm |hcm-invalidate-ack when home-receives-invalidate|
   (implies (and (hsl-heg-invariant st)
                 (hsl-ch3-invariant st)
                 (hcm-invalidate-ack-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hcm-invalidate-ack-invariant (german-step st stimulus)))
   :hints (("Goal"
            :cases ((heg st))))))

;; What happens when the sharer invalidates?  I need to claim that under the
;; non-trivial conditions there is no invalidate at all, and hence there is no
;; problem.

(local
 (defthm invalidate-not-a-problem
   (implies (and (hcm-ch2 hcm heg ch2 keys)
                 (memberp i keys)
                 (equal (g i ch2) :invalidate))
            (hcm-invalidate-ack hcm heg ch3 keys))
   :hints (("Goal"
            :in-theory (enable hcm-invalidate-ack)
            :use hcm-ch2-necc))))

(local
 (defthm |hcm-invalidate-ack after sharer invalidates|
   (implies (and (hcm-invalidate-ack-invariant st)
                 (hcm-ch2-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (hcm-invalidate-ack-invariant (german-step st stimulus)))))

;; Now what happens if either there is a grant-exclusive? Again I will go thru
;; the pain of hsl and all-false.  This predicate *is* really like hcm-ch2, the
;; more I think about it.

(local
 (defthm hsl-ch3-and-all-false-implies-hcm
   (implies (and (hsl-ch3 hsl ch3 keys)
                 (all-false keys hsl))
            (hcm-invalidate-ack hcm heg ch3 keys))
   :hints
   (("Goal"
     :cases ((equal i (hcm-invalidate-ack-witness hcm heg ch3 keys))))
    ("Subgoal 1"
     :in-theory (enable hcm-invalidate-ack))
    ("Subgoal 2"
     :in-theory (enable hcm-invalidate-ack)))))

(local
 (defthm |hsm-invalidate-ack when grants exclusive|
   (implies (and (hcm-invalidate-ack-invariant st)
                 (hsl-ch3-invariant st)
                 (equal (action stimulus) :home-grants-exclusive))
            (hcm-invalidate-ack-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hcm-invalidate-ack-invariant                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now I handle invalidate-clients-invariant.  This should not be too much
;; trouble.  If says that if a client has an invalidate it must be shared or
;; exclusive.  In other words invalidation is not sent to idle clients.  Since
;; this involves a property of two components for the same index, this should
;; be easy.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.22: Proof of hcm-invalidate-ack-invariant              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |invalidate-clients default cases|
   (implies (and (invalidate-clients-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (invalidate-clients-invariant (german-step st stimulus)))))

;; And as is standard, I will show that if the predicate already holds then
;; setting ch2 to something other than invalidate does not change it.

(local
 (defthm invalidate-after-something-else
   (implies (and (invalidate-clients ch2 clients keys)
                 (not (equal v :invalidate)))
            (invalidate-clients (s i v ch2) clients keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

;; which takes care of home granting shared or invalidate.

(local
 (defthm |invalidate-clients after home-grants|
   (implies (and (invalidate-clients-invariant st)
                 (memberp (action stimulus)
                          '(:home-grants-shared
                            :home-grants-exclusive)))
            (invalidate-clients-invariant (german-step st stimulus)))))

;; Now when the client receives something it also does not matter as long as it
;; does not receive an invalidate.

(local
 (defthm invalidate-after-client-set
   (implies (and (invalidate-clients ch2 clients keys)
                 (not (equal v :invalidate)))
            (invalidate-clients (s i v ch2) (s i u clients) keys))
   :hints (("Goal"
            :do-not '(eliminate-destructors generalize fertilize))
           ("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |clients are fine with invalidate-clients|
   (implies (and (invalidate-clients-invariant st)
                 (memberp (action stimulus)
                          '(:sharer-invalidate-cache
                            :client-receives-shared
                            :client-receives-exclusive)))
            (invalidate-clients-invariant (german-step st stimulus)))))

;; The only crucial point is when home sends invalidate.  Why is that ok?  As I
;; realize now, the reason is kind of subtle and I had not realized this when I
;; posited the predicate.  The reason is that if hil has an index that is set
;; then the process is either shared, or exclusive, or grant-shared, or
;; grant-exclusive.  The reason actually is that hsl behaves the same way, and
;; therefore hil gets it derived.  We thus need to posit this as a predicate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hil-client-ch2 (hil clients ch2 keys)
   (if (endp keys) T
     (and (implies (g (first keys) hil)
                   (or (equal (g (first keys) clients) :shared)
                       (equal (g (first keys) clients) :exclusive)
                       (equal (g (first keys) ch2) :grant-shared)
                       (equal (g (first keys) ch2) :grant-exclusive)))
          (hil-client-ch2 hil clients ch2 (rest keys))))))

(local
 (defun hil-client-ch2-invariant (st)
   (hil-client-ch2 (hil st) (clients st) (ch2 st) (keys))))

(local
 (defthm hil-client-for-nil (hil-client-ch2 nil clients ch2 keys)))

(local
 (defthm |init has hil-client-ch2| (hil-client-ch2-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now this tells us that everything is ok.

(local
 (defthm hil-client-ch2-memberp-reduction
   (implies (and (hil-client-ch2 hil clients ch2 keys)
                 (memberp i keys)
                 (g i hil))
            (or (equal (g i clients) :shared)
                (equal (g i clients) :exclusive)
                (equal (g i ch2) :grant-shared)
                (equal (g i ch2) :grant-exclusive)))
   :rule-classes :forward-chaining))

;; Of course now it is fine to do the invalidate since this index is shared of
;; exclusive.  (Note that home checks if the ch2 has become empty.)

(local
 (defthm invalidate-clients-not-memberp-reduction
   (implies (and (invalidate-clients ch2 clients keys)
                 (not (memberp i keys)))
            (invalidate-clients (s i v ch2) clients keys))))

(local
 (defthm hil-client-hil-ch2-reduction
   (implies (and (hil-client-ch2 hil clients ch2 keys)
                 (invalidate-clients ch2 clients keys)
                 (memberp i keys)
                 (g i hil)
                 (not (g i ch2)))
            (invalidate-clients (s i v ch2) clients keys))
   :hints (("Subgoal *1/6"
            :cases ((equal i (car keys)))))))

(local
 (defthm |invalidate-clients after home-sends-invalidate|
   (implies (and (invalidate-clients-invariant st)
                 (hil-client-ch2-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (invalidate-clients-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of invalidate-clients-invariant                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I am annoyed that the proof is going on and on.  I thought when I was
;; proving invalidate-clients that it would be the last predicate I need to
;; reason about, but I got one more predicate.  Of course to deal with this I
;; already know one more is necessary, namely about hsl relating it with
;; clients and ch2.  But I hope not much more is involved.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.23: Proof of hil-client-ch2-invariant                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hil-client-ch2 default cases|
   (implies (and (hil-client-ch2-invariant st)
                 (not (memberp (action stimulus)
                               '(:pick-new-request
                                 :home-sends-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hil-client-ch2-invariant (german-step st stimulus)))))

;; And of course if I set the ch2 to grant-shared or grant-exclusive it does
;; not matter.

(local
 (defthm hil-client-ch2-set-ch2
   (implies (and (hil-client-ch2 hil clients ch2 keys)
                 (or (equal v :grant-exclusive)
                     (equal v :grant-shared)))
            (hil-client-ch2 hil clients (s i v ch2) keys))
   :hints (("Subgoal *1/3"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-client when home grants|
   (implies (and (hil-client-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:home-grants-exclusive
                            :home-grants-shared)))
            (hil-client-ch2-invariant (german-step st stimulus)))))

;; And as long as I set the clients to shared or exclusive again it does not
;; matter.  In fact it does not matter if we remove things from ch2.

(local
 (defthm hil-client-ch2-set-client
   (implies (and (hil-client-ch2 hil clients ch2 keys)
                 (or (equal v :exclusive)
                     (equal v :shared)))
            (hil-client-ch2 hil (s i v clients) (s i u ch2) keys))
   :hints (("Subgoal *1/3"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-client when client is set|
   (implies (and (hil-client-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:client-receives-exclusive
                            :client-receives-shared)))
            (hil-client-ch2-invariant (german-step st stimulus)))))

;; And for sharer-invalidating we only need to say that hil is not existing.
;; And this is known from hil-invalidate-ch2.

(local
 (defthm hil-invalidate-implies-can-set-client
   (implies (and (hil-client-ch2 hil clients ch2 keys)
                 (hil-invalidate-ch2 hil ch2 keys)
                 (equal (g i ch2) :invalidate))
            (hil-client-ch2 hil (s i v clients) (s i u ch2) keys))
   :hints (("Subgoal *1/5"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-client for sharer invalidating|
   (implies (and (hil-client-ch2-invariant st)
                 (hil-invalidate-ch2-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (hil-client-ch2-invariant (german-step st stimulus)))))

;; Why does hil-client work for home sending the invalidate?  I have nothing to
;; prove since hil is being set to nil.

(local
 (defthm hil-client-ch2-to-nil
   (implies (hil-client-ch2 hil clients ch2 keys)
            (hil-client-ch2 (s i nil hil) clients (s i v ch2) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hil-client-ch2 when home-sends-invalidate|
   (implies (and (hil-client-ch2-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hil-client-ch2-invariant (german-step st stimulus)))))

;; All right, now for the non-trivial one.  I need to write another predicate
;; which says that hsl has indices that are only shared, exclusive,
;; grant-shared, or grant-exclusive, or in fact the ch3 has invalidate-ack.
;; Otherwise I cannot have hil-client-ch2 when hil is set to hsl.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Begin Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun hsl-client-ch2 (hsl clients ch2 ch3 keys)
   (if (endp keys) T
     (and (implies (g (first keys) hsl)
                   (or (equal (g (first keys) clients) :shared)
                       (equal (g (first keys) clients) :exclusive)
                       (equal (g (first keys) ch2) :grant-shared)
                       (equal (g (first keys) ch2) :grant-exclusive)
                       (equal (g (first keys) ch3) :invalidate-ack)))
          (hsl-client-ch2 hsl clients ch2 ch3 (rest keys))))))

(local
 (defun hsl-client-ch2-invariant (st)
   (hsl-client-ch2 (hsl st) (clients st) (ch2 st) (ch3 st) (keys))))

(local
 (defthm hsl-client-for-nil (hsl-client-ch2 nil clients ch2 ch3 keys)))

(local
 (defthm |init has hsl-client-ch2| (hsl-client-ch2-invariant (init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Definition of new predicate                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; OK now we can prove that if hsl-client-ch2 holds then set-hil-hsl is fine.
;; I will prove it again using witness functions.  I now understand why J said
;; that I really love quantification....!!!

(local
 (defun hil-client-witness (hil clients ch2 keys)
   (if (endp keys) nil
     (if (and (g (first keys) hil)
              (not (equal (g (first keys) clients) :shared))
              (not (equal (g (first keys) clients) :exclusive))
              (not (equal (g (first keys) ch2) :grant-shared))
              (not (equal (g (first keys) ch2) :grant-exclusive)))
         (first keys)
       (hil-client-witness hil clients ch2 (rest keys))))))

(local
 (defthm hil-client-witness-to-hil-clients
   (implies
    (or (not (memberp (hil-client-witness hil clients ch2 keys) keys))
        (implies (g  (hil-client-witness hil clients ch2 keys) hil)
                 (or (equal (g (hil-client-witness hil clients ch2 keys)
                               clients)
                            :shared)
                     (equal (g (hil-client-witness hil clients ch2 keys)
                               clients)
                            :exclusive)
                     (equal (g (hil-client-witness hil clients ch2 keys) ch2)
                            :grant-shared)
                     (equal (g (hil-client-witness hil clients ch2 keys) ch2)
                            :grant-exclusive))))
    (hil-client-ch2 hil clients ch2 keys))
   :rule-classes nil))

;; And now prove that hsl-client-ch2 implies the above conditions.

(local
 (defthm hsl-client-member
   (implies (and (hsl-client-ch2 hsl clients ch2 ch3 keys)
                 (memberp i keys)
                 (not (equal (g i ch3) :invalidate-ack))
                 (g i hsl))
            (or (equal (g i clients) :shared)
                (equal (g i clients) :exclusive)
                (equal (g i ch2) :grant-shared)
                (equal (g i ch2) :grant-exclusive)))
   :rule-classes :forward-chaining))

;; Now we are in great shape, since hcm-invalidate-ack guarantees that we have
;; no invalidate-ack.

(local
 (defthm hsl-client-hil-client-reduction
   (implies (and (hsl-client-ch2 hsl clients ch2 ch3 keys)
                 (hcm-invalidate-ack hcm heg ch3 keys)
                 (not hcm))
            (hil-client-ch2 (set-hil-hsl keys hil hsl) clients ch2 keys))
   :hints
   (("Goal"
     :use
     ((:instance hil-client-witness-to-hil-clients
                 (hil (set-hil-hsl keys hil hsl)))
      (:instance
       hcm-invalidate-ack-necc
       (i (hil-client-witness (set-hil-hsl keys hil hsl)
                              clients ch2 keys))))))))

(local
 (defthm |hil-client-ch2 for picking request|
   (implies (and (hsl-client-ch2-invariant st)
                 (hil-client-ch2-invariant st)
                 (hcm-invalidate-ack-invariant st)
                 (equal (action stimulus) :pick-new-request))
            (hil-client-ch2-invariant (german-step st stimulus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End Proof of hil-client-ch2-invariant                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All right!  Well done.  Now let us trace the hsl and clients and everything
;; and try to finish this proof.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3.24: Proof of hsl-client-ch2-invariant                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm |hsl-client-ch2 default cases|
   (implies (and (hsl-client-ch2-invariant st)
                 (not (memberp (action stimulus)
                               '(:home-sends-invalidate
                                 :home-receives-invalidate
                                 :sharer-invalidate-cache
                                 :client-receives-shared
                                 :client-receives-exclusive
                                 :home-grants-shared
                                 :home-grants-exclusive))))
            (hsl-client-ch2-invariant (german-step st stimulus)))))

;; Well now if home sends invalidate then I dont have to prove anything.  But
;; first let me prove that it is ok.

(local
 (defthm hil-hsl-and-hil-and-ch2-implies-hsl
   (implies (and (hsl-client-ch2 hsl clients ch2 ch3 keys)
                 (hil-client-ch2 hil clients ch2 keys)
                 (g i hil)
                 (not (g i ch2)))
            (hsl-client-ch2 hsl clients (s i v ch2) ch3 keys))
   :hints (("Subgoal *1/5"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-client-ch2 on home-sends-invalidate|
   (implies (and (hsl-client-ch2-invariant st)
                 (hil-client-ch2-invariant st)
                 (equal (action stimulus) :home-sends-invalidate))
            (hsl-client-ch2-invariant (german-step st stimulus)))))

;; When home-receives invalidate it removes the hsl and therefore I have to
;; prove nothing.

(local
 (defthm hsl-client-reset-hsl
   (implies (hsl-client-ch2 hsl clients ch2 ch3 keys)
            (hsl-client-ch2 (s i nil hsl) clients ch2 (s i v ch3) keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-client-ch2 when home-receives-invalidate|
   (implies (and (hsl-client-ch2-invariant st)
                 (equal (action stimulus) :home-receives-invalidate))
            (hsl-client-ch2-invariant (german-step st stimulus)))))

;; When sharer invalidates cache it sets ch3 to invalidate-ack and hence I dont
;; have to prove anything.

(local
 (defthm hsl-client-set-ch3
   (implies (hsl-client-ch2 hsl clients ch2 ch3 keys)
            (hsl-client-ch2 hsl
                            (s i u clients)
                            (s i v ch2)
                            (s i :invalidate-ack ch3)
                            keys))
   :hints (("Subgoal *1/4"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-client-ch2 when sharer invalidates|
   (implies (and (hsl-client-ch2-invariant st)
                 (equal (action stimulus) :sharer-invalidate-cache))
            (hsl-client-ch2-invariant (german-step st stimulus)))))

;; When the client receives something it sets itself to shared or exclusive so
;; that is fine.

(local
 (defthm hsl-client-ch2-on-clients
   (implies (and (hsl-client-ch2 hsl clients ch2 ch3 keys)
                 (or (equal v :exclusive)
                     (equal v :shared)))
            (hsl-client-ch2 hsl
                            (s i v clients)
                            (s i u ch2)
                            ch3 keys))
   :hints (("Subgoal *1/3"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-client-ch2 when client sets|
   (implies (and (hsl-client-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:client-receives-shared
                            :client-receives-exclusive)))
            (hsl-client-ch2-invariant (german-step st stimulus)))))

;; And the last case, when home is granting.

(local
 (defthm hsl-client-ch2-on-home-grant
   (implies (and (hsl-client-ch2 hsl clients ch2 ch3 keys)
                 (or (equal v :grant-exclusive)
                     (equal v :grant-shared)))
            (hsl-client-ch2 (s i u hsl)
                            clients
                            (s i v ch2)
                            ch3 keys))
   :hints (("Subgoal *1/3"
            :cases ((equal i (car keys)))))))

(local
 (defthm |hsl-client-ch2 when home grants|
   (implies (and (hsl-client-ch2-invariant st)
                 (memberp (action stimulus)
                          '(:home-grants-shared
                            :home-grants-exclusive)))
            (hsl-client-ch2-invariant (german-step st stimulus)))))

;; All right so finally done.  The definition and proof of the inductive
;; invariant took way more time than I anticipated.  I missed most of the
;; subtleties of the protocol when I started with the earlier predicates.  It
;; would be interesting to see if the predicates can be made much simpler with
;; the insight I possess now, but I am too lazy to get back to them now that
;; the proof is virtually over.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Cleanup and final theorem                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now I have gotten thru the most difficult part of the proof, namely coming
;; up with a set of predicates that together imply that their conjunction holds
;; at the next step.  In this proof I have shown all predicates true on a
;; case-by-case basis already, so the final clean-up will not require the
;; definition of the predicates.  Further the final cleanup also does not
;; require the definition of german-step.  So I disable all definitions here.

;; Note: Since everything was done on a case-by-case basis the replay of the
;; proofs will be rather slow.  One way to improve the speed of proof is to
;; just remove all the individual persistence theorems, and do it all together
;; at the end.  I normally do that, but I am doing this proof more to show how
;; one comes up with such a proof in ACL2 than to speed up the certification.
;; So I leave things like this.  [In practice we define the invariant and every
;; time the persistence of invariance fails we augment the invariant with a new
;; predicate or lemma.]

(local
 (in-theory (disable coherent
                     ch2-client-shared-invariant
                     ch2-client-exclusive-invariant
                     not-heg-clients-shared-invariant
                     channel-nil-exclusive-invariant
                     hsl-client-invariant
                     invalidate-ack-clients-invariant
                     heg-exclusive-invariant
                     hsl-ch2-invariant
                     hil-heg-invariant
                     invalidate-ack-idle-invariant
                     invalidate-exclusive-invariant
                     hil-hsl-invariant
                     invalidate-ack-ch2-invariant
                     unique-hil-invariant
                     hsl-heg-invariant
                     hsl-ch3-invariant
                     invalidate-clients-invariant
                     hsl-boolean-invariant
                     hil-invalidate-invariant
                     hil-invalidate-ch2-invariant
                     valid-status-invariant
                     hcm-ch2-invariant
                     hcm-invalidate-ack-invariant
                     hil-client-ch2-invariant
                     hsl-client-ch2-invariant
                     init
                     (init)
                     german-step)))

(local
 (defun inv (st)
   (and (coherent st)
        (ch2-client-shared-invariant st)
        (ch2-client-exclusive-invariant st)
        (not-heg-clients-shared-invariant st)
        (channel-nil-exclusive-invariant st)
        (hsl-client-invariant st)
        (invalidate-ack-clients-invariant st)
        (heg-exclusive-invariant st)
        (hsl-ch2-invariant st)
        (hil-heg-invariant st)
        (hil-client-ch2-invariant st)
        (hsl-client-ch2-invariant st)
        (invalidate-ack-idle-invariant st)
        (invalidate-exclusive-invariant st)
        (invalidate-ack-ch2-invariant st)
        (hil-invalidate-ch2-invariant st)
        (hsl-heg-invariant st)
        (hsl-ch3-invariant st)
        (unique-hil-invariant st)
        (invalidate-clients-invariant st)
        (valid-status-invariant st)
        (hsl-boolean-invariant st)
        (hcm-ch2-invariant st)
        (hcm-invalidate-ack-invariant st)
        (hil-invalidate-invariant st)
        (hil-hsl-invariant st))))

;; Now the final proofs which should go thru without too much hassle.

(local
 (defthm |inv holds in initial state| (inv (init))))

(local
 (defthm |inv is inductive| (implies (inv st) (inv (german-step st stimulus)))
   :hints (("Goal"
            :cases ((equal (action stimulus) :request-shared-access)
                    (equal (action stimulus) :request-exclusive-access)
                    (equal (action stimulus) :pick-new-request)
                    (equal (action stimulus) :home-sends-invalidate)
                    (equal (action stimulus) :home-receives-invalidate)
                    (equal (action stimulus) :sharer-invalidate-cache)
                    (equal (action stimulus) :client-receives-shared)
                    (equal (action stimulus) :client-receives-exclusive)
                    (equal (action stimulus) :home-grants-shared)
                    (equal (action stimulus) :home-grants-exclusive))))))

(local
 (defthm |inv implies coherent|
   (implies (inv st) (coherent st))))

;; Of course I am done already but just for the heck of it let me prove as a
;; final theorem that inv does imply coherent and hence coherent is true of
;; every execution.  First let us define an execution of the german protocol.

(defun german-run (st stimuli)
  (if (endp stimuli) st
    (let* ((stimulus (first stimuli)))
      (german-run (german-step st stimulus) (rest stimuli)))))

(local
 (defthm |inv persists along run|
   (implies (inv st) (inv (german-run st stimuli)))))

(local
 (defthm |inv is true of all runs from init|
   (inv (german-run (init) stimuli))))

;; And the final one is a capital DEFTHM.

(DEFTHM |every run is coherent| (coherent (german-run (init) stimuli)))



