; This books demonstrates how we could model network communications between a
; client and server, and how we can interleave an attacker that would be a "Man
; in the middle" between the client and a server.  This file is the second of
; two that perform this modeling.  This file, network-state.lisp, is similar to
; the first, but it uses more advanced features of ACL2 (like defn,
; defaggregate, b*, guards, defun+ and its output signatures, etc.).

; The concepts in this book are based off David Rager's JFKr model, which can
; be found in books/projects/security/jfkr.lisp and is explained in "An
; Executable Model for JFKr", which was included in the 2009 ACL2 Workshop.

; Copyright David Rager 2012.

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


; Suppose we have the following English description of a protocol.

; There are two actors, a client/initiator and a server/responder.  In this
; case, the server is providing a simple service -- it looks for a request on
; the network (presumably sent to the responder), squares the number included
; within the request, and sends the result back on the network.

; The server will keep track of the number of requests that it has served.


; The way we model state in this book is a reasonable model.  However, there
; are of course other ways that we could have done this.  The following two
; paragraphs are intended for a slightly more experienced reader, and the
; novice reader may wish to skip them.

; In this book, we have three states: the client state, the server state, and
; the network state.  One thing that could be different is that these three
; states could be combined into one single state.  Such a decision is a
; judgment call.  The current approach makes it clear to the reader that the
; server can not change the client state.  However, even if the client state
; was embedded in one single state (and we implemented such embedding
; correctly), ACL2 should easily be able to determine (prove) that the server
; does not change the client state.

; Another difference between this model and other models is that we sequence
; the client and server steps in a relatively manual fashion (see the uses of
; "b*" below).  We could model a greater variety of attacks if we had a single
; interpreter that took a state and a list that said what sequence of steps to
; run.  This interpreter would then run the sequence of steps on the state, and
; we could prove properties about the resulting sequence.  We could also
; underspecify the sequence of steps and still attempt to prove the same
; properties.  If those properties held, despite this less well-defined
; sequence of steps, we would have more assurance in the protocol.  One
; potentially interesting way to model picking the "next step" would be to have
; an "oracle" (for an example of an oracle that returns one of two values, see
; function foo in file nondeterminism.lisp, in this same directory) that could
; indicate whether the client, server, or attacker would get to take the next
; step.  We could then attempt to prove that given the oracle returns one of
; the three values each time the interpreter is called, if the :answer field in
; the client changes from :unknown, that the value for :answer must be the
; square of the client's :number-to-square.  Of course, this property isn't
; true of the protocol described and implemented in this file.  However, if we
; were to correctly add cryptographic functions (for example, encryption and
; signed hashes), we could perhaps create a protocol that had this property.

(in-package "ACL2")

(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "misc/defun-plus" :dir :system)
(include-book "std/util/bstar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;
; Setup client state
;;;;;;;;;;;;;;;;;;;;;;;

(defn unknown-or-integerp (x) ; defn implicitly verifies a :guard of t
  (or (equal x :unknown)
      (integerp x)))

(std::defaggregate client-state
  (number-to-square answer)
  :require ((integer-p-of-client-state->number-to-square
             (integerp number-to-square))
            (unknown-or-integerp-of-client-state->answer
             (unknown-or-integerp answer)))
  :tag :client-state)

(defconst *initial-client* ; for concrete simulation
  (make-client-state :number-to-square 8
                     :answer :unknown))

;;;;;;;;;;;;;;;;;;;;;;;
; Setup server state
;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate server-state
 (requests-served)
 :require ((integerp-of-server-state->requests-served
            (integerp requests-served)
            :rule-classes ((:type-prescription))))
 :tag :server-state)

(defconst *initial-server* ; for concrete simulation
  (make-server-state :requests-served 0))

;;;;;;;;;;;;;;;;;;;;;;
; Setup network state
;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate message
  (tag payload)
  :require ((keywordp-of-message->tag
             (keywordp tag))
            (integerp-of-message->payload
             (integerp payload)
             :rule-classes ((:type-prescription))))
  :tag :message)

(defn id-p (x)

; Would rather make this a macro, but since we can't do that and use deflist,
; we later create a forward chaining rule that gives us similar functionality.

  (keywordp x))

(defthm id-p-implies-keywordp
  (implies (id-p x)
           (keywordp x))
  :rule-classes :forward-chaining)

(std::defaggregate network-packet
  (sender dest message)
  :require ((id-p-of-network-packet->sender
             (id-p sender))
            (id-p-of-network-packet->dest
             (id-p dest))
            (message-p-of-network-packet->message
             (message-p message)))
  :tag :network-packet)

(in-theory (disable id-p)) ; we want to reason about id-p, not keywordp

(defconst *initial-network* ; for concrete simulation
  nil)

(std::deflist network-state-p (x)
  (network-packet-p x)
  :elementp-of-nil nil
  :true-listp t)

(encapsulate ()

 (local (include-book "arithmetic/top" :dir :system))

 (defun+ square (x)
   (declare (xargs :guard t ; could be (integerp x)
                   :output (integerp (square x))))
   (cond ((integerp x)
          (expt x 2))
         (t 0))))

(defconst *client-id* :client)
(defconst *server-id* :server)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define retrieving a message from the network
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun retrieve-network-message (dest network-st)

; Returns the message and a new network state, which does not include the new
; message

  (declare (xargs :guard (and (id-p dest)
                              (network-state-p network-st))))
  (cond ((atom network-st)
         (mv nil nil))
        (t
         (let ((packet (car network-st)))
           (cond ((equal (network-packet->dest packet) dest)
                  (mv packet (cdr network-st)))
                 (t (mv-let (msg network-st-recursive)
                            (retrieve-network-message dest
                                                      (cdr network-st))
                            (mv msg
                                (cons (car network-st)
                                      network-st-recursive)))))))))

(defthm retrieve-network-message-returns-network-packet-p
  (implies (and (id-p dest)
                (network-state-p network-st))
           (implies (car (retrieve-network-message dest network-st))
                    (network-packet-p (mv-nth 0
                                              (retrieve-network-message dest
                                                                        network-st))))))
(defthm retrieve-network-message-returns-network-state-p
  (implies (network-state-p network-st)

; Using (cadr ...) in the below call causes a later theorem
; (SERVER-STEP1-OUTPUT-LEMMA-2) to fail, but shouldn't (mv-nth 1 ...) just
; expand to cadr since mv-nth is enabled?  Actually, probably not, since mv-nth
; is recursive and its argument isn't the base case.

           (network-state-p (mv-nth 1 (retrieve-network-message
                                       x
                                       network-st)))))

(defun+ make-square-request (value-to-square)
  (declare (xargs :guard (integerp value-to-square)
                  :output (network-packet-p (make-square-request value-to-square))))
  (make-network-packet
   :sender *client-id*
   :dest *server-id*
   :message (make-message :tag :request
                          :payload value-to-square)))

(defn print-states (client-st server-st network-st)
  (prog2$
   (cw "~%Client state is: ~x0~%" client-st)
   (prog2$
    (cw "Server state is: ~x0~%" server-st)
    (cw "Network state is: ~x0~%" network-st))))

;;;;;;;;;;;;;;;;;;;;;;;
; Client makes request
;;;;;;;;;;;;;;;;;;;;;;;

(defun+ client-step1 (client-st network-st)
  (declare (xargs :guard (and (client-state-p client-st)
                              (network-state-p network-st))
                  :output (and (client-state-p (car (client-step1 client-st
                                                                  network-st)))
                               (network-state-p (cadr (client-step1 client-st
                                                                    network-st))))))
  (mv client-st
      (cons
       (make-square-request
        (client-state->number-to-square client-st))
       network-st)))

#+demo-only ; skipped during book certification
(let ((client-st *initial-client*)
      (server-st *initial-server*)
      (network-st *initial-network*))
  (b* (((mv client-st network-st)
        (client-step1 client-st network-st)))
    (print-states client-st server-st network-st)))

(defun+ make-square-response (dest result)
  (declare (xargs :guard (and (id-p dest)
                              (integerp result))
                  :output (network-packet-p (make-square-response dest
                                                                  result))))
  (make-network-packet :sender *server-id*
                       :dest dest
                       :message (make-message :tag :answer
                                              :payload result)))

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Server creates response
;;;;;;;;;;;;;;;;;;;;;;;;;;

; Reordering the rewrite-clause-type-alist: I added the uppercase text below to
; make this work.  See the comment in rewrite-clause-type-alist.
; JSM April 7, 2013.

(DEFTHM LEMMA-ADDED-IN-TYPE-ALIST-REORDERING
  (IMPLIES
   (AND (NETWORK-STATE-P NETWORK-ST)
        (CAR (RETRIEVE-NETWORK-MESSAGE :SERVER NETWORK-ST)))
   (NETWORK-PACKET-P (CAR (RETRIEVE-NETWORK-MESSAGE :SERVER NETWORK-ST)))))

; Note: The old proof of server-step1-output-lemma-2 (generated by the defun+
; below) was quite complex: the string ``goal'' is mentioned 91 times, 3
; inductions are performed, and there are 3 forcing rounds to deal with 7
; forced subgoals.  The new proof, using the lemma above, mentions ``goal'' 12
; times, does no inductions, and one subgoal is forced.

(defun+ server-step1 (server-st network-st)
  (declare (xargs :guard (and (server-state-p server-st)
                              (network-state-p network-st))
                  :output (and (server-state-p (car (server-step1 server-st
                                                                  network-st)))
                               (network-state-p (cadr (server-step1
                                                       server-st network-st))))))
  (b* (((mv packet network-st)
        (retrieve-network-message *server-id* network-st))
       ((when (null packet))
        (prog2$ (cw "Missing packet~%")
                (mv server-st network-st))))
    (mv (change-server-state server-st
                             :requests-served
                             (+ 1 (server-state->requests-served server-st)))
        (cons
         (make-square-response
          (network-packet->sender packet)
          (square (message->payload (network-packet->message packet))))
         network-st))))

#+demo-only
(let ((client-st *initial-client*)
      (server-st *initial-server*)
      (network-st *initial-network*))
  (mv-let (client-st network-st)
          (client-step1 client-st network-st)
          (mv-let (server-st network-st)
                  (server-step1 server-st network-st)
                  (print-states client-st server-st
                                network-st))))

;;;;;;;;;;;;;;;;;;;;;;
; Client saves answer
;;;;;;;;;;;;;;;;;;;;;;

(defun+ client-step2 (client-st network-st)
  (declare (xargs :guard (and (client-state-p client-st)
                              (network-state-p network-st))
                  :output (and (client-state-p (car (client-step2 client-st
                                                                  network-st)))
                               (network-state-p (cadr (client-step2 client-st network-st))))))
  (b* (((mv packet network-st)
        (retrieve-network-message *client-id* network-st))
       ((when (null packet))
        (prog2$ (cw "Missing packet~%")
                (mv client-st network-st))))
    (mv (change-client-state
         client-st
         :answer (message->payload (network-packet->message packet)))
        network-st)))

#+demo-only
(b* ((client-st *initial-client*)
     (server-st *initial-server*)
     (network-st *initial-network*)
     ((mv client-st network-st)
      (client-step1 client-st network-st))
     (- (print-states client-st server-st network-st))
     ((mv server-st network-st)
      (server-step1 server-st network-st))
     (- (print-states client-st server-st network-st))
     ((mv client-st network-st)
      (client-step2 client-st network-st)))
  (print-states client-st server-st network-st))

;;;;;;;;;;;;;;;;;;;;;;;
; Concrete correctness
;;;;;;;;;;;;;;;;;;;;;;;

(defthm honest-square-is-good-concrete
  (b* ((client-st *initial-client*)
       (server-st *initial-server*)
       (network-st *initial-network*)
       ((mv client-st network-st)
        (client-step1 client-st network-st))
       ((mv ?server-st network-st)
        (server-step1 server-st network-st))
       ((mv client-st ?network-st)
        (client-step2 client-st network-st)))
    (equal (expt (client-state->number-to-square client-st) 2)
           (client-state->answer client-st))))

;;;;;;;;;;;;;;;;;;;;;;;
; Symbolic correctness
;;;;;;;;;;;;;;;;;;;;;;;

(defthm honest-square-is-good-symbolic-simulation
  (implies (and (client-state-p client-st-orig)
                (server-state-p server-st)
                (network-state-p network-st))
           (b* (((mv client-st network-st)
                 (client-step1 client-st-orig network-st))
                ((mv ?server-st network-st)
                 (server-step1 server-st network-st))
                ((mv client-st ?network-st)
                 (client-step2 client-st network-st)))
             (equal (expt (client-state->number-to-square client-st-orig) 2)
                    (client-state->answer client-st)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a specific attack
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun+ man-in-the-middle-specific-attack (network-st)
  (declare (xargs :guard (network-state-p network-st)
                  :output (network-state-p (man-in-the-middle-specific-attack
                                            network-st))))

; Changes the number that the client requested

  (b* (((mv original-packet network-st)
        (retrieve-network-message *server-id* network-st))
       ((when (null original-packet))
        (prog2$ (cw "Missing packet~%")
                network-st)))
    (cons (make-square-request
           (+ 1 (message->payload (network-packet->message
                                   original-packet))))
          network-st)))

#+demo-only
(b* ((client-st *initial-client*) ; not symbolic, because it has concrete initialization
     (server-st *initial-server*)
     (network-st *initial-network*)
     ((mv client-st network-st)
      (client-step1 client-st network-st))
     (- (print-states client-st server-st network-st))
     (- (cw "~%Attack!!!~%~%"))
     (network-st (man-in-the-middle-specific-attack network-st))
     (- (print-states client-st server-st network-st))
     (- (cw "~%Done attacking~%~%"))
     ((mv server-st network-st)
      (server-step1 server-st network-st))
     (- (print-states client-st server-st network-st))
     ((mv client-st network-st)
      (client-step2 client-st network-st)))
  (print-states client-st server-st network-st))

; There is no point in trying to prove the analogous concrete or symbolic
; versions of the honest-square-is-good* theorems -- they would not be true.

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define abstract attacks
;;;;;;;;;;;;;;;;;;;;;;;;;;

; We leave attack1 and attack2 completely unconstrained.  We could be a little
; more realistic and at least define versions that return a network-state-p.
; However, this difference will not affect our ability to not prove the theorem
; below (it will still be false).  Thus, we opt for the simple call to defstub,
; so that the reader can more clearly see that we allow the attacker to
; anything their heart desires to the network state.

; We define attack1 and attack2 to be functions that each take a single
; argument and return a single value -- nothing more.

(defstub attack1 (*) => *)
(defstub attack2 (*) => *)

; Technically being unable to prove the below theorem in ACL2 doesn't mean that
; the theorem isn't valid.  However, if we believed the theorem to be valid, we
; would relentlessly examine the feedback from ACL2 until we figured out either
; of (1) how to make ACL2 agree with our belief or (2) a counterexample that
; illustrates a weakness in the protocol.  In this example, we happen to know
; that the theorem isn't true (we have a such a counter-example, shown in
; function man-in-the-middle-specific-attack), so we leave it as is.

#||
(defthm |bad-square-is-good?-with-double-attack|
  (implies (and (client-state-p client-st-orig) ; is symbolic
                (server-state-p server-st)
                (network-state-p network-st))
           (b* (((mv client-st network-st)
                 (client-step1 client-st network-st))
                (network-st (attack1 network-st)) ; ATTACK!!!
                ((mv ?server-st network-st)
                 (server-step1 server-st network-st))
                (network-st (attack2 network-st)) ; ATTACK!!!
                ((mv client-st ?network-st)
                 (client-step2 client-st network-st)))
             (equal (expt (client-state->number-to-square client-st-orig) 2)
                    (client-state->answer client-st)))))
||#
