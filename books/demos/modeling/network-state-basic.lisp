; This books demonstrates how we could model network state and an attacker that
; would be a "Man in the middle" between a client and a server.  This file is
; one of two that perform this modeling.  The second file, network-state.lisp,
; is similar to this file, but it uses more advanced features of ACL2 (like
; defn, defaggregate, etc.).

; The concepts in this book are based off Rager's JFKr model, which can be
; found in books/projects/security/jfkr/jfkr.lisp and is explained in "An
; Executable Model for JFKr", by David Rager, which was included in the 2009
; ACL2 Workshop.

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

; Suppose we have the following english description of a protocol.

; There are two actors, a client/initiator and a server/responder.  In this
; case, the server is providing a simple service -- it looks for a request on
; the network (presumably sent to the responder), squares the number included
; within the request, and sends the result back on the network.

; The server will keep track of the number of requests that it has served.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defconst *initial-number-to-square* 8)

(defconst *initial-result* :unknown)

(defun initialize-client ()
  (list *initial-number-to-square*
        *initial-result*))

(defconst *initial-client-state*
  (initialize-client))

(defun valid-client-state (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (equal (length st) 2)
       (integerp (car st))
       (or (integerp (cadr st))
           (equal (cadr st) :unknown))))

(defun get-number-to-square-from-client-state (st)
  (declare (xargs :guard (valid-client-state st)))
  (car st))

(defun get-answer-from-client-state (st)
  (declare (xargs :guard (valid-client-state st)))
  (cadr st))

(defconst *intial-number-of-requests-served* 0)

(defun initialize-server ()
  (list *intial-number-of-requests-served*))

(defun valid-server-state (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (equal (length st) 1)
       (integerp (car st))
       (>= (car st) 0)))

(defconst *initial-server-state*
  (initialize-server))

(defun initialize-network ()
  nil)

(defun valid-message (msg)
  (declare (xargs :guard t))
  (and (true-listp msg)
       (equal (len msg) 3)))

(defun valid-message-list (msg-list)
  (declare (xargs :guard t))
  (cond ((atom msg-list)
         (null msg-list))
        (t (and (valid-message (car msg-list))
                (valid-message-list (cdr msg-list))))))

(defun valid-network (st)
  (declare (xargs :guard t))
  (valid-message-list st))

(defun server-function (x)
  (expt x 2))

(defconst *client-id* :client)
(defconst *server-id* :server)

(defun make-message (sender dest msg)
  (declare (xargs :guard t))
  (list sender dest msg))

(defun retrieve-network-message (receiver network-st)
; Returns the message and a new network state, which does not include the new
; message
  (declare (xargs :guard (and (or (equal receiver *client-id*)
                                  (equal receiver *server-id*))
                              (valid-network network-st))))
  (cond ((atom network-st)
         (mv nil nil))
        ((equal (cadar network-st) receiver)
         (mv (car network-st) (cdr network-st)))
        (t (mv-let (msg network-st-recursive)
                   (retrieve-network-message receiver (cdr network-st))
                   (mv msg (cons (car network-st)
                                 network-st-recursive))))))

(defun client-make-message-1 (value-to-square)
  (declare (xargs :guard t))
  (make-message *client-id* *server-id* (list :request value-to-square)))

(defun client-step1 (client-st network-st)
  (declare (xargs :guard (and (valid-client-state client-st)
                              (valid-network network-st))))
  (mv client-st
      (cons
       (client-make-message-1
        (get-number-to-square-from-client-state client-st))
       network-st)))

(defun print-states (client-st server-st network-st)
  (prog2$
   (cw "Client state is: ~x0~%" client-st)
   (prog2$
    (cw "Server state is: ~x0~%" server-st)
    (cw "Network state is: ~x0~%" network-st))))

#+demo-only ; skipped during book certification
(let ((client-st (initialize-client))
      (server-st (initialize-server))
      (network-st (initialize-network)))
  (mv-let (client-st network-st)
          (client-step1 client-st network-st)
          (print-states client-st server-st network-st)))

(defun get-input-from-client-request (msg)
  (declare (xargs :guard (valid-message msg)
                  :verify-guards nil))
  (cadr (caddr msg)))

(defun server-make-message-1 (result)
  (declare (xargs :guard t))
  (make-message *server-id* *client-id*
                (list :answer result)))

(defun server-step1 (server-st network-st)
  (declare (xargs :guard (and (valid-server-state server-st)
                              (valid-network network-st))
                  :verify-guards nil))
  (mv-let (message network-st)
          (retrieve-network-message *server-id* network-st)
          (mv (list (+ 1 (car server-st))) ; todo abstract server state
              (cons
               (server-make-message-1
                (server-function (get-input-from-client-request message)))
               network-st))))

#+demo-only
(let ((client-st (initialize-client))
      (server-st (initialize-server))
      (network-st (initialize-network)))
  (mv-let (client-st network-st)
          (client-step1 client-st network-st)
          (mv-let (server-st network-st)
                  (server-step1 server-st network-st)
                  (print-states client-st server-st
                                network-st))))

(defun client-step2 (client-st network-st)
  (mv-let (message network-st)
          (retrieve-network-message *client-id* network-st)
          (mv (list (car client-st)
                    (cadr (caddr message))) ; todo make an assoc off :answer
              network-st)))

#+demo-only
(let ((client-st (initialize-client))
      (server-st (initialize-server))
      (network-st (initialize-network)))
  (mv-let (client-st network-st)
          (client-step1 client-st network-st)
          (mv-let (server-st network-st)
                  (server-step1 server-st network-st)
                  (mv-let (client-st network-st)
                          (client-step2 client-st
                                        network-st)
                          (print-states client-st server-st
                                        network-st)))))


(defun man-in-the-middle-attacks-once (network-st)

; Changes the number requested

  (mv-let (original-message network-st)
          (retrieve-network-message *server-id* network-st)
          (cons (client-make-message-1 (1+ (cadr (caddr original-message))))
                network-st)))

#+demo-only
(let ((client-st (initialize-client))
      (server-st (initialize-server))
      (network-st (initialize-network)))
  (mv-let (client-st network-st)
          (client-step1 client-st network-st)
          (let ((network-st (man-in-the-middle-attacks-once network-st)))
            (mv-let (server-st network-st)
                    (server-step1 server-st network-st)
                    (print-states client-st server-st network-st)))))

#+demo-only
(let ((client-st (initialize-client))
      (server-st (initialize-server))
      (network-st (initialize-network)))
  (mv-let (client-st network-st)
          (client-step1 client-st network-st)
          (prog2$
           (print-states client-st server-st network-st)
           (mv-let (server-st network-st)
                   (server-step1 server-st
                                 (man-in-the-middle-attacks-once network-st))
                   (print-states client-st server-st network-st)))))

(defthm honest-square-is-good-concrete
  (let ((client-st (initialize-client)) ; not symbolic, because it has concrete initialization
        (server-st (initialize-server))
        (network-st (initialize-network)))
    (mv-let (client-st network-st)
            (client-step1 client-st network-st)
            (mv-let (server-st network-st)
                    (server-step1 server-st network-st)
                    (declare (ignore server-st))
                    (mv-let (client-st network-st)
                            (client-step2 client-st network-st)
                            (declare (ignore network-st))
                            (equal (expt (get-number-to-square-from-client-state client-st) 2)
                                   (get-answer-from-client-state client-st)))))))

(defthm honest-square-is-good-symbolic-simulation
  (implies (and (valid-client-state client-st) ; is symbolic
                (valid-server-state server-st)
                (valid-network network-st))
           (mv-let (client-st network-st)
                   (client-step1 client-st network-st)
                   (mv-let (server-st network-st)
                           (server-step1 server-st network-st)
                           (declare (ignore server-st))
                           (mv-let (client-st network-st)
                                   (client-step2 client-st network-st)
                                   (declare (ignore network-st))
                                   (equal (expt (get-number-to-square-from-client-state client-st) 2)
                                          (get-answer-from-client-state client-st)))))))

(encapsulate (((attack1 *) => *))
             (local (defun attack1 (x) (declare (ignore x))
                      nil)))

(encapsulate (((attack2 *) => *))
             (local (defun attack2 (x) (declare (ignore x))
                      nil)))

(must-fail

; Technically being unable to prove this theorem in ACL2 doesn't mean that the
; theorem isn't valid.  However, if we believed the theorem to be valid, we
; would relentlessly examine the feedback from ACL2 until we figured out how to
; make ACL2 agree with our belief.  But, we happen to know that the theorem
; isn't true, so we leave it as is.

 (defthm |bad-square-is-good?-with-single-attack|
   (implies
    (and (valid-client-state client-st) ; is symbolic
         (valid-server-state server-st)
         (valid-network network-st))
    (mv-let (client-st network-st)
            (client-step1 client-st network-st)
            (mv-let (server-st network-st)
                    (server-step1 server-st (attack1 network-st))
                    (declare (ignore server-st))
                    (mv-let (client-st network-st)
                            (client-step2 client-st network-st)
                            (declare (ignore network-st))
                            (equal (expt (get-number-to-square-from-client-state client-st) 2)
                                   (get-answer-from-client-state client-st))))))))

(must-fail

; Technically being unable to prove this theorem in ACL2 doesn't mean that the
; theorem isn't valid.  However, if we believed the theorem to be valid, we
; would relentlessly examine the feedback from ACL2 until we figured out how to
; make ACL2 agree with our belief.  But, we happen to know that the theorem
; isn't true, so we leave it as is.

 (defthm |bad-square-is-good?-with-double-attack|
   (implies
    (and (valid-client-state client-st) ; is symbolic
         (valid-server-state server-st)
         (valid-network network-st))
    (mv-let (client-st network-st)
            (client-step1 client-st (attack1 network-st))
            (mv-let (server-st network-st)
                    (server-step1 server-st (attack2 network-st))
                    (declare (ignore server-st))
                    (mv-let (client-st network-st)
                            (client-step2 client-st network-st)
                            (declare (ignore network-st))
                            (equal (expt (get-number-to-square-from-client-state client-st) 2)
                                   (get-answer-from-client-state client-st))))))))
