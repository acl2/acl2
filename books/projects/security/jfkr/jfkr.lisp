; Copyright David Rager 2006

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


; A Model for key establishment protocol JFKr
;
; The goal is to create an executable version of JFKr and then reason about it,
; proving some properties about it
;
;
; JFKr has the following message exchanges.  A very brief description of some
; of the abbreviations is included.
; I == Initiator
; R == Recipient
; N == Nonce (random value)
;
; I -> R   Ni, xi
;   xi == g^(di)
; R -> I   Ni, Nr, xr, gr, tr
;   xr == g^(dr), gr == DH group, tr == hash-under-kr (xr, Nr, Ni, IPi)
; I -> R   Ni, Nr, xi, xr, tr, ei, hi
;   ei == enc-under-ks (IDi, IDr, sai, signature-under-ki (Ni, Nr, xi, xr, gr))
;   hi == hash-under-ka("i", ei)
; R -> I   er, hr
;   er == enc-under-ks (IDr, sar, signature-under-kr (Ni, Nr, xi, xr))
;   hi == hash-under-ka("r", er)


; This model takes advantage of the encapsulate/defstub feature to introduce
; non-determinism.

(in-package "JFKR")

; These allow me to use a macro to bind variables to their accessors in a
; standard fashion without retyping the accesses and calculations everytime.  I
; could retype, but it results in really long looking code and is painful to
; read

;(set-inhibit-warnings "non-rec" "subsume")

(include-book "encryption")
(include-book "diffie-helman")
(include-book "random")
(include-book "std/testing/assert-bang" :dir :system)

(defun identityp (x)
  (declare (xargs :guard t))
  (integerp x))

(defmacro defaccessor (name)
  `(defun ,name (alist)
     (declare (xargs :guard (alistp alist)))
      (cdr (assoc-equal (quote ,name) alist))))

; Accessors that work for both the initiator and responder
(defaccessor id)
(defaccessor nonce)
(defaccessor dh-exponent)
(defaccessor private-key)
(defaccessor ip)
(defaccessor sa)

; Just responder
(defaccessor g)
(defaccessor b)

; Public values
(defaccessor public-key-i)
(defaccessor public-key-r)


(defun initiator-constantsp (lst)
  (declare (xargs :guard (alistp lst)))
  (and (alistp lst)
       (integerp (id lst))
       (integerp (nonce lst))
       (integerp (dh-exponent lst))
       (integerp (private-key lst))
       (integerp (ip lst))
       (integerp (sa lst))
       ;; more interesting parts we actually need
       (<= 1 (nonce lst))
       (<= 1 (dh-exponent lst))))

(defun responder-constantsp (lst)
  (declare (xargs :guard (alistp lst)))
  (and (alistp lst)
       (integerp (id lst))
       (integerp (nonce lst))
       (integerp (dh-exponent lst))
       (integerp (private-key lst))
       (integerp (ip lst))
       (integerp (sa lst))
       ;; more interesting parts we actually need
       (<= 1 (nonce lst))
       (<= 1 (dh-exponent lst))

       (integerp (g lst))
       (integerp (b lst))
       (<= 1 (g lst))
       (<= 1 (b lst))))

(defun public-constantsp (lst)
  (declare (xargs :guard (alistp lst)))
  (and (alistp lst)
       (integerp (public-key-i lst))
       (integerp (public-key-r lst))))


; Accessors for the constants
(defun initiator-constants (lst)
  (declare (xargs :guard (alistp lst)))
  (cdr (assoc-equal 'initiator-constants lst)))

(defun responder-constants (lst)
  (declare (xargs :guard (alistp lst)))
  (cdr (assoc-equal 'responder-constants lst)))

(defun public-constants (lst)
  (declare (xargs :guard (alistp lst)))
  (cdr (assoc-equal 'public-constants lst)))


(defun constantsp (lst)
  (declare (xargs :guard (and (alistp lst)
                              (alistp (initiator-constants lst))
                              (alistp (responder-constants lst))
                              (alistp (public-constants lst)))
                  :guard-hints (("Goal" :in-theory (enable CRYPTO::keyp)))))

  (and (initiator-constantsp (initiator-constants lst))
       (responder-constantsp (responder-constants lst))
       (public-constantsp (public-constants lst))

       (CRYPTO::public-private-key-pairp (public-key-r (public-constants lst))
                                         (private-key (responder-constants lst)))
       (CRYPTO::public-private-key-pairp (public-key-i (public-constants lst))
                                         (private-key (initiator-constants lst)))))

(in-theory (disable id nonce dh-exponent private-key ip sa g b public-key-i public-key-r))

(defthm can-disable-constant-list-accessors
  (implies (constantsp lst)
           (and (initiator-constantsp (initiator-constants lst))
                (responder-constantsp (responder-constants lst))
                (public-constantsp (public-constants lst)))))

(in-theory (disable initiator-constants responder-constants public-constants))


; Setup sample constants for example executions.

(defconst *random-seed1* 412381)
(defconst *random-seed2* 598171)

(defconst *initiator-constants*
  (let* ((id (CRYPTO::genrandom *random-seed1*))
         (nonce (CRYPTO::genrandom id))
         (dh-exponent (CRYPTO::genrandom nonce))
         (private-key (CRYPTO::genrandom dh-exponent))
         (ip (CRYPTO::genrandom private-key))
         (sa (CRYPTO::genrandom ip)))
    (list (cons 'id id)
          (cons 'nonce nonce)
          (cons 'dh-exponent dh-exponent)
          (cons 'private-key private-key)
          (cons 'ip ip)
          (cons 'sa sa))))

; Test that instantiated initiator constant list is an initiator constant list.
(ACL2::assert! (initiator-constantsp *initiator-constants*))



(defconst *responder-constants*
  (let* ((id (CRYPTO::genrandom *random-seed2*))
         (nonce (CRYPTO::genrandom id))
         (dh-exponent (CRYPTO::genrandom nonce))
         (private-key (CRYPTO::genrandom dh-exponent))
         ;; don't need ip for responder but makes life simpler
         (ip (CRYPTO::genrandom private-key))
         (sa (CRYPTO::genrandom ip))
         (g (CRYPTO::genrandom sa))
         (b (CRYPTO::genrandom g)))
    (list (cons 'id id)
          (cons 'nonce nonce)
          (cons 'dh-exponent dh-exponent)
          (cons 'private-key private-key)
          (cons 'ip ip)
          (cons 'sa sa)
          (cons 'g g)
          (cons 'b b))))

; Test that instantiated responder constant list is an responder constant list.
(ACL2::assert! (responder-constantsp *responder-constants*))




(defconst *public-constants*
  (let* ((public-key-i (- (private-key *initiator-constants*)))
         (public-key-r (- (private-key *responder-constants*))))
    (list (cons 'public-key-i public-key-i)
          (cons 'public-key-r public-key-r))))

; It's good that we don't relate the public keys to the private keys in the
; abstratction, because I later assume that the keys are not valid pairs (by
; saying they're negatives of each other).

(defconst *constants*
  (list (cons 'initiator-constants *initiator-constants*)
        (cons 'responder-constants *responder-constants*)
        (cons 'public-constants *public-constants*)))

; Test that instantiated constant list is a constant list.
(ACL2::assert! (constantsp *constants*))


(defconst *string-quote-initiator* 4)
(defconst *string-quote-responder* 5)


(defun msg1 (s)
  (declare (xargs :guard (alistp s)))
  (cdr (assoc-equal 1 s)))

(defun msg2 (s)
  (declare (xargs :guard (alistp s)))
  (cdr (assoc-equal 2 s)))

(defun msg3 (s)
  (declare (xargs :guard (alistp s)))
  (cdr (assoc-equal 3 s)))

(defun msg4 (s)
  (declare (xargs :guard (alistp s)))
  (cdr (assoc-equal 4 s)))

(defmacro defmessage-accessor (label)
  (let ((symbol
         (ACL2::intern-in-package-of-symbol
          (coerce (append (explode-atom label 10)
                          (explode-atom '-msg 10)) 'string) 'msg3)))
  `(defun ,symbol (msg)
     (declare (xargs :guard (alistp msg)))
     (cdr (assoc-equal (quote ,label) msg)))))

(defmessage-accessor Xi)
(defmessage-accessor Src-ip)
(defmessage-accessor Ni)
(defmessage-accessor Nr)
(defmessage-accessor Xr)
(defmessage-accessor G)
(defmessage-accessor B)
(defmessage-accessor Tr)
(defmessage-accessor Xi)
(defmessage-accessor Hi)
(defmessage-accessor Er)
(defmessage-accessor Ei)
(defmessage-accessor Hr)


(defund compute-tr (Ni Nr Xr IPi Kr)
  (CRYPTO::compute-keyed-hash (list Xr Nr Ni IPi) Kr))

(defund compute-session-key (Ni Nr dh-key)
  (CRYPTO::compute-keyed-hash (list Ni Nr) dh-key))

(defund compute-sig-Ki (Ni Nr Xi Xr G B private-key-i)
  (CRYPTO::compute-signature-list (list Ni Nr Xi Xr g b)
                                  private-key-i))

(defund verify-sig-Ki (Ni Nr Xi Xr G B public-key-i)
  (CRYPTO::verify-signature-list (list Ni Nr Xi Xr G B) public-key-i))

(defthm signature-verifies-Ki
  (let ((lst (list Ni Nr Xi Xr G B)))
    (implies (and (CRYPTO::public-private-key-pairp public-key-i private-key-i)
                  (CRYPTO::encryptable-listp lst))
             (equal (compute-sig-Ki Ni Nr Xi Xr G B private-key-i)
                    (verify-sig-Ki  Ni Nr Xi Xr G B public-key-i))))
  :hints (("Goal" :in-theory (enable compute-sig-Ki verify-sig-ki))))


(defund compute-sig-Kr (Ni Nr Xi Xr private-key-r)
  (CRYPTO::compute-signature-list (list Ni Nr Xi Xr)
                                  private-key-r))

(defund verify-sig-Kr (Ni Nr Xi Xr public-key-r)
  (CRYPTO::verify-signature-list (list Ni Nr Xi Xr) public-key-r))

(defthm signature-verifies-Kr
  (implies (and (CRYPTO::public-private-key-pairp public-key-r private-key-r)
                (CRYPTO::encryptable-listp (list Ni Nr Xi Xr G B)))
           (equal (compute-sig-Kr Ni Nr Xi Xr private-key-r)
                  (verify-sig-Kr  Ni Nr Xi Xr public-key-r)))
  :hints (("Goal" :in-theory (enable compute-sig-Kr verify-sig-Kr
                                     CRYPTO::encryptable-listp))))

(defun compute-Ei (IDi SAi SigKi session-key)
  (CRYPTO::encrypt-symmetric-list (list IDi SAi SigKi)
                                        session-key))
(defthm nth2-of-compute-Ei-is-SigKi
  (implies (force (integer-listp (list IDi SAi SigKi)))
           (equal (nth 2 (CRYPTO::decrypt-symmetric-list
                          (CRYPTO::encrypt-symmetric-list (list IDi SAi SigKi) session-key)
                          session-key))
                  SigKi))
  :hints (("Goal" :in-theory (enable CRYPTO::ENCRYPTABLE-LISTP))))


(defund compute-Hi (Ei session-key)
  (CRYPTO::compute-keyed-hash (append (list *string-quote-initiator*) Ei)
                              session-key))

(defun compute-Er (IDr SAr SigKr session-key)
  (CRYPTO::encrypt-symmetric-list (list IDr SAr SigKr)
                                  session-key))

(defund compute-Hr (Er session-key)
  (CRYPTO::compute-keyed-hash (append (list *string-quote-responder*) Er)
                              session-key))

; Let-with-bindings-from-all-constants requires that a variable of the name
; constants and type constantsp be within lexical scope

; the -c's in this function stand for "Derived from a global view of the constants"

(defmacro let-with-bindings-from-all-constants (&rest body)
  `(let* (
          ;; Fetch constant lists first
          (initiator-constants (initiator-constants constants))
          (responder-constants (responder-constants constants))
          (public-constants (public-constants constants))

          ;; Fetch more primitive items
          (IDi-c (id initiator-constants))
          (IDr-c (id responder-constants))
          (Ni-c (nonce initiator-constants))
          (Nr-c (nonce responder-constants))
          (dh-exponent-i-c (dh-exponent initiator-constants))
          (dh-exponent-r-c (dh-exponent responder-constants))
          (private-key-i-c (private-key initiator-constants))
          (private-key-r-c (private-key responder-constants))
          (IPi-c (ip initiator-constants))
          (IPr-c (ip responder-constants))
          (SAi-c (sa initiator-constants))
          (SAr-c (sa responder-constants))
          (G-c (g responder-constants))
          (B-c (b responder-constants))

          ;; Calculate the more complex items
          (public-key-i-c (public-key-i public-constants))
          (public-key-r-c (public-key-r public-constants))

          (SrcIP-c IPi-c)

          (Xi-c (CRYPTO::compute-public-dh-value G-c dh-exponent-i-c B-c))
          (Xr-c (CRYPTO::compute-public-dh-value G-c dh-exponent-r-c B-c))

          (Tr-c (compute-tr Xr-c Nr-c Ni-c SrcIP-c private-key-r-c))

          (dh-key-c (CRYPTO::compute-dh-key Xr-c dh-exponent-i-c B-c))
          (session-key-c (compute-session-key Ni-c Nr-c dh-key-c))

          (SigKi-c (compute-sig-Ki Ni-c Nr-c Xi-c Xr-c G-c B-c private-key-i-c))
          (SigKr-c (compute-sig-Kr Ni-c Nr-c Xi-c Xr-c private-key-r-c))


          (Ei-c (compute-Ei IDi-c SAi-c SigKi-c session-key-c))

          (Hi-c (compute-Hi Ei-c session-key-c))

          (Er-c (compute-Er IDr-c SAr-c SigKr-c session-key-c))

          (Hr-c (compute-Hr Er-c session-key-c)))

     ,@body))



(defmacro let-with-bindings-from-initiator-constants (body)
  `(let* (
          ;; Fetch from Initiator's Constants
          (IDi-c (id initiator-constants))
          (Ni-c (nonce initiator-constants))
          (dh-exponent-i-c (dh-exponent initiator-constants))
          (private-key-i-c (private-key initiator-constants))
          (IPi-c (ip initiator-constants))
          (SAi-c (sa initiator-constants))

          ;; Fetch from Public Constants
          (public-key-i-c (public-key-i public-constants))
          (public-key-r-c (public-key-r public-constants)))
     ,body))


(defmacro let-with-bindings-from-responder-constants (body)
  `(let* (
          ;; Fetch from responder's constants
          (IDr-c (id responder-constants))
          (Nr-c (nonce responder-constants))
          (dh-exponent-r-c (dh-exponent responder-constants))
          (private-key-r-c (private-key responder-constants))
          (IPr-c (ip responder-constants))
          (SAr-c (sa responder-constants))
          (G-c (g responder-constants))
          (B-c (b responder-constants))

          ;; Fetch from public constants
          (public-key-i-c (public-key-i public-constants))
          (public-key-r-c (public-key-r public-constants)))
     ,body))


(defun well-formed-msg1p (msg)
  (declare (xargs :guard t))
  (and (alistp msg)
       (integerp (Ni-msg msg))
       (integerp (src-ip-msg msg))))

; Defnitions of good and bad messages.

(defun badly-forged-msg1p (msg responder-state initiator-constants responder-constants)
  (declare (ignore msg responder-state initiator-constants responder-constants))
  ;; There is no way for the responder to detect a bad forgery after msg1,
  ;; because there's nothing signed by the initiator in this step.  Consider
  ;; changing the name and returning t.
  nil)

(defun well-formed-msg2p (msg)
  (declare (xargs :guard t))
  (and (alistp msg)
       (integerp (Ni-msg msg))
       (integerp (Nr-msg msg))
       (<= 1 (Nr-msg msg))
       (integerp (Xr-msg msg))
       (<= 1 (Xr-msg msg))
       (integerp (G-msg  msg))
       (integerp (B-msg  msg))
       (integerp (Tr-msg msg))))

(defun badly-forged-msg2p (msg initiator-state initiator-constants responder-constants)
  (declare (ignore msg initiator-state initiator-constants responder-constants))
  ;; There is no way for the initiator to tell if msg 2 was forged or not.
  ;; Consider changing the name and returning t.
  nil)


(defun well-formed-msg3p (msg)
  (declare (xargs :guard t))
  (and (alistp msg)
       (integerp (Ni-msg msg))
       (integerp (Nr-msg msg))
       (integerp (Xi-msg msg))
       (<= 0 (Xi-msg msg))
       (integerp (Xr-msg msg))
       (<= 0 (Xr-msg msg))
       (integerp (Tr-msg msg))
       (integer-listp (Er-msg msg))
       (integerp (Hi-msg msg))
       (integerp (Src-ip-msg msg))))


(defun well-formed-msg4p (msg)
  (declare (xargs :guard t))
  (and (alistp msg)
       (integer-listp (Er-msg msg))
       (integerp (Hr-msg msg))))



(defun well-formed-network-state-after-step1p (network)
  (declare (xargs :guard (and (alistp network)
                              (alistp (msg1 network))
                              (alistp (msg2 network))
                              (alistp (msg3 network))
                              (alistp (msg4 network)))))
  (well-formed-msg1p (msg1 network)))


(defun well-formed-network-state-after-step2p (network)
  (declare (xargs :guard (and (alistp network)
                              (alistp (msg1 network))
                              (alistp (msg2 network))
                              (alistp (msg3 network))
                              (alistp (msg4 network)))))
  (and (well-formed-msg1p (msg1 network))
       (well-formed-msg2p (msg2 network))))



(defun well-formed-network-state-after-step3p (network)
  (declare (xargs :guard (and (alistp network)
                              (alistp (msg1 network))
                              (alistp (msg2 network))
                              (alistp (msg3 network))
                              (alistp (msg4 network)))))
  (and (well-formed-msg1p (msg1 network))
       (well-formed-msg2p (msg2 network))
       (well-formed-msg3p (msg3 network))))


(defun well-formed-network-state-after-step4p (network)
  (declare (xargs :guard (and (alistp network)
                              (alistp (msg1 network))
                              (alistp (msg2 network))
                              (alistp (msg3 network))
                              (alistp (msg4 network)))))
  (and (well-formed-msg1p (msg1 network))
       (well-formed-msg2p (msg2 network))
       (well-formed-msg3p (msg3 network))
       (well-formed-msg4p (msg4 network))))


(defun well-formed-network-statep (network)
  (declare (xargs :guard (and (alistp network)
                              (alistp (msg1 network))
                              (alistp (msg2 network))
                              (alistp (msg3 network))
                              (alistp (msg4 network)))))
  (or (null network)
      (well-formed-network-state-after-step1p network)
      (well-formed-network-state-after-step2p network)
      (well-formed-network-state-after-step3p network)
      (well-formed-network-state-after-step4p network)))


(defmacro defstate-accessor (state-property)
  `(defun ,state-property (my-state)
     (declare (xargs :guard (alistp my-state)))
     (cdr (assoc-equal (quote ,state-property) my-state))))


(defstate-accessor Ni)
(defstate-accessor Nr)
(defstate-accessor Xi)
(defstate-accessor Xr)
(defstate-accessor Id-r)
(defstate-accessor Id-i)
(defstate-accessor session-key)
(defstate-accessor success)
(defstate-accessor done)


(defun protocol-failure (my-state)
  (declare (xargs :guard (alistp my-state)))
  (and (null (success my-state))
       (done my-state)))

(defun protocol-success (my-state)
  (declare (xargs :guard (alistp my-state)))
  (and (success my-state)
       (done my-state)))


(defund get-mv-protocol-failure ()
  (mv nil (acons 'done t nil)))

(defthm get-mv-protocol-failure-is-failure
  (equal (protocol-failure (mv-nth 1 (get-mv-protocol-failure)))
         t))

(defthm get-mv-protocol-failure-is-not-success
  (equal (protocol-success (mv-nth 1 (get-mv-protocol-failure)))
         nil))

(defthm car-of-mv-protocol-failure-is-nil
  (equal (car (get-mv-protocol-failure))
         nil))

(in-theory (disable (:executable-counterpart get-mv-protocol-failure)))


; Define predicates on the states of the initiator and responder

(defun initiator-state-after-step-1p (s)
  (declare (xargs :guard (alistp s)))
  (declare (ignore s))
  t)

(defun initiator-state-after-step-2p (s)
  (declare (xargs :guard (alistp s)))
  (and (initiator-state-after-step-1p s)
       (integerp (Nr s))
       (integerp (Xi s))
       (<= 0 (Xi s))
       (integerp (Xr s))
       (<= 0 (Xr s))
       (integerp (session-key s))))

(defun initiator-state-after-step-3p (s)
  (declare (xargs :guard (alistp s)))
  (and (initiator-state-after-step-2p s)
       (success s)
       (done s)
       (identityp (id-r s))))

(defun responder-state-after-step-1p (s)
  (declare (xargs :guard (alistp s)))
  (declare (ignore s))
  ;; responder doesn't need to remember any state after step 1
  t)


(defun responder-state-after-step-2p (s)
  (declare (xargs :guard (alistp s)))
  (and (responder-state-after-step-1p s)
       (session-key s)
       (id-i s)
       (assoc-equal 'success s)
       (assoc-equal 'done s)))


(set-verify-guards-eagerness 0)


; We use an auxilury function to ensure that we get abstraction.  Basically, we
; will use the normal function to check that all data is "correct", and that it
; matches what we can check so far.  If we encounter an error, we assume the
; presence of an attacker and remove all network messages (signals an abort)
; and mark ourselves as unsuccessful

(defun initiator-step1-aux (network-s my-s my-constants public-constants)
  (declare (ignore public-constants))
  (let* ((network-update (list (cons 'Ni (nonce my-constants))
                               (cons 'Src-ip (ip my-constants))))
         (my-update nil))
    (mv (acons 1 network-update network-s)
        (append my-update my-s))))

(defun initiator-step1-prev-msg-ok ()
  ;; there is no message to check, since the initiator is @ the beginning
  t)


(defun initiator-step1 (network-s my-s my-constants public-constants)
; doesn't matter who responder is - just use their key
  (declare (xargs :guard (and (initiator-constantsp my-constants)
                              (public-constantsp public-constants)
                              (alistp network-s)
                              (alistp my-s))
                  :guard-hints (("Goal" :do-not '(eliminate-destructors generalize)))))

  (if (initiator-step1-prev-msg-ok)
      (initiator-step1-aux network-s my-s my-constants public-constants)
    (get-mv-protocol-failure)))


(defthm initator-step1-acting-on-network-produces-well-formed-msg
  (implies (and (initiator-constantsp initiator-constants)
                (public-constantsp public-constants))
           (mv-let
            (network-s-after-1 initiator-s-after-1)
            (initiator-step1 network-s initiator-s initiator-constants public-constants)
            (and (well-formed-network-state-after-step1p network-s-after-1)
                 (initiator-state-after-step-1p initiator-s-after-1)))))


(defun run-1-step-honest (network-s initiator-constants responder-constants
                                    public-constants initiator-s responder-s)
  (declare (ignore responder-constants))
  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)

   (mv network-s-after-1
       initiator-s-after-1
       responder-s)))
#|
(run-1-step-honest nil
                   *initiator-constants*
                   *responder-constants*
                   *public-constants*
                   nil
                   nil)
|#

(defun responder-step1-aux (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (responder-constantsp my-constants)
                              (public-constantsp public-constants)))
           (ignore public-constants))

    (let* ((prev-msg (msg1 network-s))

           (Ni (ni-msg prev-msg))
           (Src-ip (Src-ip-msg prev-msg))

           (Nr (nonce my-constants))

           (g (g my-constants))
           (dh-exponent (dh-exponent my-constants))
           (b (b my-constants))

           (Xr (CRYPTO::compute-public-dh-value g dh-exponent b))

           (private-key (private-key my-constants))

           (Tr (compute-tr Xr Nr Ni src-ip private-key))

           (network-update (list (cons 'Ni Ni)
                                 (cons 'Nr Nr)
                                 (cons 'Xr Xr)
                                 (cons 'G G)
                                 (cons 'B B)
                                 (cons 'Tr Tr)))
           ;; no real update to my state, since I'm throwing it away - stateless
           (my-update nil))

      (mv (acons 2 network-update network-s)
          (append my-update my-s))))

(defun responder-step1-prev-msg-ok (msg)
  (declare (xargs :guard (alistp msg)))
  (well-formed-msg1p msg))

(defun responder-step1 (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (responder-constantsp my-constants)
                              (public-constantsp public-constants))))

  ;; If the network isn't well formed, then there's a problem and abort
  ;; If the other party takes interest in reading the network later, the
  ;; attacker must reforge all messages, but in theory the attacker won't be
  ;; able to forge parts neccessary for the other party to finish the protocol
  ;; succesfully, and the other party will also fail - we want to prove this

  (if (responder-step1-prev-msg-ok (msg1 network-s))
      (responder-step1-aux network-s my-s my-constants public-constants)
    (get-mv-protocol-failure)))


(defthm poorly-formed-network-msg1-yields-failure-for-responder
  (implies (not (well-formed-msg1p (msg1 network-s-after-1)))
           (mv-let
            (network-s-after-2 responder-s-after-2)
            (responder-step1 network-s-after-1 responder-s responder-constants
                             public-constants)
            (declare (ignore network-s-after-2))
            (protocol-failure responder-s-after-2)))
  :hints (("Goal" :in-theory (disable
                              well-formed-network-state-after-step1p))))

; Later we'll want to show that a well-formed message that's missing a property
; yields failure

(defun run-2-steps-honest (network-s initiator-constants responder-constants
                                    public-constants initiator-s responder-s)

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)

   (mv-let
    (network-s-after-2 responder-s-after-2)
    (responder-step1 network-s-after-1 responder-s responder-constants
                     public-constants)


    (mv network-s-after-2
        initiator-s-after-1
        responder-s-after-2))))

#|
(run-2-steps-honest nil
                   *initiator-constants*
                   *responder-constants*
                   *public-constants*
                   nil
                   nil)
|#

; initiator is processing and sending message
(defun initiator-step2-aux (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (initiator-constantsp my-constants)
                              (public-constantsp public-constants)))
           (ignore public-constants))

    (let* (
           (prev-msg (msg2 network-s))


           (Ni (nonce my-constants))
           (Nr (Nr-msg prev-msg))

           (dh-exponent (dh-exponent my-constants))

           (G (G-msg prev-msg))
           (B (B-msg prev-msg))

           (Xi (CRYPTO::compute-public-dh-value g dh-exponent b))
           (Xr (Xr-msg prev-msg))
           (Tr (Tr-msg prev-msg))

           (ID-i (id my-constants))
           ;; ommitting id-r since it's not always there

           (SA-i (sa my-constants))

           (private-key (private-key my-constants))

           (Sig-Ki (compute-sig-Ki Ni Nr Xi Xr G B private-key))

           (dh-key (CRYPTO::compute-dh-key Xr dh-exponent b))
           (session-key (compute-session-key Ni Nr dh-key))


           (Ei (compute-ei ID-i SA-i Sig-Ki session-key))

           (Hi (compute-hi Ei Session-key))

           (src-ip (ip my-constants))

           (network-update
            (list (cons 'Ni Ni)
                  (cons 'Nr Nr)
                  (cons 'Xi Xi)
                  (cons 'Xr Xr)
                  (cons 'Tr Tr)
                  (cons 'Ei Ei)
                  (cons 'Hi Hi)
                  (cons 'Src-ip Src-ip)))

           (my-update
            ;; don't need to save DH key, could comment ni and xi
            (list (cons 'Ni Ni)
                  (cons 'Nr Nr)
                  (cons 'Xi Xi)
                  (cons 'Xr Xr)
                  (cons 'session-key session-key))))

    (mv
     (acons 3 network-update network-s)
     (append my-update my-s))))

(defun initiator-step2-prev-msg-ok (msg2 my-s my-constants public-constants)
  (declare (ignore my-s public-constants))
  (and (well-formed-msg2p msg2)
       (equal (Ni-msg msg2) (nonce my-constants))))


(defun initiator-step2 (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (initiator-constantsp my-constants)
                              (public-constantsp public-constants))))

  (if (initiator-step2-prev-msg-ok (msg2 network-s) my-s my-constants
                                   public-constants)
      (initiator-step2-aux network-s my-s my-constants public-constants)
    (get-mv-protocol-failure)))



(defthm poorly-formed-network-msg2-yields-failure-for-initiator
  (implies (not (well-formed-msg2p (msg2 network-s-after-2)))
           (mv-let
            (network-s-after-3 initiator-s-after-3)
            (initiator-step2 network-s-after-2 initiator-s-after-1
                             initiator-constants public-constants)
            (declare (ignore network-s-after-3))
            (protocol-failure initiator-s-after-3)))
  :hints (("Goal" :in-theory (disable well-formed-network-state-after-step2p))))


(defun run-3-steps-honest (network-s initiator-constants responder-constants
                                     public-constants initiator-s responder-s)

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)

   (mv-let
    (network-s-after-2 responder-s-after-2)
    (responder-step1 network-s-after-1 responder-s responder-constants
                     public-constants)


  (mv-let
   (network-s-after-3 initiator-s-after-3)
   (initiator-step2 network-s-after-2 initiator-s-after-1 initiator-constants
                    public-constants)


    (mv network-s-after-3
        initiator-s-after-3
        responder-s-after-2)))))

#|
(run-3-steps-honest nil
                   *initiator-constants*
                   *responder-constants*
                   *public-constants*
                   nil
                   nil)
|#



;; responder is processing and sending message
(defun responder-step2-aux (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (responder-constantsp my-constants)
                              (public-constantsp public-constants))))
    (let* ((prev-msg (msg3 network-s))

           (Xr (Xr-msg prev-msg))
           (Nr (Nr-msg prev-msg))
           (Xi (Xi-msg prev-msg))
           (Ni (Ni-msg prev-msg))
           (Tr-msg (Tr-msg prev-msg))
           (Ei (Ei-msg prev-msg))
           (Hi-msg (Hi-msg prev-msg))
           (Src-ip (src-ip-msg prev-msg))

           (dh-exponent (dh-exponent my-constants))
           (b (b my-constants))
           (g (g my-constants))

           (dh-key (CRYPTO::compute-dh-key Xi dh-exponent b))
           (session-key (compute-session-key Ni Nr dh-key))

           (hi-calc (compute-hi Ei Session-key))
           (private-key (private-key my-constants))
           (tr-calc (compute-tr Ni Nr Xr src-ip private-key)) ; should check compute-tr

           (ei-decrypted (CRYPTO::decrypt-symmetric-list ei session-key))
           (id-i (nth 0 ei-decrypted)) ; consider changing from nth to an abstraction
           (sa-i (nth 1 ei-decrypted))
           (sig-ki-msg (nth 2 ei-decrypted))

           (public-key-i (public-key-i public-constants))
           (SigKi-calc (verify-sig-Ki Ni Nr Xi Xr G B public-key-i))

           (sa-r (sa my-constants))
           (id-r (id my-constants))

           (sig-kr (compute-sig-kr Xi Xr Ni Nr private-key))
           (er (compute-er ID-r sa-r sig-kr session-key))
           (hr (compute-hr Er session-key))

           (success (and (equal sig-ki-msg SigKi-calc)
                         (equal tr-msg tr-calc)
                         (equal hi-msg hi-calc)))
           (done t)

           (my-update (list (cons 'ID-i Id-i)
                            (cons 'session-key session-key)
                            (cons 'success success)
                            (cons 'done done)))

           (network-update (list (cons 'er er)
                                 (cons 'hr hr))))
      (declare (ignore sa-i))

      (mv
       (acons 4 network-update network-s)
       (append my-update my-s))))

; everything suffixed with a -msg means it was pulled from a message
; everything suffixed with a -c means it was pulled from a constant list
; everything suffixed with a -s means it was pulled from a state list (may be
;   unused)

(defun responder-step2-prev-msg-ok (prev-msg my-constants public-constants)

  (and
   (well-formed-msg3p prev-msg)

   (let* ((Xr-msg (Xr-msg prev-msg))
          (Nr-msg (Nr-msg prev-msg))
          (Xi-msg (Xi-msg prev-msg))
          (Ni-msg (Ni-msg prev-msg))
          (Tr-msg (Tr-msg prev-msg))
          (Ei-msg (Ei-msg prev-msg)) ;;; dsafdsfaasdfasdfdsf
          (Hi-msg (Hi-msg prev-msg))
         (Src-ip-msg (src-ip-msg prev-msg))

         (Nr-c (nonce my-constants))

         (dh-exponent (dh-exponent my-constants))
         (B-c (b my-constants))
         (G-c (g my-constants))

         (Xr-c (CRYPTO::compute-public-dh-value G-c
                                                (dh-exponent my-constants)
                                                B-c))
         (dh-key-calc (CRYPTO::compute-dh-key Xi-msg dh-exponent B-c))
         (session-key-calc (compute-session-key Ni-msg Nr-c dh-key-calc))

         (hi-calc (compute-hi Ei-msg session-key-calc))
         (private-key (private-key my-constants))
         (tr-calc (compute-tr Ni-msg Nr-c Xr-c src-ip-msg private-key))

         (Ei-decrypted (CRYPTO::decrypt-symmetric-list Ei-msg session-key-calc))
         (id-i (nth 0 Ei-decrypted))
         (sa-i (nth 1 Ei-decrypted))
         (sig-ki-msg (nth 2 Ei-decrypted))

         (public-key-i (public-key-i public-constants))
         (SigKi-calc (verify-sig-ki Ni-msg Nr-msg Xi-msg Xr-msg G-c B-c
                                    public-key-i))

         (sa-r (sa my-constants))
         (id-r (id my-constants))

         (sig-kr (compute-sig-kr Ni-msg Nr-c Xi-msg Xr-c private-key))
         (er (compute-er ID-r sa-r sig-kr session-key-calc))
         (hr (compute-hr Er session-key-calc)))
     (declare (ignore id-i sa-i hr))
     (and (equal Nr-msg Nr-c)
          (equal Xr-msg Xr-c)

          (equal tr-msg tr-calc)

          (equal hi-msg hi-calc) ; swapped order
          (equal sig-ki-msg SigKi-calc)))))


; Note that we intentionally use the initiator's private key.  We will later
; use analysis to make the conclusion that it won't verify with the public key
; unless the private key is equal to the actual private key

(defun badly-forged-msg3p-old
  (msg responder-constants initiator-private-key)

  (let* ((dh-key (CRYPTO::compute-dh-key (xi-msg msg)
                                         (dh-exponent responder-constants)
                                         (b responder-constants)))

         (session-key (compute-session-key (Ni-msg msg)
                                           (Nr-msg msg)
                                           dh-key))

         (SigKi (compute-sig-Ki (Ni-msg msg)
                                (Nr-msg msg)
                                (Xi-msg msg)
                                (Xr-msg msg)
                                (g responder-constants)
                                (b responder-constants)
                                initiator-private-key))

         (Ei-decrypted (CRYPTO::decrypt-symmetric-list (Ei-msg msg) session-key)))

     (not (equal (nth 2 Ei-decrypted)
                 SigKi))))


(defun badly-forged-msg3p (msg responder-constants initiator-public-key)

  (let* ((dh-key (CRYPTO::compute-dh-key (xi-msg msg)
                                         (dh-exponent responder-constants)
                                         (b responder-constants)))

         (session-key (compute-session-key (Ni-msg msg)
                                           (Nr-msg msg)
                                           dh-key))

         (SigKi (verify-sig-Ki (Ni-msg msg)
                               (Nr-msg msg)
                               (Xi-msg msg)
                               (Xr-msg msg)
                               (g responder-constants)
                               (b responder-constants)
                               initiator-public-key))

         (Ei-decrypted (CRYPTO::decrypt-symmetric-list (Ei-msg msg) session-key)))

    (not (equal (nth 2 Ei-decrypted)
                SigKi))))


(defthm badly-forged-msg3p-implies-responder-step2-prev-msg-not-ok
  (implies (and (constantsp constants)
                (badly-forged-msg3p msg
                                    (responder-constants constants)
                                    (public-key-I (public-constants constants))))
           (not (responder-step2-prev-msg-ok msg

                                             (responder-constants constants)
                                             (public-constants constants))))
  :hints (("Goal" :in-theory (e/d (responder-step2-prev-msg-ok
                                   compute-sig-ki verify-sig-ki)
                                  (Ni-msg Nr-msg Xi-msg Src-ip-msg nonce ei-msg
                                          b g
                                          well-formed-msg3p xr-msg)))))


(defun responder-step2 (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (responder-constantsp my-constants)
                              (public-constantsp public-constants))))

  (if (responder-step2-prev-msg-ok (msg3 network-s) my-constants public-constants)
      (responder-step2-aux network-s my-s my-constants public-constants)
    (get-mv-protocol-failure)))


(defthm poorly-formed-network-msg3-yields-failure-for-responder
  (implies (not (well-formed-msg3p (msg3 network-s-after-3)))
           (mv-let
            (network-s-after-4 responder-s-after-4)
            (responder-step2 network-s-after-3 responder-s-after-2
                             responder-constants public-constants)
            (declare (ignore network-s-after-4))
            (protocol-failure responder-s-after-4)))
  :hints (("Goal" :in-theory (disable well-formed-network-state-after-step3p))))


(defthm badly-forged-network-msg3-yields-failure-for-responder
  (implies (and (constantsp constants)
                (badly-forged-msg3p (msg3 network-s-after-3)
                                    (responder-constants constants)
                                    (public-key-i (public-constants constants))))
           (mv-let
            (network-s-after-4 responder-s-after-4)
            (responder-step2 network-s-after-3 responder-s-after-2
                             (responder-constants constants)
                             (public-constants constants))
            (declare (ignore network-s-after-4))
            (protocol-failure responder-s-after-4)))
  :hints (("Goal" :in-theory (e/d (responder-step2)
                                  (responder-step2-aux constantsp)))))



(defun run-4-steps-honest (network-s initiator-constants responder-constants
                                    public-constants initiator-s responder-s)

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)

   (mv-let
    (network-s-after-2 responder-s-after-2)
    (responder-step1 network-s-after-1 responder-s responder-constants public-constants)


  (mv-let
   (network-s-after-3 initiator-s-after-3)
   (initiator-step2 network-s-after-2 initiator-s-after-1 initiator-constants public-constants)

   (mv-let
    (network-s-after-4 responder-s-after-4)
    (responder-step2 network-s-after-3 responder-s-after-2 responder-constants public-constants)


    (mv network-s-after-4
        initiator-s-after-3
        responder-s-after-4))))))

#|
(run-4-steps-honest nil
                   *initiator-constants*
                   *responder-constants*
                   *public-constants*
                   nil
                   nil)
|#



(defun initiator-step3-aux (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (initiator-constantsp my-constants)
                              (public-constantsp public-constants))))

  (let* ((prev-msg (msg4 network-s))

         (er (er-msg prev-msg))
         (Hr-msg (Hr-msg prev-msg))
         (session-key (session-key my-s))

         (er-decrypted (CRYPTO::decrypt-symmetric-list er session-key))
         (id-r (nth 0 er-decrypted))
         (sa-r (nth 1 er-decrypted))
         (sig-kr-msg (nth 2 er-decrypted))

         (Xr (Xr my-s))
         (Nr (Nr my-s))
         (Xi (Xi my-s))
         (Ni (nonce my-constants))

         (public-key-r (public-key-r public-constants))

         (SigKr-calc (verify-sig-kr Ni Nr Xi Xr public-key-r))
         (hr-calc (compute-hr Er session-key))

         (success (and (equal sig-kr-msg SigKr-calc)
                       (equal hr-msg hr-calc)))
         (done t)

         (my-update (list (cons 'ID-r Id-r)
                          (cons 'success success)
                          (cons 'done done)))

         (network-update nil))

    (declare (ignore sa-r))

    (mv (acons 5 network-update network-s)
        (append my-update my-s))))


(defun initiator-step3-prev-msg-ok (prev-msg my-s my-constants public-constants)
  (and
   (well-formed-msg4p prev-msg)
   (let* ((Er-msg (Er-msg prev-msg))
          (Hr-msg (Hr-msg prev-msg))
          (Session-key (session-key my-s))

          (Er-decrypted (CRYPTO::decrypt-symmetric-list Er-msg session-key))
          (id-r (nth 0 er-decrypted))
          (sa-r (nth 1 er-decrypted))
          (sig-kr-msg (nth 2 er-decrypted))

          (Xr-s (Xr my-s))
          (Nr-s (Nr my-s))
          (Xi-s (Xi my-s))
          (Ni-c (nonce my-constants))

          (public-key-r (public-key-r public-constants))

          (SigKr-calc (verify-sig-kr Ni-c Nr-s Xi-s Xr-s public-key-r))
          (hr-calc (compute-hr Er-msg session-key)))
     (declare (ignore id-r sa-r))

     (and (equal sig-kr-msg SigKr-calc)
          (equal hr-msg hr-calc)))))


(defun initiator-step3 (network-s my-s my-constants public-constants)
  (declare (xargs :guard (and (initiator-constantsp my-constants)
                              (public-constantsp public-constants))))

  (if (initiator-step3-prev-msg-ok (msg4 network-s) my-s my-constants public-constants)
      (initiator-step3-aux network-s my-s my-constants public-constants)
    (get-mv-protocol-failure)))


(defun badly-forged-msg4p
  (msg initiator-s initiator-constants responder-public-key) ; init-s for Xr

  (let* ((dh-key (CRYPTO::compute-dh-key (Xr initiator-s)
                                         (dh-exponent initiator-constants)
                                         (b initiator-s)))

         (SigKr (verify-sig-Kr (Nonce initiator-constants)
                               (Nr initiator-s)
                               (Xi initiator-s)
                               (Xr initiator-s)
                               responder-public-key))

         (Er-decrypted (CRYPTO::decrypt-symmetric-list (Er-msg msg)
                                                       (session-key initiator-s))))
    (declare (ignore dh-key))

    (not (equal (nth 2 Er-decrypted)
                SigKr))))


(defthm badly-forged-msg4p-implies-initiator-step3-prev-msg-not-ok
  (implies (and (constantsp constants)
                (badly-forged-msg4p msg
                                    initiator-s ; will probably need to qualify
                                    (initiator-constants constants)
                                    (public-key-R (public-constants constants))))
           (not (initiator-step3-prev-msg-ok msg
                                             initiator-s
                                             (initiator-constants constants)
                                             (public-constants constants))))
  :hints (("Goal" :in-theory (e/d (initiator-step3-prev-msg-ok
                                   compute-sig-ki verify-sig-ki)
                                  (nonce er-msg
                                         Ni Ni-msg Nr-msg Nr Xi Xr session-key
                                         well-formed-msg4p hr-msg)))))


(defthm poorly-formed-network-msg4-yields-failure-for-initiator
  (implies (not (well-formed-msg4p (msg4 network-s-after-4)))
           (mv-let
            (network-s-after-5 initiator-s-after-5)
            (initiator-step3 network-s-after-4 initiator-s-after-3
                             initiator-constants public-constants)
            (declare (ignore network-s-after-5))

            (protocol-failure initiator-s-after-5)))
  :hints (("Goal" :in-theory (disable well-formed-network-state-after-step4p))))


(defthm badly-forged-network-msg4-yields-failure-for-initiator
  (implies (and (constantsp constants)
                (badly-forged-msg4p (msg4 network-s-after-4)
                                    initiator-s-after-2
                                    (initiator-constants constants)
                                    (public-key-r (public-constants constants))))
           (mv-let
            (network-s-after-5 initiator-s-after-5)
            (initiator-step3 network-s-after-4 initiator-s-after-2
                             (initiator-constants constants)
                             (public-constants constants))
            (declare (ignore network-s-after-5))

            (protocol-failure initiator-s-after-5)))
  :hints (("Goal" :in-theory (e/d (initiator-step3)
                                  (initiator-step3-aux msg4 constantsp)))))


(defun run-5-steps-honest (network-s initiator-constants responder-constants
                                   public-constants initiator-s responder-s)

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)

   (mv-let
    (network-s-after-2 responder-s-after-2)
    (responder-step1 network-s-after-1 responder-s responder-constants public-constants)


  (mv-let
   (network-s-after-3 initiator-s-after-3)
   (initiator-step2 network-s-after-2 initiator-s-after-1 initiator-constants public-constants)

   (mv-let
    (network-s-after-4 responder-s-after-4)
    (responder-step2 network-s-after-3 responder-s-after-2 responder-constants public-constants)

  (mv-let
   (network-s-after-5 initiator-s-after-5)
   (initiator-step3 network-s-after-4 initiator-s-after-3 initiator-constants public-constants)

    (mv network-s-after-5
        initiator-s-after-5
        responder-s-after-4)))))))



#|
(run-5-steps-honest nil
                   *initiator-constants*
                   *responder-constants*
                   *public-constants*
                   nil
                   nil)
|#

#|
; The below assertion illustrates an example of what a successful trace of the
; JFKr protocol looks like.
(ACL2::assert!
 (mv-let (network-s initiator-s responder-s)
         (run-5-steps-honest nil *initiator-constants* *responder-constants*
                             *public-constants* nil nil)
         (declare (ignore network-s))
         (and
          ;; responder stores the correct partner
          (equal (id *initiator-constants*)
                 (id-i responder-s))
          ;; initiator stores the correct partner
          (equal (id *responder-constants*)
                 (id-r initiator-s))
          ;; responder and initiator have the same session key
          (equal (session-key initiator-s)
                 (session-key responder-s)))))
|#

; example-correct-message# act as oracles - we probably will never use these
; (and they could be deleted, but they are preserved for now), but they serve
; as a reference point for what extreme correctness is.  We should be able to
; prove that an exactly correct trace of messages produces success.

(set-verify-guards-eagerness 0)
(defun example-correct-message1 (network constants)
  (declare (xargs :guard (and (well-formed-network-statep network)
                              (constantsp constants))))
  (let-with-bindings-from-all-constants
   (declare (ignore ipr-c public-key-i-c public-key-r-c tr-c hi-c hr-c))
   (let ((prev-msg (msg1 network)))
     (and (equal Ni-c (Ni-msg prev-msg))
          (equal SrcIP-c (Src-ip-msg prev-msg))))))

#|
(ACL2::assert! (example-correct-message1 (quote ((1 (NI . 52425) (SRC-IP . 13441))))
                                   *constants*))
|#

(defun example-correct-message2 (network constants)
  (declare (xargs :guard (and (well-formed-network-statep network)
                              (constantsp constants))))
  (let-with-bindings-from-all-constants
   (declare (ignore ipr-c public-key-r-c public-key-i-c hr-c hi-c))
   (let ((prev-msg (msg2 network)))
     (and (equal Ni-c (Ni-msg prev-msg))
          (equal Nr-c (Nr-msg prev-msg))
          (equal Xr-c (Xr-msg prev-msg))
          (equal G-c (g-msg prev-msg))
          (equal Tr-c (tr-msg prev-msg))))))
#|
(assert$ (example-correct-message2 (quote ((2 (NI . 52425)
                                              (NR . 287024)
                                              (XR . 526534)
                                              (G . 1996645)
                                              (B . 656437)
                                              (TR . 1149228))
                                           (1 (NI . 52425) (SRC-IP . 13441))))
                                   *constants*)
         "Message2 test is exactly correct!")
|#

; We'll need to enable these for attacker proofs later

(defun example-correct-message3 (network constants)
  (declare (xargs :guard (and (well-formed-network-statep network)
                              (constantsp constants))))
  (let-with-bindings-from-all-constants
   (declare (ignore ipr-c public-key-i-c public-key-r-c hr-c))
   (let ((prev-msg (msg3 network)))
     (and (equal Ni-c (Ni-msg prev-msg))
          (equal Nr-c (Nr-msg prev-msg))
          (equal Xi-c (Xi-msg prev-msg))
          (equal Xr-c (Xr-msg prev-msg))
          (equal Tr-c (tr-msg prev-msg))
          (equal Ei-c (Ei-msg prev-msg))
          (equal Hi-c (Hi-msg prev-msg))))))

#|
(ACL2::assert! (example-correct-message3 (quote ((3 (NI . 52425)
                                              (NR . 287024)
                                              (XI . 612850)
                                              (XR . 526534)
                                              (TR . 1149228)
                                              (EI 919164 1697752 4094474)
                                              (HI . 7628163)
                                              (SRC-IP . 13441))
                                           (2 (NI . 52425)
                                              (NR . 287024)
                                              (XR . 526534)
                                              (G . 1996645)
                                              (B . 656437)
                                              (TR . 1149228))
                                           (1 (NI . 52425) (SRC-IP . 13441))) )
                                   *constants*))
|#

(defun example-correct-message4 (network constants)
  (declare (xargs :guard (and (well-formed-network-statep network)
                              (constantsp constants))))
  (let-with-bindings-from-all-constants
   (declare (ignore ipr-c public-key-i-c public-key-r-c tr-c hi-c))
   (let ((prev-msg (msg4 network)))
     (and (equal Er-c (Er-msg prev-msg))
          (equal Hr-c (Hr-msg prev-msg))))))


#|
(ACL2::assert! (example-correct-message4 (quote ((4 (ER 1149802 2458657 2125798)
                                              (HR . 6651031))
                                           (3 (NI . 52425)
                                              (NR . 287024)
                                              (XI . 612850)
                                              (XR . 526534)
                                              (TR . 1149228)
                                              (EI 919164 1697752 4094474)
                                              (HI . 7628163)
                                              (SRC-IP . 13441))
                                           (2 (NI . 52425)
                                              (NR . 287024)
                                              (XR . 526534)
                                              (G . 1996645)
                                              (B . 656437)
                                              (TR . 1149228))
                                           (1 (NI . 52425) (SRC-IP . 13441))) )
                                   *constants*))
|#

; Here we define some functions that we know nothing about to assist the
; attacker in modifying the network messages

(defstub function-we-know-nothing-about1 (*) => *)
(defstub function-we-know-nothing-about2 (*) => *)
(defstub function-we-know-nothing-about3 (*) => *)
(defstub function-we-know-nothing-about4 (*) => *)
(defstub function-we-know-nothing-about5 (*) => *)

#|
; The following forms make debugging of the proofs easier, but since
; add-untranslate-pattern isn't embeddable, they are commented.
(include-book ;; fool dependency scanner
 "misc/untranslate-patterns" :dir :system)
(add-untranslate-pattern (function-we-know-nothing-about1 ?x) (attacker |...|))
(add-untranslate-pattern (function-we-know-nothing-about2 ?x) (attacker |...|))
(add-untranslate-pattern (function-we-know-nothing-about3 ?x) (attacker |...|))
(add-untranslate-pattern (function-we-know-nothing-about4 ?x) (attacker |...|))
(add-untranslate-pattern (function-we-know-nothing-about5 ?x) (attacker |...|))
|#


(defthm run-2-steps-with-poorly-formed-attacker-yields-responder-failure

     (mv-let
      (network-s-after-1 initiator-s-after-1)
      (initiator-step1 network-s initiator-s initiator-constants public-constants)
      (declare (ignore initiator-s-after-1))

      (let ((network-s-after-1-munged (function-we-know-nothing-about1 network-s-after-1)))
        (mv-let
         (network-s-after-2 responder-s-after-2)
         (responder-step1 network-s-after-1-munged responder-s
                          responder-constants public-constants)
         (declare (ignore network-s-after-2))

         (implies (not (well-formed-msg1p (msg1 network-s-after-1-munged)))
                  (protocol-failure responder-s-after-2))))))


(defthm run-3-steps-with-poorly-formed-attacker-yields-initiator-failure

     (mv-let
      (network-s-after-1 initiator-s-after-1)
      (initiator-step1 network-s initiator-s initiator-constants public-constants)


      (let ((network-s-after-1-munged (function-we-know-nothing-about1 network-s-after-1)))
        (mv-let
         (network-s-after-2 responder-s-after-2)
         (responder-step1 network-s-after-1-munged responder-s
                          responder-constants public-constants)
         (declare (ignore responder-s-after-2))
         (let ((network-s-after-2-munged (function-we-know-nothing-about2 network-s-after-2)))
           (mv-let
            (network-s-after-3 initiator-s-after-3)
            (initiator-step2 network-s-after-2-munged initiator-s-after-1
                             initiator-constants public-constants)
            (declare (ignore network-s-after-3))
            (implies (not (well-formed-msg2p (msg2 network-s-after-2-munged)))
                     (protocol-failure initiator-s-after-3)))))))

  :hints (("Goal" :in-theory (disable well-formed-msg1p  well-formed-msg2p))))


(defthm run-4-steps-with-poorly-formed-attacker-yields-responder-failure

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)


   (let ((network-s-after-1-munged (function-we-know-nothing-about1 network-s-after-1)))
     (mv-let
      (network-s-after-2 responder-s-after-2)
      (responder-step1 network-s-after-1-munged responder-s
                       responder-constants public-constants)

      (let ((network-s-after-2-munged (function-we-know-nothing-about2 network-s-after-2)))
        (mv-let
         (network-s-after-3 initiator-s-after-3)
         (initiator-step2 network-s-after-2-munged initiator-s-after-1
                          initiator-constants public-constants)
         (declare (ignore initiator-s-after-3))

         (let ((network-s-after-3-munged (function-we-know-nothing-about3 network-s-after-3)))

           (mv-let
            (network-s-after-4 responder-s-after-4)
            (responder-step2 network-s-after-3-munged responder-s-after-2
                             responder-constants public-constants)
            (declare (ignore network-s-after-4))

            (implies (not (well-formed-msg3p (msg3 network-s-after-3-munged)))
                     (protocol-failure responder-s-after-4)))))))))

  :hints (("Goal" :in-theory (e/d (responder-step2 initiator-step2)
                                  (well-formed-msg1p
                                   well-formed-msg2p well-formed-msg3p

                                   responder-step2-aux
                                   initiator-step2-aux responder-step1
                                   initiator-step1 ei-msg hi-msg ni-msg
                                   nr-msg src-ip-msg tr-msg xi-msg xr-msg
                                   msg2 msg3)))))


(defthm run-4-steps-with-badly-forged-attacker-yields-responder-failure
  (let ((initiator-constants (initiator-constants constants))
        (responder-constants (responder-constants constants))
        (public-constants (public-constants constants)))

    (mv-let
     (network-s-after-1 initiator-s-after-1)
     (initiator-step1 network-s initiator-s initiator-constants
                      public-constants)


     (let ((network-s-after-1-munged (function-we-know-nothing-about1 network-s-after-1)))
       (mv-let
        (network-s-after-2 responder-s-after-2)
        (responder-step1 network-s-after-1-munged responder-s
                         responder-constants public-constants)

        (let ((network-s-after-2-munged (function-we-know-nothing-about2 network-s-after-2)))
          (mv-let
           (network-s-after-3 initiator-s-after-3)
           (initiator-step2 network-s-after-2-munged initiator-s-after-1
                            initiator-constants public-constants)
           (declare (ignore initiator-s-after-3))

           (let ((network-s-after-3-munged (function-we-know-nothing-about3 network-s-after-3)))

             (mv-let
              (network-s-after-4 responder-s-after-4)
              (responder-step2 network-s-after-3-munged responder-s-after-2
                               responder-constants public-constants)
              (declare (ignore network-s-after-4))

              (implies
               (and (constantsp constants)
                    (badly-forged-msg3p (msg3 network-s-after-3-munged)
                                        (responder-constants constants)
                                        (public-key-i (public-constants constants))))

               (protocol-failure responder-s-after-4))))))))))

  :hints (("Goal" :in-theory (e/d (responder-step2)
                                  (constantsp
                                   well-formed-msg3p
                                   badly-forged-msg3p
                                   responder-step2-prev-msg-ok
                                   responder-step2-aux
                                   initiator-step2
                                   responder-step1
                                   initiator-step1
                                   ei-msg hi-msg ni-msg
                                   nr-msg src-ip-msg tr-msg xi-msg xr-msg
                                   msg2 msg3
                                   protocol-failure protocol-success)))))


(defthm run-5-steps-with-poorly-formed-attacker-yields-initiator-failure

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)

   (let ((network-s-after-1-munged (function-we-know-nothing-about1
                                    network-s-after-1)))
     (mv-let
      (network-s-after-2 responder-s-after-2)
      (responder-step1 network-s-after-1-munged responder-s
                       responder-constants public-constants)

      (let ((network-s-after-2-munged (function-we-know-nothing-about2
                                       network-s-after-2)))
        (mv-let
         (network-s-after-3 initiator-s-after-3)
         (initiator-step2 network-s-after-2-munged initiator-s-after-1
                          initiator-constants public-constants)

         (let ((network-s-after-3-munged (function-we-know-nothing-about3
                                          network-s-after-3)))

           (mv-let
            (network-s-after-4 responder-s-after-4)
            (responder-step2 network-s-after-3-munged responder-s-after-2
                             responder-constants public-constants)
            (declare (ignore responder-s-after-4))

            (let ((network-s-after-4-munged (function-we-know-nothing-about4
                                             network-s-after-4)))

              (mv-let
               (network-s-after-5 initiator-s-after-5)
               (initiator-step3 network-s-after-4-munged initiator-s-after-3
                                initiator-constants public-constants)
               (declare (ignore network-s-after-5))

               (implies (not (well-formed-msg4p
                              (msg4 network-s-after-4-munged)))
                        (protocol-failure initiator-s-after-5)))))))))))

  :hints (("Goal" :in-theory (e/d (responder-step2 initiator-step2)
                                  (well-formed-msg1p
                                   well-formed-msg2p well-formed-msg3p
                                   responder-step2-aux
                                   initiator-step2-aux responder-step1
                                   initiator-step1 ei-msg hi-msg ni-msg
                                   nr-msg src-ip-msg tr-msg xi-msg xr-msg
                                   msg2 msg3 protocol-failure)))))


(defthm run-5-steps-with-badly-forged-attacker-yields-initiator-failure

  (let ((initiator-constants (initiator-constants constants))
        (responder-constants (responder-constants constants))
        (public-constants (public-constants constants)))

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)


   (let ((network-s-after-1-munged (function-we-know-nothing-about1
                                    network-s-after-1)))
     (mv-let
      (network-s-after-2 responder-s-after-2)
      (responder-step1 network-s-after-1-munged responder-s
                       responder-constants public-constants)

      (let ((network-s-after-2-munged (function-we-know-nothing-about2
                                       network-s-after-2)))
        (mv-let
         (network-s-after-3 initiator-s-after-3)
         (initiator-step2 network-s-after-2-munged initiator-s-after-1
                          initiator-constants public-constants)

         (let ((network-s-after-3-munged (function-we-know-nothing-about3
                                          network-s-after-3)))

           (mv-let
            (network-s-after-4 responder-s-after-4)
            (responder-step2 network-s-after-3-munged responder-s-after-2
                             responder-constants public-constants)
            (declare (ignore responder-s-after-4))
            (let ((network-s-after-4-munged (function-we-know-nothing-about4
                                             network-s-after-4)))

              (mv-let
               (network-s-after-5 initiator-s-after-5)
               (initiator-step3 network-s-after-4-munged initiator-s-after-3
                                initiator-constants public-constants)
               (declare (ignore network-s-after-5))

               (implies
                (and (constantsp constants)
                     (badly-forged-msg4p (msg4 network-s-after-4-munged)
                                         initiator-s-after-3
                                         initiator-constants
                                         (public-key-R public-constants)))

                (protocol-failure initiator-s-after-5))))))))))))

  :hints (("Goal" :in-theory (e/d (responder-step2 initiator-step2)
                                  (well-formed-msg1p
                                   well-formed-msg2p well-formed-msg3p
                                   responder-step2-aux
                                   initiator-step2-aux responder-step1
                                   initiator-step1 ei-msg hi-msg ni-msg
                                   nr-msg src-ip-msg tr-msg xi-msg xr-msg
                                   msg2 msg3 protocol-failure)))))



(defthm run-5-steps-with-badly-forged-attacker-yields-both-failure

  (let ((initiator-constants (initiator-constants constants))
        (responder-constants (responder-constants constants))
        (public-constants (public-constants constants)))

  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s initiator-constants public-constants)


   (let ((network-s-after-1-munged (function-we-know-nothing-about1
                                    network-s-after-1)))
     (mv-let
      (network-s-after-2 responder-s-after-2)
      (responder-step1 network-s-after-1-munged responder-s
                       responder-constants public-constants)

      (let ((network-s-after-2-munged (function-we-know-nothing-about2
                                       network-s-after-2)))
        (mv-let
         (network-s-after-3 initiator-s-after-3)
         (initiator-step2 network-s-after-2-munged initiator-s-after-1
                          initiator-constants public-constants)

         (let ((network-s-after-3-munged (function-we-know-nothing-about3
                                          network-s-after-3)))

           (mv-let
            (network-s-after-4 responder-s-after-4)
            (responder-step2 network-s-after-3-munged responder-s-after-2
                             responder-constants public-constants)


            (let ((network-s-after-4-munged (function-we-know-nothing-about4
                                             network-s-after-4)))

              (mv-let
               (network-s-after-5 initiator-s-after-5)
               (initiator-step3 network-s-after-4-munged initiator-s-after-3
                                initiator-constants public-constants)
               (declare (ignore network-s-after-5))
               (implies
                (and (constantsp constants)
                     (badly-forged-msg3p (msg3 network-s-after-3-munged)
                                         (responder-constants constants)
                                         (public-key-i (public-constants constants)))
                     (badly-forged-msg4p (msg4 network-s-after-4-munged)
                                         initiator-s-after-3
                                         initiator-constants
                                         (public-key-R public-constants)))
                (and (protocol-failure responder-s-after-4)
                     (protocol-failure initiator-s-after-5)))))))))))))

  :hints (("Goal" :do-not  '(eliminate-destructors generalize)
           :do-not-induct t

           :in-theory (e/d ()
                           (responder-step2
                            badly-forged-network-msg4-yields-failure-for-initiator
                            initiator-step2
                            well-formed-msg1p
                            badly-forged-msg3p badly-forged-msg4p
                            well-formed-msg2p well-formed-msg3p
                            responder-step2-aux
                            initiator-step2-aux responder-step1
                            initiator-step1 ei-msg hi-msg ni-msg
                            nr-msg src-ip-msg tr-msg xi-msg xr-msg
                            msg2 msg3 msg4 protocol-failure xi xr
                            well-formed-msg4p session-key constantsp
                            er-msg hr-msg initiator-step3
                            initiator-step3-prev-msg-ok nr mv-nth)))))


#|
; Theorem to prove in the future to show that if both the initiator and
; responder successfully complete the protocol, they have the same view of the
; session keys.

(defthm success-of-both-implies-equal-session-keys
  (mv-let
   (network-s-after-1 initiator-s-after-1)
   (initiator-step1 network-s initiator-s
                    initiator-constants public-constants)
   (mv-let
    (network-s-after-2 responder-s-after-2)
    (responder-step1
     (function-we-know-nothing-about1 network-s-after-1)
     responder-s responder-constant public-constants)

    (mv-let
     (network-s-after-3 initiator-s-after-3)
     (initiator-step2
      (function-we-know-nothing-about2 network-s-after-2)
      initiator-s-after-1 initiator-constants
      public-constants)

     (mv-let
      (network-s-after-4 responder-s-after-4)
      (responder-step2
       (function-we-know-nothing-about3 network-s-after-3)
       responder-s-after-2 responder-constants
       public-constants)

      (mv-let
       (network-s-after-5 initiator-s-after-5)
       (initiator-step3
        (function-we-know-nothing-about4 network-s-after-4)
        initiator-s-after-3 initiator-constants
        public-constants)
       (declare (ignore network-s-after-5))

       (implies
        (and (done initiator-s-after-5)
             (success initiator-s-after-5)
             (done responder-s-after-4)
             (success responder-s-after-4))
        (equal (session-key initiator-s-after-5)
               (session-key responder-s-after-5)))))))))
|#
