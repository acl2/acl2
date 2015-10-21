; VI Cache Coherency Protocol
; Copyright (C) 2015, Oracle and/or its affiliates. All rights reserved.
;
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
;
; Original authors: Ben Selfridge <ben.selfridge@oracle.com>
;                   David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

(set-ignore-ok t)

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;
;; TABLES ;;
;;;;;;;;;;;;

; For fun, we create constants to represent the tables of this protocol. We
; don't use it for any purpose here other than to show the reader what the
; protocol is, and indicate how we might actually use these tables to implement
; the step function.

; Every transition for the cache protocol is a list where the first is the
; message to be sent (along with its destination) and the second is the next
; state the cache should transition to. We interpret nil to indicate an invalid
; state/message combination.
(defconst *cache-protocol*
  ; state  L/S                 evict               data       fwd-get              put-ack
  '((:i    ((:get :dir) :iv-d) (nil nil)           nil        nil                  nil)
    (:iv-d (nil nil)           (nil nil)           (nil :v)   (nil nil)            nil)
    (:v    (nil nil)           ((:put :dir) :vi-a) nil        ((:data :req) :i)    nil)
    (:vi-a (nil nil)           (nil nil)           nil        ((:data :req) :ii-a) (nil :i))
    (:ii-a (nil nil)           (nil nil)           nil        nil                  (nil :i))))

; Every transition for the directory protocol is a list where the first is the
; message to be set (along with its destination), the second is the new owner
; (nil indicates to keep the owner the same), and the third is the state to
; transition to.
(defconst *dir-protocol*
  ;  state   get                         put (owner)              put (non-owner)
  '((:i      ((:data :req) :req :v)      nil                      ((:put-ack :req) nil :i))
    (:v      ((:fwd-get :owner) :req :v) ((:put-ack :req) nil :i) ((:put-ack :req) nil :v))))

;;;;;;;;;;
;; MISC ;;
;;;;;;;;;;

; We use remove-nth to remove an incoming request or response from our list. We use remove-last to remove the
; last forward from our list of forwards.
(define remove-nth
  ((i natp)
   (l (and (true-listp l)
           (< i (len l)))))
  :returns (new-l true-listp :hyp :fguard)
  (if (zp i)
      (cdr l)
    (cons (car l) (remove-nth (1- i) (cdr l)))))

(define remove-last
  ((l (and (true-listp l)
           (consp l))))
  :returns (new-l true-listp :hyp :fguard)
  (cond ((endp l) nil)
        ((endp (cdr l)) nil)
        (t (cons (car l) (remove-last (cdr l))))))

(defrule len-remove-nth
  (implies (and (< 0 (len x))
                (natp i)
                (< i (len x)))
           (= (len (remove-nth i x))
              (1- (len x))))
  :enable remove-nth)

(defrule consp-remove-nth
  (implies (and (< 0 (len x))
                (natp i)
                (< i (len x)))
           (equal (consp (remove-nth i x))
                  (not (= (len x) 1))))
  :enable remove-nth)

(defruled nth-remove-nth
  (implies (and (natp i)
                (natp j)
                (< i (len x))
                (< j (len x)))
           (equal (nth j (remove-nth i x))
                  (if (nth j (remove-nth i x))
                      (if (< j i)
                          (nth j x)
                        (nth (1+ j) x))
                    nil)))
  :enable remove-nth)

;;;;;;;;;;;;;;;;;;
;; SYSTEM STATE ;;
;;;;;;;;;;;;;;;;;;

(fty::deftagsum cache-state

 ; i - this cache does not have a copy of the data.
 (:i    ()                :base-name i-state)

 ; V - this cache has a valid copy of the data. He can read or write.
 (:v    ((data integerp)) :base-name v-state)

 ; IV^D - this cache has sent a Get request to the directory, and is waiting on
 ; a data response either from the directory or from the previously owning
 ; cache.
 (:iv-d ()                :base-name iv-d-state)

 ; VI^A - this cache has sent a Put request to the directory, and is waiting on
 ; a Put-Ack from the directory. In the meantime, the cache still has to be
 ; ready to respond to any coherence requests that the directory might forward
 ; its way before receiving the Put request from this cache.
 (:vi-a ((data integerp)) :base-name vi-a-state)

 ; II^A - this cache has sent a Put request from the directory, then
 ; subsequently received and processed a Fwd-Get. It is still waiting on a
 ; Put-Ack from the directory, though.
 (:ii-a ()                :base-name ii-a-state))

(fty::deftagsum dir-state

 ; I - none of the caches have a valid copy of the data, so the directory has
 ; the data (that's why this constructor has a data field).
 (:i ((data integerp)) :base-name i-dir-state)

 ; V - exactly one cache has a valid copy of the data (the one referenced by
 ; owner-id). Any coherence requests sent to the directory will be forwarded to
 ; the owner.
 (:v ((owner-id natp)) :base-name v-dir-state))

(fty::deftagsum core-event
  (:cload ((cache-id natp))  :base-name cload)
  (:cstore ((cache-id natp) (data integerp)) :base-name cstore)
  (:cevict ((cache-id natp)) :base-name cevict))

(fty::deftagsum request
  (:get ((cache-id natp)) :base-name req-get)
  (:put ((cache-id natp) (data integerp)) :base-name req-put))

(fty::deftagsum forward
  (:get     ((cache-id natp)) :base-name fwd-get)
  (:put-ack ()                :base-name fwd-put-ack))

; even though there is only one case, we make this a deftagsum as opposed to a defprod just for simplicity.
(fty::deftagsum response
  (:data      ((data integerp)) :base-name resp-data))

(fty::deflist request-list :elt-type request :true-listp t)
(fty::deflist forward-list :elt-type forward :true-listp t)
(fty::deflist response-list :elt-type response :true-listp t)

(defrule request-p-of-nth-request-list
  (implies (and (request-list-p request-list)
                (natp i)
                (< i (len request-list)))
           (request-p (nth i request-list))))

(defrule forward-p-of-last-forward-list
  (implies (and (forward-list-p forward-list)
                (consp forward-list))
           (forward-p (car (last forward-list)))))

(defrule response-p-of-nth-response-list
  (implies (and (response-list-p response-list)
                (natp i)
                (< i (len response-list)))
           (response-p (nth i response-list))))

(defrule request-list-p-of-remove-nth-request-list
  (implies (and (request-list-p request-list)
                (natp i)
                (< i (len request-list)))
           (request-list-p (remove-nth i request-list)))
  :enable remove-nth)

(defrule forward-list-p-of-remove-last-forward-list
  (implies (and (forward-list-p forward-list)
                (consp forward-list))
           (forward-list-p (remove-last forward-list)))
  :enable remove-last)

(defrule response-list-p-of-remove-nth-response-list
  (implies (and (response-list-p response-list)
                (natp i)
                (< i (len response-list)))
           (response-list-p (remove-nth i response-list)))
  :enable remove-nth)

(fty::defprod cache
  ((cache-state cache-state)
   (forwards forward-list)   ;; incoming forwarding requests from
                             ;; directory controller
   (responses response-list) ;; incoming responses from network
   ))

(fty::deflist cache-list :elt-type cache :true-listp t)

(defrule cache-p-of-nth-cache-list
  (implies (and (cache-list-p cache-list)
                (natp i)
                (< i (len cache-list)))
           (cache-p (nth i cache-list))))

; Since we never expect to change the length of a cache-list via
; update-nth, we can just force all these hypotheses.
(defrule cache-list-p-of-update-nth-cache-list
  (implies (and (cache-list-p cache-list)
                (natp i)
                (< i (len cache-list))
                (cache-p new-cache))
           (cache-list-p (update-nth i new-cache cache-list))))

(fty::defprod dir
  ((dir-state dir-state)
   (requests request-list)   ;; incoming requests from network
   ))

;; memory system is a list of caches and a directory
(fty::defprod vi
  ((caches cache-list)
   (dir dir)))

(define dir-process-request
  :guard-debug t
  ((m vi-p)
   (i natp)) ;; which request to process

  :returns (m-prime vi-p
                    :hyp :fguard)

  (b* (((vi m) m)
       ((dir dir) m.dir)
       ((when (<= (len dir.requests) i)) m)
       (request (nth i dir.requests)))
    (request-case request

     (:get
      (b* ((requestor-id request.cache-id)
           ((when (<= (len m.caches) requestor-id)) m)
           ((cache requestor) (nth requestor-id m.caches)))
        (dir-state-case dir.dir-state
         ; Get / I
         (:i
          (b* ((new-dir
                     ; owner = requestor
                (dir (v-dir-state requestor-id)
                     ; remove request
                     (remove-nth i dir.requests)))
               (new-requestor
                (cache requestor.cache-state
                       requestor.forwards
                       ; send data to requestor
                       (cons (resp-data dir.dir-state.data)
                             requestor.responses)))
               (new-caches
                (update-nth requestor-id new-requestor m.caches)))
            (vi new-caches new-dir)))
         ; Get / V
         (:v
          (b* ((owner-id dir.dir-state.owner-id)
               ((when (<= (len m.caches) owner-id)) m)
               ((cache owner) (nth owner-id m.caches))
               (new-dir
                     ; owner = requestor
                (dir (v-dir-state requestor-id)
                     ; remove request
                     (remove-nth i dir.requests)))
               (new-owner
                (cache owner.cache-state
                       ; forward request to owner
                       (cons (fwd-get request.cache-id)
                             owner.forwards)
                       owner.responses))
               (new-caches
                (update-nth owner-id new-owner m.caches)))
            (vi new-caches new-dir))))))

     (:put
      (b* ((requestor-id request.cache-id)
           ((when (<= (len m.caches) requestor-id)) m)
           ((cache requestor) (nth requestor-id m.caches)))
        (dir-state-case dir.dir-state
         (:i m)
         (:v
          (if (= requestor-id dir.dir-state.owner-id)
              ; requestor is owner
              (b* ((new-dir
                         ; copy data, set to I
                    (dir (i-dir-state request.data)
                         ; remove request
                         (remove-nth i dir.requests)))
                   (new-requestor
                    (cache requestor.cache-state
                           ; send put-ack to owner/requestor
                           (cons (fwd-put-ack)
                                 requestor.forwards)
                           requestor.responses))
                   (new-caches
                    (update-nth requestor-id new-requestor m.caches)))
                (vi new-caches new-dir))
            ; requestor is not owner (so it was a previous owner who has been
            ; invalidated by a Get request/forward)
            (b* ((new-dir
                       ; state doesn't change; owner stays the same
                  (dir dir.dir-state
                       ; remove request
                       (remove-nth i dir.requests)))
                 (new-requestor
                  (cache requestor.cache-state
                         ; send put-ack to requestor
                         (cons (fwd-put-ack)
                               requestor.forwards)
                         requestor.responses))
                 (new-caches
                  (update-nth requestor-id new-requestor m.caches)))
              (vi new-caches new-dir))))))))))

(define cache-process-cevent
  ((m vi-p)
   (cevent core-event-p))
  :returns (m-prime vi-p :hyp :fguard)
  (b* (((vi m) m)
       ((dir dir) m.dir))
    (core-event-case cevent
     (:cload
      (b* ((requestor-id cevent.cache-id)
           ((when (<= (len m.caches) requestor-id)) m)
           ((cache requestor) (nth requestor-id m.caches)))
        (cache-state-case requestor.cache-state

         ; Core load / I
         (:i
          (b* ((new-dir
                (dir dir.dir-state
                     (cons (req-get requestor-id) dir.requests)))
               (new-requestor
                (cache (iv-d-state)
                       requestor.forwards
                       requestor.responses))
               (new-caches
                (update-nth requestor-id new-requestor m.caches)))
            (vi new-caches new-dir)))

         ; Core load / V
         ; We have a cache hit, so we can just ``perform'' the load, i.e. stall.
         (:v m)

         ; Core load / IV^D, VI^A, II^A: stall
         (& m))))

     (:cstore
      (b* ((requestor-id cevent.cache-id)
           ((when (<= (len m.caches) requestor-id)) m)
           ((cache requestor) (nth requestor-id m.caches)))
        (cache-state-case requestor.cache-state

        ; Core store / I
        (:i
         (b* ((new-dir
               (dir dir.dir-state
                    (cons (req-get requestor-id) dir.requests)))
              (new-requestor
               (cache (iv-d-state)
                      requestor.forwards
                      requestor.responses))
              (new-caches
               (update-nth requestor-id new-requestor m.caches)))
           (vi new-caches new-dir)))

        ; Core store / V
        ; We have a cache hit, so we can just perform the store
        (:v
         (b* ((new-requestor
               (cache (v-state cevent.data)
                      requestor.forwards
                      requestor.responses))
              (new-caches
               (update-nth requestor-id new-requestor m.caches)))
           (vi new-caches dir)))

        ; Core store / IV^D, VI^A, II^A: stall
        (& m))))

     (:cevict
      (b* ((requestor-id cevent.cache-id)
           ((when (<= (len m.caches) requestor-id)) m)
           ((cache requestor) (nth requestor-id m.caches)))
        (cache-state-case requestor.cache-state

         ; Core evict / I - illegal
         (:i m)

         ; Core evict / V
         (:v
          (b* ((new-dir
                (dir dir.dir-state
                           ; send put to dir
                     (cons (req-put requestor-id requestor.cache-state.data)
                           dir.requests)))
               (new-requestor
                (cache (vi-a-state requestor.cache-state.data)
                       requestor.forwards
                       requestor.responses))
               (new-caches
                (update-nth requestor-id new-requestor m.caches)))
            (vi new-caches new-dir)))

         ; Core evict / IV^D, VI&A, II^A: stall
         (& m)))))))

; The forward network has point-to-point ordering, so we need not supply an
; index for which one to process. We have to process the last one on the list,
; as it was the first one to be sent from the directory.
(define cache-process-forward
  :guard-debug t
  ((m vi-p)
   (cache-id natp))
  :returns (m-prime vi-p :hyp :fguard)
  (b* (((vi m) m)
       ((when (<= (len m.caches) cache-id)) m)
       ((cache cache) (nth cache-id m.caches))
       ((when (endp cache.forwards)) m)
       (forward (car (last cache.forwards)))
       (dir m.dir))
    (forward-case forward
     (:get
      (b* ((requestor-id forward.cache-id)
           ((when (<= (len m.caches) requestor-id))
            m)
           ((cache requestor) (nth requestor-id m.caches)))
        (cache-state-case cache.cache-state

         ; Fwd-Get / V
         (:v
          ; Now, we have two changes to the caches. First of all, the request
          ; should receive the data in his response buffer. Secondly, the
          ; processing cache must change to I and remove the message from his
          ; forward buffer. We do these one at a time, first updating the
          ; requestor, then the processing cache.
          (b* ((new-requestor
                (cache requestor.cache-state
                       requestor.forwards
                       ; send data to requestor
                       (cons (resp-data cache.cache-state.data)
                             requestor.responses)))
               ; update the requestor.
               (new-caches
                (update-nth requestor-id new-requestor m.caches))
               ; get the cache state again (just in case cache = requestor, we
               ; need to combine the changes to the requestor and to this
               ; cache)
               ((cache cache) (nth cache-id new-caches))
               (new-cache
                (cache (i-state)
                       ; remove forward
                       (remove-last cache.forwards)
                       cache.responses))
               (new-caches
                (update-nth cache-id new-cache new-caches)))
            (vi new-caches dir)))

         ; Fwd-Get / VI^A
         (:vi-a
          (b* ((new-requestor
                (cache requestor.cache-state
                       requestor.forwards
                       ; send data to requestor
                       (cons (resp-data cache.cache-state.data)
                             requestor.responses)))
               ; update the requestor
               (new-caches
                (update-nth requestor-id new-requestor m.caches))
               ; get the cache state again
               ((cache cache) (nth cache-id new-caches))
               (new-cache
                (cache (ii-a-state)
                       ; remove forward
                       (remove-last cache.forwards)
                       cache.responses))
               (new-caches
                (update-nth cache-id new-cache new-caches)))
            (vi new-caches dir)))

         ; Fwd-Get / IV^D - stall
         (:iv-d m)

         ; Fwd-Get / I, II^A - error
         (& m))))

     (:put-ack
      (cache-state-case cache.cache-state

       ; Put-Ack / VI^A
       (:vi-a
        (b* ((new-cache
              (cache (i-state)
                     ; remove forward
                     (remove-last cache.forwards)
                     cache.responses))
             (new-caches
              (update-nth cache-id new-cache m.caches)))
          (vi new-caches dir)))

       ; Put-Ack / II^A
       (:ii-a
        (b* ((new-cache
              (cache (i-state)
                     ; remove forward
                     (remove-last cache.forwards)
                     cache.responses))
             (new-caches
              (update-nth cache-id new-cache m.caches)))
          (vi new-caches dir)))

       ; Put-Ack / I, IV^D, V - error
       (& m))))))

(define cache-process-response
  ((m vi-p)
   (cache-id natp)
   (i natp)) ;; which response to process
  :returns (m-prime vi-p :hyp :fguard)
  (b* (((vi m) m)
       ((when (<= (len m.caches) cache-id)) m)
       ((cache cache) (nth cache-id m.caches))
       ((when (<= (len cache.responses) i)) m)
       (response (nth i cache.responses)))
    (response-case response
     (:data
      (cache-state-case cache.cache-state

       ; Data / IV^D
       (:iv-d
        (b* ((new-cache
                     ; state V, copy the incoming data
              (cache (v-state response.data)
                     cache.forwards
                     ; remove response
                     (remove-nth i cache.responses)))
             (new-caches
              (update-nth cache-id new-cache m.caches)))
          (vi new-caches m.dir)))

       ; All other states are errors
       (& m))))))
