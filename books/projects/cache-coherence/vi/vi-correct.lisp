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

(include-book "vi-impl")
(include-book "utils")

;; A simple cache coherency protocol with two states: Valid and Invalid.
;; Similar in spirit to the German protocol verified by Sandip Ray, this effort
;; takes an approach that starts with a goal invariant and develops many helper
;; invariants while trying to prove this goal invariant.

;; The whole idea of this particular approach is to define a notion of
;; ``has-data'' -- when does a cache ``have'' the data, and when does the
;; directory ``have'' the data? If we can formulate this property so that
;; exactly one agent has the data at any given time, we should be able to prove
;; it is invariant (maybe with a few additional assumptions) without much
;; trouble.

;; To have the data is to be responsible for it. In most cases, it is
;; unambiguous whether a particular agent is responsible for the data - it is
;; whoever HAS the data, literally -- either in cache, or in an input
;; buffer. However, there is one scenario where two agents have the data - when
;; the owner evicts, he is in VI^A and so still has the data, but at the same
;; time there is a put request at the directory with another valid copy of the
;; data. In this scenario, we decided that the directory should be thought of
;; as ``responsible'' for the data, since it is up to him whether or not the
;; evicting cache needs to service any additional requests. The directory can
;; then send the responsibility back to the evicting cache with a forwarded get
;; request.

;; In retrospect, I should have started directory-centric - simply declare that
;; the directory has the data when he is in I, and he does not have the data
;; when he is in V. Then we would have a slightly messier definition of
;; cache-has-data, but a SIGNIFICANTLY cleaner definition of
;; dir-has-data. Cache-has-data would need to be modified in the VI^A case - a
;; cache in VI^A would have the data if its forward buffer was empty, OR the
;; first forward in its buffer was a get. If its forward buffer is non-empty
;; and the first forward is a put-ack, then we would say he no longer is
;; responsible. I believe this would have worked just as well to conduct the
;; exclusivity proof and it would have ultimately been easier since I wouldn't
;; have needed to define the notion of the directory having a put-from-owner,
;; which necessitated a defun-sk with ``exists'' (Yuck).

;; So, our notion of cache-has-data is defined as follows. Depending on what
;; the state of the cache is in, we have different requirements for
;; cache-has-data.
;;
;; State    Has-data
;;     I    no
;;  IV^D    only if data in response buffer
;;     V    yes
;;  VI^A    only if get in forward buffer
;;  II^A    no
;;
;; Likewise, dir-has-data is defined as follows.
;;
;; State    Has-data
;;     I    yes
;;     V    only if put-owner in request buffer
;;
;; I designed these notions so that every single valid transition step in the
;; system will either maintain has-data, or will transfer it from one agent to
;; another. In other words, there is always exactly one agent that has-data at
;; any given time. This is formalized in the definition of one-has-data, and
;; our verification task is to show that one-has-data is an invariant of our
;; system. All by itself, it is not quite an inductive invariant, but we only
;; need 8 or so other properties to make it inductive. We invent these
;; properties as we go, and then at the end we wrap them all up in
;; big-invariant and show that big-invariant is an inductive invariant under
;; the four transitions in our system. Since big-invariant -> one-has-data ->
;; i-v-j-v, we know that if we start in a state that satisfies big-invariant,
;; we cannot get to a state that does not satisfy i-v-j-v. So the final step in
;; the proof is to show that our ``start-state'' function which generates a
;; start state actually satisfies big-invariant.

;; When does a cache ``have'' data?
(define cache-has-data
  ((m vi-p)
   (i (cache-index-p m i)))
  (b* (((vi m) m)
       ((cache cachei) (nth i m.caches)))
    (cache-state-case
     cachei.cache-state
     (:i nil)
     (:iv-d (consp cachei.responses))
     (:v t)
     (:vi-a
      (b* (((unless (consp cachei.forwards)) nil)
           (fwd (car (last cachei.forwards))))
        (forward-case
         fwd
         (:get t)
         (:put-ack nil))))
     (:ii-a nil))))

;; To define dir-has-data, we need to define the concept of the directory
;; having a put from the owner. So we define request-list-has-put-from-cache,
;; which we will use to specify this concept when we define dir-has-data.
(define request-list-has-put-from-cache-unq
  ((requests request-list-p)
   (cache-id natp)
   (req-i-idx (and (natp req-i-idx)
                   (< req-i-idx (len requests)))))
  (b* ((req (nth req-i-idx requests)))
    (request-case
     req
     (:put (= cache-id req.cache-id))
     (:get nil))))

(defun-sk request-list-has-put-from-cache (requests cache-id)
  (exists req-i-idx
          (implies (and (request-list-p requests)
                        (natp cache-id))
                   (and (natp req-i-idx)
                        (< req-i-idx (len requests))
                        (request-list-has-put-from-cache-unq requests
                                                             cache-id
                                                             req-i-idx)))))

(in-theory (disable request-list-has-put-from-cache
                    request-list-has-put-from-cache-suff))

;; Useful rules about request-list-has-put-from-cache

(defrule in-range-implies-nth
  (implies (and (request-list-p requests)
                (natp req-i-idx)
                (< req-i-idx (len requests)))
           (nth req-i-idx requests)))

(defrule request-list-has-put-from-cache-remove-nth
  (implies (and (request-list-p requests)
                (natp req-i-idx)
                (< req-i-idx (len requests))
                (natp cache-id)
                (request-list-has-put-from-cache
                 (remove-nth req-i-idx requests)
                 cache-id))
           (request-list-has-put-from-cache requests cache-id))
  :expand (request-list-has-put-from-cache
           (remove-nth req-i-idx requests)
           cache-id)
  :enable (request-list-has-put-from-cache-unq)
  :disable nth
  :use ((:instance nth-remove-nth
                   (i req-i-idx)
                   (j (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS (REMOVE-NTH REQ-I-IDX REQUESTS)
                                                               CACHE-ID))
                   (x requests))
        (:instance request-list-has-put-from-cache-suff
                   (req-i-idx (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                               (REMOVE-NTH REQ-I-IDX REQUESTS)
                               CACHE-ID)))
        (:instance request-list-has-put-from-cache-suff
                   (req-i-idx (1+ (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                   (REMOVE-NTH REQ-I-IDX REQUESTS)
                                   CACHE-ID))))))

(local (include-book "arithmetic/top-with-meta" :dir :system))
(defrule request-list-has-put-from-cache-remove-nth-2
  (implies (and (request-list-p requests)
                (natp req-i-idx)
                (< req-i-idx (len requests))
                (natp cache-id)
                (equal (request-kind (nth req-i-idx requests)) :put)
                (not (equal (req-put->cache-id (nth req-i-idx requests)) cache-id))
                (request-list-has-put-from-cache
                 requests
                 cache-id))
           (request-list-has-put-from-cache
            (remove-nth req-i-idx requests)
            cache-id))
  :do-not-induct t
  :enable request-list-has-put-from-cache-unq
  :expand (request-list-has-put-from-cache requests cache-id)
  :cases ((< req-i-idx
             (request-list-has-put-from-cache-witness requests cache-id))
          (= req-i-idx
             (request-list-has-put-from-cache-witness requests cache-id)))
  :disable nth
  :use ((:instance request-list-has-put-from-cache-suff
                   (requests (remove-nth req-i-idx requests))
                   (cache-id cache-id)
                   (req-i-idx
                    (request-list-has-put-from-cache-witness
                     requests cache-id)))
        (:instance nth-remove-nth
                   (i req-i-idx)
                   (j (request-list-has-put-from-cache-witness
                       requests cache-id))
                   (x requests))
        (:instance request-list-has-put-from-cache-suff
                   (requests (remove-nth req-i-idx requests))
                   (cache-id cache-id)
                   (req-i-idx
                    (1- (request-list-has-put-from-cache-witness
                         requests cache-id))))
        (:instance nth-remove-nth
                   (i req-i-idx)
                   (j (1- (request-list-has-put-from-cache-witness
                           requests cache-id)))
                   (x requests))))

(define dir-has-put-owner
  :verify-guards nil
  :enabled t
  ((m vi-p))
  (b* (((vi m) m)
       ((dir dir) m.dir))
    (dir-state-case
     dir.dir-state
     (:i nil)
     (:v (request-list-has-put-from-cache dir.requests dir.dir-state.owner-id)))))

;; When does the directory ``have'' data? If it is in state I, of course - but
;; if it is in state V and it has a put from the owner, we know that put
;; contains the most recent data, so the directory must be thought to ``have''
;; the data then as well.
(define dir-has-data
  :verify-guards nil
  ((m vi-p))
  (b* (((vi m) m)
       ((dir dir) m.dir))
    (dir-state-case
     dir.dir-state
     (:i t)
; If the dir is in state V, the only way he ``has data'' is if he has a
; put from the owner (because he could then transition to I in one step).
     (:v (dir-has-put-owner m)))))

(defun-sk dir-has-data-i-has-data (m)
  (forall i
          (implies (and (vi-p m)                 ; type
                        (cache-index-p m i)      ; type
                        (dir-has-data m))        ; hyp
                   (not (cache-has-data m i))))) ; conc

(in-theory (disable dir-has-data-i-has-data
                    dir-has-data-i-has-data-necc))

(defun-sk i-has-data-j-has-data (m)
  (forall (i j)
          (implies (and (vi-p m)               ; type
                        (cache-index-p m i)    ; type
                        (cache-index-p m j)    ; type
                        (not (= i j))          ; hyp
                        (cache-has-data m i))    ; hyp
                   (not (cache-has-data m j))))) ; conclusion

(in-theory (disable i-has-data-j-has-data
                    i-has-data-j-has-data-necc))

; leave enabled
(defun one-has-data (m)
  (and (dir-has-data-i-has-data m)
       (i-has-data-j-has-data m)))

; dpr

(define two-reqs-same-cache-unq
  ((m vi-p)
   (req-i-idx (request-index-p m req-i-idx))
   (req-j-idx (request-index-p m req-j-idx)))
  (b* (((vi m) m)
       ((dir dir) m.dir)
       ((when (= req-i-idx req-j-idx)) t)
       (req-i (nth req-i-idx dir.requests))
       (reqj (nth req-j-idx dir.requests)))
    (request-case
     req-i
     (:get
      (request-case
       reqj
       (:get (not (= req-i.cache-id reqj.cache-id)))
       (:put (not (= req-i.cache-id reqj.cache-id)))))
     (:put
      (request-case
       reqj
       (:get (not (= req-i.cache-id reqj.cache-id)))
       (:put (not (= req-i.cache-id reqj.cache-id))))))))

(defun-sk two-reqs-same-cache (m)
  (forall (req-i-idx req-j-idx)
          (implies (and (vi-p m)
                        (request-index-p m req-i-idx)
                        (request-index-p m req-j-idx)
                        (not (= req-i-idx req-j-idx)))
                   (two-reqs-same-cache-unq m req-i-idx req-j-idx))))

(in-theory (disable two-reqs-same-cache
                    two-reqs-same-cache-necc))

(defrule dpr-one-has-data-1-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (two-reqs-same-cache m)
                (request-index-p m req-i-idx)
                (cache-index-p m i)
                (dir-has-data (dir-process-request m req-i-idx)))
           (not (cache-has-data (dir-process-request m req-i-idx) i)))
  :enable (cache-has-data
           dir-has-data
           two-reqs-same-cache-unq
           request-list-has-put-from-cache-unq
           dir-process-request)
  :disable nth
  :hints (("Subgoal 20.2"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 20.1"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 19.2"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 19.1"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 18.2"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 18.1"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 17"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE
                    (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                    (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M))))))
                            (x (dir->requests (vi->dir m))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                        (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                        (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (+ 1
                                          (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                           (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                           (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR
                                                                                             M))))))))))
          ("Subgoal 16"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE
                    (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                    (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M))))))
                            (x (dir->requests (vi->dir m))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                        (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                        (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (1+ (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                            (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                            (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M))))))))))
          ("Subgoal 15"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE
                    (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                    (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M))))))
                            (x (dir->requests (vi->dir m))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                        (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                        (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (1+ (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                            (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                            (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR
                                                                                              M))))))))))
          ("Subgoal 14"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE
                    (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                    (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M))))))
                            (x (dir->requests (vi->dir m))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                        (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                        (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (1+ (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                                            (REMOVE-NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR M)))
                                            (REQ-GET->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS (VI->DIR
                                                                                              M))))))))))
          ("Subgoal 13"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 12"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 11"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 10"
           :use ((:instance dir-has-data-i-has-data-necc
                            (i (REQ-PUT->CACHE-ID (NTH REQ-I-IDX (DIR->REQUESTS
                                                                  (VI->DIR M))))))))
          ("Subgoal 9"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 8"
           :use ((:instance dir-has-data-i-has-data-necc
                            (i (v-dir-state->owner-id
                                (dir->dir-state
                                 (vi->dir m)))))
                 (:instance dir-has-data-i-has-data-necc)
                 (:instance request-list-has-put-from-cache-suff
                            (requests (dir->requests (vi->dir m)))
                            (cache-id (v-dir-state->owner-id
                                       (dir->dir-state
                                        (vi->dir m)))))))
          ("Subgoal 6"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 5"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 4"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 3"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 2"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 1"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ))

(defrule dpr-one-has-data-1
  (implies (and (vi-p m)
                (one-has-data m)
                (two-reqs-same-cache m)
                (request-index-p m req-i-idx))
           (dir-has-data-i-has-data (dir-process-request m req-i-idx)))
  :expand (dir-has-data-i-has-data (dir-process-request m req-i-idx)))

(define i-resp-i-state-unq
  ((m vi-p)
   (i (cache-index-p m i)))
  (b* (((vi m) m)
       ((cache cachei) (nth i m.caches)))
    (implies (consp cachei.responses)
             (and (equal (cache-state-kind cachei.cache-state) :iv-d)
                  (endp (cdr cachei.responses))))))

(defun-sk i-resp-i-state (m)
  (forall i
          (implies (and (vi-p m)
                        (cache-index-p m i))
                   (i-resp-i-state-unq m i))))

(in-theory (disable i-resp-i-state
                    i-resp-i-state-necc))

(defrule request-list-has-put-from-cache-cons-get
  (implies (and (request-list-p requests)
                (natp i)
                (natp cache-id))
           (iff (request-list-has-put-from-cache
                 (cons (req-get i) requests)
                 cache-id)
                (request-list-has-put-from-cache requests cache-id)))
  :enable request-list-has-put-from-cache-unq
  :hints (("Subgoal 1"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE (CONS (REQ-GET I) REQUESTS)
                                                    CACHE-ID)
           :use ((:instance request-list-has-put-from-cache-suff
                            (req-i-idx
                             (1-
                              (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                               (CONS (REQ-GET I) REQUESTS) CACHE-ID))))))
          ("Subgoal 2"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE REQUESTS CACHE-ID)
           :use ((:instance request-list-has-put-from-cache-suff
                            (requests (cons (req-get i) requests))
                            (req-i-idx
                             (1+
                              (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                               REQUESTS CACHE-ID))))))))

(defrule request-list-has-put-from-cache-cons-put
  (implies (and (request-list-p requests)
                (natp i)
                (integerp data)
                (natp cache-id))
           (iff (request-list-has-put-from-cache
                 (cons (req-put i data) requests)
                 cache-id)
                (or
                 (= i cache-id)
                 (request-list-has-put-from-cache requests cache-id))))
  :enable request-list-has-put-from-cache-unq
  :hints (("Subgoal 3"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE (CONS (REQ-PUT I DATA) REQUESTS)
                                                    CACHE-ID)
           :use ((:instance request-list-has-put-from-cache-suff
                            (req-i-idx
                             (1-
                              (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                               (CONS (REQ-PUT I DATA) REQUESTS) CACHE-ID))))))
          ("Subgoal 2"
           :expand (REQUEST-LIST-HAS-PUT-FROM-CACHE REQUESTS CACHE-ID)
           :use ((:instance request-list-has-put-from-cache-suff
                            (requests (cons (req-put i data) requests))
                            (req-i-idx
                             (1+
                              (REQUEST-LIST-HAS-PUT-FROM-CACHE-WITNESS
                               REQUESTS CACHE-ID))))))
          ("Subgoal 1"
           :use ((:instance request-list-has-put-from-cache-suff
                            (requests (cons (req-put cache-id data) requests))
                            (req-i-idx 0))))))

(define i-get-i-state-unq
  ((m vi-p)
   (i (cache-index-p m i)))
  (b* (((vi m) m)
       ((dir dir) m.dir)
       ((cache cachei) (nth i m.caches))
       ((unless (consp cachei.forwards)) t)
       (fwd (car (last cachei.forwards))))
    (and
     (dir-state-case
      dir.dir-state
      (:i t)
      (:v (not (= i dir.dir-state.owner-id))))
     (forward-case
      fwd
      (:get
       (cache-state-case
        cachei.cache-state
        (:iv-d (endp (remove-last cachei.forwards)))
        (:v (endp (remove-last cachei.forwards)))
        (:vi-a (or (endp (remove-last cachei.forwards))
                   (and (equal (forward-kind
                                (car (last (remove-last cachei.forwards))))
                               :put-ack)
                        (endp (remove-last (remove-last cachei.forwards))))))
        (& nil)))
      (& t)))))

(defun-sk i-get-i-state (m)
  (forall i
          (implies (and (vi-p m)
                        (cache-index-p m i))
                   (i-get-i-state-unq m i))))

(in-theory (disable i-get-i-state
                    i-get-i-state-necc))

(defrule cpc-one-has-data-1-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (i-resp-i-state m)
                (i-get-i-state m)
                (core-event-p cevent)
                (dir-has-data (cache-process-cevent m cevent))
                (cache-index-p m i))
           (not (cache-has-data (cache-process-cevent m cevent) i)))
  :enable (cache-has-data
           dir-has-data
           i-resp-i-state-unq
           i-get-i-state-unq
;           two-reqs-same-cache-unq
           request-list-has-put-from-cache-unq
           cache-process-cevent)
  :hints (("Subgoal 29"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 28"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 27"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 26"
           :use ((:instance i-resp-i-state-necc
                            (i (cload->cache-id cevent)))))
          ("Subgoal 25"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 24"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 23"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 22"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 21"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 20"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 19"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 18"
           :use (
                 (:instance i-get-i-state-necc
                            (i (cevict->cache-id cevent)))
                 (:instance dir-has-data-i-has-data-necc
                            (i (cevict->cache-id cevent)))))
          ("Subgoal 17"
           :use ((:instance dir-has-data-i-has-data-necc)
                 (:instance i-has-data-j-has-data-necc
                            (j (cevict->cache-id cevent)))))
          ("Subgoal 16"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 15"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 14"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 13"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 12"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 11"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 10"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 9"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 8"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 7"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 6"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 5"
           :use ((:instance i-resp-i-state-necc
                            (i (cstore->cache-id cevent)))))
          ("Subgoal 4"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 3"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 2"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ("Subgoal 1"
           :use ((:instance dir-has-data-i-has-data-necc)))
          ))

(defrule cpc-one-has-data-1
  (implies (and (vi-p m)
                (one-has-data m)
                (i-resp-i-state m)
                (i-get-i-state m)
                (core-event-p cevent))
           (dir-has-data-i-has-data (cache-process-cevent m cevent)))
  :expand (dir-has-data-i-has-data (cache-process-cevent m cevent)))

(defrule cpf-one-has-data-1-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i)
                (cache-index-p m j)
                (dir-has-data (cache-process-forward m i)))
           (not (cache-has-data (cache-process-forward m i) j)))
  :enable (cache-has-data
           dir-has-data
           request-list-has-put-from-cache-unq
           cache-process-forward)
  :use ((:instance dir-has-data-i-has-data-necc (i j))
        (:instance dir-has-data-i-has-data-necc)))

(defrule cpf-one-has-data-1
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i))
           (dir-has-data-i-has-data (cache-process-forward m i)))
  :expand (dir-has-data-i-has-data (cache-process-forward m i)))

(defrule cpr-one-has-data-1-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j)
                (dir-has-data (cache-process-response m i response-i)))
           (not (cache-has-data (cache-process-response m i response-i)
                                j)))
  :enable (cache-has-data
           dir-has-data
           request-list-has-put-from-cache-unq
           cache-process-response)
  :use ((:instance dir-has-data-i-has-data-necc)
        (:instance dir-has-data-i-has-data-necc (i j))))

(defrule cpr-one-has-data-1
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (dir-has-data-i-has-data (cache-process-response m i response-i)))
  :expand (dir-has-data-i-has-data (cache-process-response m i response-i)))

(define owner-state-unq
  :verify-guards nil
  ((m vi-p))
  (b* (((vi m) m)
       ((dir dir) m.dir))
    (dir-state-case
     dir.dir-state
     (:i t)
     (:v (b* (((unless (cache-index-p m dir.dir-state.owner-id)) t)
              ((cache owner) (nth dir.dir-state.owner-id m.caches)))
           (cache-state-case
            owner.cache-state
            (:iv-d (endp owner.forwards))
            (:v (and (endp owner.forwards)
                     (endp owner.responses)))
            (:vi-a (and (endp owner.forwards)
                        (endp owner.responses)
                        (request-list-has-put-from-cache
                         dir.requests
                         dir.dir-state.owner-id)))
            (& nil)))))))

(defun owner-state (m)
  (implies (vi-p m)
           (owner-state-unq m)))

(defrule owner-state-necc
  (implies (and (vi-p m)
                (owner-state m))
           (owner-state-unq m)))

(in-theory (disable owner-state owner-state-necc))

(defrule dpr-one-has-data-2-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (owner-state m)
                (request-index-p m req-i-idx)
                (cache-index-p m i)
                (cache-index-p m j)
                (not (= i j))
                (cache-has-data (dir-process-request m req-i-idx) i))
           (not (cache-has-data (dir-process-request m req-i-idx) j)))
  :enable (cache-has-data
           dir-has-data
           owner-state-unq
           request-list-has-put-from-cache-unq
           dir-process-request)
  :use ((:instance i-has-data-j-has-data-necc)
        (:instance owner-state-necc)
        (:instance dir-has-data-i-has-data-necc
                   (i j))
        (:instance dir-has-data-i-has-data-necc)))

; why do i need an instance hint?
(defrule dpr-one-has-data-2
  (implies (and (vi-p m)
                (one-has-data m)
                (owner-state m)
                (request-index-p m req-i-idx))
           (i-has-data-j-has-data (dir-process-request m req-i-idx)))
  :expand (i-has-data-j-has-data (dir-process-request m req-i-idx))
  :use ((:instance dpr-one-has-data-2-unq
                   (i (MV-NTH
                       0
                       (I-HAS-DATA-J-HAS-DATA-WITNESS (DIR-PROCESS-REQUEST M
                                                                           REQ-I-IDX))))
                   (j (MV-NTH
                       1
                       (I-HAS-DATA-J-HAS-DATA-WITNESS (DIR-PROCESS-REQUEST M
                                                                           REQ-I-IDX)))))))

(defrule cpc-one-has-data-2-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (i-resp-i-state m)
                (core-event-p cevent)
                (cache-index-p m i)
                (cache-index-p m j)
                (not (= i j))
                (cache-has-data (cache-process-cevent m cevent) i))
           (not (cache-has-data (cache-process-cevent m cevent) j)))
  :enable (cache-has-data
           dir-has-data
           i-resp-i-state-unq
           request-list-has-put-from-cache-unq
           cache-process-cevent)
  :use ((:instance i-has-data-j-has-data-necc)
        (:instance i-resp-i-state-necc (i (cload->cache-id cevent)))
        (:instance i-resp-i-state-necc (i (cstore->cache-id cevent)))))

(defrule cpc-one-has-data-2
  (implies (and (vi-p m)
                (one-has-data m)
                (i-resp-i-state m)
                (core-event-p cevent))
           (i-has-data-j-has-data (cache-process-cevent m cevent)))
  :expand (i-has-data-j-has-data (cache-process-cevent m cevent))
  :use ((:instance cpc-one-has-data-2-unq
                   (i (MV-NTH
                       0
                       (I-HAS-DATA-J-HAS-DATA-WITNESS (CACHE-PROCESS-CEVENT M
                                                                            CEVENT))))
                   (j (MV-NTH
                       1
                       (I-HAS-DATA-J-HAS-DATA-WITNESS (CACHE-PROCESS-CEVENT M
                                                                            CEVENT)))))))

(defrule cpf-one-has-data-2-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i)
                (cache-index-p m j)
                (cache-index-p m k)
                (not (= j k))
                (cache-has-data (cache-process-forward m i) j))
           (not (cache-has-data (cache-process-forward m i) k)))
  :enable (cache-has-data
           dir-has-data
           request-list-has-put-from-cache-unq
           cache-process-forward)
  :use ((:instance i-has-data-j-has-data-necc (i j) (j k))
        (:instance i-has-data-j-has-data-necc)
        (:instance i-has-data-j-has-data-necc (j k))))

(defrule cpf-one-has-data-2
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i))
           (i-has-data-j-has-data (cache-process-forward m i)))
  :expand (i-has-data-j-has-data (cache-process-forward m i))
  :use ((:instance cpf-one-has-data-2-unq
                   (j (MV-NTH 0
                              (I-HAS-DATA-J-HAS-DATA-WITNESS (CACHE-PROCESS-FORWARD M I))))
                   (k (MV-NTH 1
                              (I-HAS-DATA-J-HAS-DATA-WITNESS (CACHE-PROCESS-FORWARD M I)))))))

(defrule cpr-one-has-data-2-unq
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j)
                (cache-index-p m k)
                (not (= j k))
                (cache-has-data (cache-process-response m i response-i)
                                j))
           (not (cache-has-data (cache-process-response m i response-i)
                                k)))
  :enable (cache-has-data
           dir-has-data
           request-list-has-put-from-cache-unq
           cache-process-response)
  :use ((:instance i-has-data-j-has-data-necc (i j) (j k))))

(defrule cpr-one-has-data-2
  (implies (and (vi-p m)
                (one-has-data m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (i-has-data-j-has-data (cache-process-response m i response-i)))
  :expand (i-has-data-j-has-data (cache-process-response m i response-i))
  :use ((:instance cpr-one-has-data-2-unq
                   (j (MV-NTH 0
                              (I-HAS-DATA-J-HAS-DATA-WITNESS
                               (CACHE-PROCESS-RESPONSE M I RESPONSE-I))))
                   (k (MV-NTH 1
                              (I-HAS-DATA-J-HAS-DATA-WITNESS
                               (CACHE-PROCESS-RESPONSE M I RESPONSE-I)))))))

;; Okay, so what's left?
;;
;; two-reqs-same-cache
;; i-resp-i-state
;; i-get-i-state
;; owner-state

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; two-reqs-same-cache proof ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule dpr-two-reqs-same-cache-unq
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (request-index-p m req-i-idx)
                (request-index-p (dir-process-request m req-i-idx)
                                 req-j-idx)
                (request-index-p (dir-process-request m req-i-idx)
                                 req-k-idx))
           (two-reqs-same-cache-unq (dir-process-request m req-i-idx)
                                    req-j-idx
                                    req-k-idx))
  :enable (two-reqs-same-cache-unq
           dir-process-request)
  :disable nth
  :use ((:instance two-reqs-same-cache-necc
                   (req-i-idx req-j-idx)
                   (req-j-idx req-k-idx))
        (:instance nth-remove-nth
                   (i req-i-idx)
                   (j req-j-idx)
                   (x (dir->requests (vi->dir m))))
        (:instance nth-remove-nth
                   (i req-i-idx)
                   (j req-k-idx)
                   (x (dir->requests (vi->dir m))))
        (:instance two-reqs-same-cache-necc
                   (req-i-idx req-j-idx)
                   (req-j-idx (+ 1 req-k-idx)))
        (:instance two-reqs-same-cache-necc
                   (req-i-idx (+ 1 req-j-idx))
                   (req-j-idx req-k-idx))
        (:instance two-reqs-same-cache-necc
                   (req-i-idx (+ 1 req-j-idx))
                   (req-j-idx (+ 1 req-k-idx)))))


(defrule dpr-two-reqs-same-cache
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (request-index-p m req-i-idx))
           (two-reqs-same-cache (dir-process-request m req-i-idx)))
  :expand (two-reqs-same-cache (dir-process-request m req-i-idx)))

(define req-state-unq
  ((m vi-p)
   (req-i-idx (request-index-p m req-i-idx)))
  (b* (((vi m) m)
       ((dir dir) m.dir)
       (req-i (nth req-i-idx dir.requests)))
    (request-case
     req-i
     (:get (b* (((unless (cache-index-p m req-i.cache-id)) t)
                ((cache getter) (nth req-i.cache-id m.caches)))
             (and (equal (cache-state-kind getter.cache-state) :iv-d)
                  (endp getter.responses)
                  (endp getter.forwards)
                  (dir-state-case
                   dir.dir-state
                   (:i t)
                   (:v (not (= req-i.cache-id dir.dir-state.owner-id)))))))
     (:put (b* (((unless (cache-index-p m req-i.cache-id)) t)
                ((cache putter) (nth req-i.cache-id m.caches)))
             (cache-state-case
              putter.cache-state
              (:vi-a (b* (((when (endp putter.forwards)) t)
                          (fwd (car (last putter.forwards))))
                       (and (equal (forward-kind fwd) :get)
                            (endp (remove-last putter.forwards))
                            (endp putter.responses))))
              (:ii-a (and (endp putter.forwards)
                          (endp putter.responses)))
              (& nil)))))))

(defun-sk req-state (m)
  (forall req-i-idx
          (implies (and (vi-p m)
                        (request-index-p m req-i-idx))
                   (req-state-unq m req-i-idx))))

(in-theory (disable req-state req-state-necc))

(defrule cpc-two-reqs-same-cache-unq
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (req-state m)
                (core-event-p cevent)
                (request-index-p (cache-process-cevent m cevent)
                                 req-i-idx)
                (request-index-p (cache-process-cevent m cevent)
                                 req-j-idx))
           (two-reqs-same-cache-unq (cache-process-cevent m cevent)
                                    req-i-idx req-j-idx))
  :enable (two-reqs-same-cache-unq
           req-state-unq
           cache-process-cevent)
  :disable nth
  :hints (("Subgoal 44"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 43"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 42"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 41"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 39"
           :use ((:instance req-state-necc
                            (req-i-idx (1- req-j-idx)))))
          ("Subgoal 38"
           :use ((:instance req-state-necc
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 37"
           :use ((:instance two-reqs-same-cache-necc
                            (req-i-idx (1- req-i-idx))
                            (req-j-idx (1- req-j-idx)))))
          ("Subgoal 36"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 35"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 34"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 33"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 32"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 31"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 30"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 29"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 27"
           :use ((:instance req-state-necc
                            (req-i-idx (1- req-j-idx)))))
          ("Subgoal 26"
           :use ((:instance req-state-necc
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 25"
           :use ((:instance two-reqs-same-cache-necc
                            (req-i-idx (1- req-i-idx))
                            (req-j-idx (1- req-j-idx)))))
          ("Subgoal 24"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 23"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 22"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 21"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 20"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 19"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 18"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 17"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 16"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 15"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 14"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 13"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 12"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 11"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 10"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 9"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 7"
           :use ((:instance req-state-necc
                            (req-i-idx (1- req-j-idx)))))
          ("Subgoal 6"
           :use ((:instance req-state-necc
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 5"
           :use ((:instance two-reqs-same-cache-necc
                            (req-i-idx (1- req-i-idx))
                            (req-j-idx (1- req-j-idx)))))
          ("Subgoal 4"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 3"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 2"
           :use ((:instance two-reqs-same-cache-necc)))
          ("Subgoal 1"
           :use ((:instance two-reqs-same-cache-necc)))
          ))

(defrule cpc-two-reqs-same-cache
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (req-state m)
                (core-event-p cevent))
           (two-reqs-same-cache (cache-process-cevent m cevent)))
  :expand (two-reqs-same-cache (cache-process-cevent m cevent)))

(defrule cpf-two-reqs-same-cache-unq
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (cache-index-p m i)
                (request-index-p (cache-process-forward m i)
                                 req-i-idx)
                (request-index-p (cache-process-forward m i)
                                 req-j-idx))
           (two-reqs-same-cache-unq (cache-process-forward m i)
                                    req-i-idx req-j-idx))
  :enable (two-reqs-same-cache-unq
           cache-process-forward)
  :use ((:instance two-reqs-same-cache-necc)))

(defrule cpf-two-reqs-same-cache
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (cache-index-p m i))
           (two-reqs-same-cache (cache-process-forward m i)))
  :expand (two-reqs-same-cache (cache-process-forward m i)))

(defrule cpr-two-reqs-same-cache-unq
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (request-index-p (cache-process-response m i response-i)
                                 req-i-idx)
                (request-index-p (cache-process-response m i response-i)
                                 req-j-idx))
           (two-reqs-same-cache-unq (cache-process-response m i response-i)
                                    req-i-idx req-j-idx))
  :enable (two-reqs-same-cache-unq
           cache-process-response)
  :use ((:instance two-reqs-same-cache-necc)))

(defrule cpr-two-reqs-same-cache
  (implies (and (vi-p m)
                (two-reqs-same-cache m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (two-reqs-same-cache (cache-process-response m i response-i)))
  :expand (two-reqs-same-cache (cache-process-response m i response-i)))


;; Okay, so what's left?
;;
;; i-resp-i-state
;; i-get-i-state
;; owner-state
;; req-state

(defrule dpr-i-resp-i-state-unq
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (req-state m)
                (request-index-p m req-i-idx)
                (cache-index-p m i))
           (i-resp-i-state-unq (dir-process-request m req-i-idx)
                               i))
  :enable (i-resp-i-state-unq
           req-state-unq
           dir-process-request)
  :use ((:instance i-resp-i-state-necc)
        (:instance req-state-necc)))

(defrule dpr-i-resp-i-state
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (req-state m)
                (request-index-p m req-i-idx))
           (i-resp-i-state (dir-process-request m req-i-idx)))
  :expand (i-resp-i-state (dir-process-request m req-i-idx)))

(defrule cpc-i-resp-i-state-unq
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (core-event-p cevent)
                (cache-index-p m i))
           (i-resp-i-state-unq (cache-process-cevent m cevent)
                               i))
  :enable (i-resp-i-state-unq
           cache-process-cevent)
  :use ((:instance i-resp-i-state-necc)))

(defrule cpc-i-resp-i-state
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (core-event-p cevent))
           (i-resp-i-state (cache-process-cevent m cevent)))
  :expand (i-resp-i-state (cache-process-cevent m cevent)))

(define i-get-getter-state-unq
  ((m vi-p)
   (i (cache-index-p m i)))
  (b* (((vi m) m)
       ((cache cachei) (nth i m.caches))
       ((unless (consp cachei.forwards)) t)
       (fwd (car (last cachei.forwards))))
    (forward-case
     fwd
     (:get
      (b* (((unless (cache-index-p m fwd.cache-id)) t)
           ((cache getter) (nth fwd.cache-id m.caches)))
        (and (equal (cache-state-kind getter.cache-state) :iv-d)
             (endp getter.responses))))
     (& t))))

(defun-sk i-get-getter-state (m)
  (forall i
          (implies (and (vi-p m)
                        (cache-index-p m i))
                   (i-get-getter-state-unq m i))))

(in-theory (disable i-get-getter-state
                    i-get-getter-state-necc))

(defrule cpf-i-resp-i-state-unq
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (i-get-getter-state m)
                (cache-index-p m i)
                (cache-index-p m j))
           (i-resp-i-state-unq (cache-process-forward m i)
                               j))
  :enable (i-resp-i-state-unq
           i-get-getter-state-unq
           cache-process-forward)
  :use ((:instance i-resp-i-state-necc (i j))
        (:instance i-get-getter-state-necc)))

(defrule cpf-i-resp-i-state
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (i-get-getter-state m)
                (cache-index-p m i))
           (i-resp-i-state (cache-process-forward m i)))
  :expand (i-resp-i-state (cache-process-forward m i)))

(defrule cpr-i-resp-i-state-unq
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j))
           (i-resp-i-state-unq (cache-process-response m i response-i)
                               j))
  :enable (i-resp-i-state-unq
           cache-process-response)
  :use ((:instance i-resp-i-state-necc)
        (:instance i-resp-i-state-necc (i j))))

(defrule cpr-i-resp-i-state
  (implies (and (vi-p m)
                (i-resp-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (i-resp-i-state (cache-process-response m i response-i)))
  :expand (i-resp-i-state (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; i-get-i-state
;; owner-state
;; req-state
;; i-get-getter-state

(define i-ack-i-state-unq
  ((m vi-p)
   (i (cache-index-p m i)))
  (b* (((vi m) m)
       ((cache cachei) (nth i m.caches))
       ((unless (consp cachei.forwards)) t)
       (fwd1 (car (last cachei.forwards))))
    (forward-case
     fwd1
     (:get
      (b* (((unless (consp (remove-last cachei.forwards))) t)
           (fwd2 (car (last (remove-last cachei.forwards)))))
        (forward-case
         fwd2
         (:put-ack (and (equal (cache-state-kind cachei.cache-state) :vi-a)
                        (endp (remove-last (remove-last cachei.forwards)))))
         (:get nil))))
     (:put-ack
      (and
       (or (equal (cache-state-kind cachei.cache-state) :vi-a)
           (equal (cache-state-kind cachei.cache-state) :ii-a))
       (endp (remove-last cachei.forwards)))))))

(defun-sk i-ack-i-state (m)
  (forall i
          (implies (and (vi-p m)
                        (cache-index-p m i))
                   (i-ack-i-state-unq m i))))

(in-theory (disable i-ack-i-state
                    i-ack-i-state-necc))

(define dir-i-i-state-unq
  ((m vi-p)
   (i (cache-index-p m i)))
  (b* (((vi m) m)
       ((dir dir) m.dir)
       ((cache cachei) (nth i m.caches)))
    (dir-state-case
     dir.dir-state
     (:i (cache-state-case
          cachei.cache-state
          (:i (and ;(endp cachei.forwards)
               (endp cachei.responses)))
          (:iv-d (and (endp cachei.responses)))
;                      (endp cachei.forwards)))
          (:v nil)
          (:vi-a (and (endp cachei.responses)))
;                      (consp cachei.forwards)
;                      (equal (forward-kind (car (last cachei.forwards)))
;                             :put-ack)
;                      (endp (remove-last cachei.forwards))))
          (:ii-a (and (endp cachei.responses)))))
;                      (consp cachei.forwards)
;                      (equal (forward-kind (car (last cachei.forwards)))
;                             :put-ack)
;                      (endp (remove-last cachei.forwards))))))
     (:v t))))

(defun-sk dir-i-i-state (m)
  (forall i
          (implies (and (vi-p m)
                        (cache-index-p m i))
                   (dir-i-i-state-unq m i))))

(in-theory (disable dir-i-i-state
                    dir-i-i-state-unq))

(defrule remove-last-cons
  (equal (remove-last (cons x xs))
         (if (consp xs)
             (cons x (remove-last xs))
           nil))
  :enable remove-last)

(defrule dpr-i-get-i-state-unq
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (req-state m)
                (i-ack-i-state m)
                (dir-i-i-state m)
                (request-index-p m req-i-idx)
                (cache-index-p m i))
           (i-get-i-state-unq (dir-process-request m req-i-idx)
                              i))
  :enable (i-get-i-state-unq
           owner-state-unq
           dir-has-data
           cache-has-data
           req-state-unq
           i-ack-i-state-unq
           dir-i-i-state-unq
           dir-process-request)
  :use ((:instance owner-state)
        (:instance dir-has-data-i-has-data-necc)
        (:instance i-get-i-state-necc)
        (:instance req-state-necc)
        (:instance i-ack-i-state-necc)
        (:instance dir-i-i-state-necc
                   (i (req-get->cache-id
                       (nth req-i-idx
                            (dir->requests
                             (vi->dir m))))))))

(defrule dpr-i-get-i-state
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (req-state m)
                (i-ack-i-state m)
                (dir-i-i-state m)
                (request-index-p m req-i-idx))
           (i-get-i-state (dir-process-request m req-i-idx)))
  :expand (i-get-i-state (dir-process-request m req-i-idx)))

(defrule cpc-i-get-i-state-unq
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (core-event-p cevent)
                (cache-index-p m i))
           (i-get-i-state-unq (cache-process-cevent m cevent)
                              i))
  :enable (i-get-i-state-unq
           owner-state-unq
           dir-has-data
           cache-has-data
           cache-process-cevent)
  :use ((:instance owner-state-necc)
        (:instance dir-has-data-i-has-data-necc)
        (:instance i-get-i-state-necc)))

(defrule cpc-i-get-i-state
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (core-event-p cevent))
           (i-get-i-state (cache-process-cevent m cevent)))
  :expand (i-get-i-state (cache-process-cevent m cevent)))

(defrule cpf-i-get-i-state-unq
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (i-ack-i-state m)
                (cache-index-p m i)
                (cache-index-p m j))
           (i-get-i-state-unq (cache-process-forward m i)
                              j))
  :enable (i-get-i-state-unq
           owner-state-unq
           dir-has-data
           cache-has-data
           i-ack-i-state-unq
           cache-process-forward)
  :use ((:instance owner-state-necc)
        (:instance dir-has-data-i-has-data-necc (i j))
        (:instance i-get-i-state-necc (i j))
        (:instance i-ack-i-state-necc)))

(defrule cpf-i-get-i-state
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (i-ack-i-state m)
                (cache-index-p m i))
           (i-get-i-state (cache-process-forward m i)))
  :expand (i-get-i-state (cache-process-forward m i)))

(defrule cpr-i-get-i-state-unq
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (i-resp-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j))
           (i-get-i-state-unq (cache-process-response m i response-i)
                              j))
  :enable (i-get-i-state-unq
           owner-state-unq
           dir-has-data
           cache-has-data
           i-resp-i-state-unq
           cache-process-response)
  :use ((:instance i-get-i-state-necc)
        (:instance owner-state-necc)
        (:instance dir-has-data-i-has-data-necc)
        (:instance i-resp-i-state-necc)
        (:instance i-has-data-j-has-data-necc)
        (:instance i-get-i-state-necc (i j))))

(defrule cpr-i-get-i-state
  (implies (and (vi-p m)
                (i-get-i-state m)
                (owner-state m)
                (one-has-data m)
                (i-resp-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (i-get-i-state (cache-process-response m i response-i)))
  :expand (i-get-i-state (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; owner-state
;; req-state
;; i-get-getter-state
;; i-ack-i-state
;; dir-i-i-state

(defrule dpr-owner-state-unq
  (implies (and (vi-p m)
                (owner-state m)
                (req-state m)
                (request-index-p m req-i-idx))
           (owner-state-unq (dir-process-request m req-i-idx)))
  :enable (owner-state-unq
           req-state-unq
           request-list-has-put-from-cache-unq
           dir-process-request)
  :use ((:instance owner-state-necc)
        (:instance req-state-necc)))

(defrule dpr-owner-state
  (implies (and (vi-p m)
                (owner-state m)
                (req-state m)
                (request-index-p m req-i-idx))
           (owner-state (dir-process-request m req-i-idx)))
  :expand (owner-state (dir-process-request m req-i-idx)))

(defrule cpc-owner-state-unq
  (implies (and (vi-p m)
                (owner-state m)
                (core-event-p cevent))
           (owner-state-unq (cache-process-cevent m cevent)))
  :enable (owner-state-unq
           cache-process-cevent)
  :use ((:instance owner-state-necc)))

(defrule cpc-owner-state
  (implies (and (vi-p m)
                (owner-state m)
                (core-event-p cevent))
           (owner-state (cache-process-cevent m cevent)))
  :expand (owner-state (cache-process-cevent m cevent)))

(defrule cpf-owner-state-unq
  (implies (and (vi-p m)
                (owner-state m)
                (one-has-data m)
                (cache-index-p m i))
           (owner-state-unq (cache-process-forward m i)))
  :enable (owner-state-unq
           dir-has-data
           cache-has-data
           cache-process-forward)
  :use ((:instance owner-state-necc)
        (:instance i-has-data-j-has-data-necc
                   (j (v-dir-state->owner-id
                       (dir->dir-state
                        (vi->dir m)))))
        (:instance dir-has-data-i-has-data-necc)))

(defrule cpf-owner-state
  (implies (and (vi-p m)
                (owner-state m)
                (one-has-data m)
                (cache-index-p m i))
           (owner-state (cache-process-forward m i)))
  :expand (owner-state (cache-process-forward m i)))

(defrule cpr-owner-state-unq
  (implies (and (vi-p m)
                (owner-state m)
                (i-resp-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (owner-state-unq (cache-process-response m i response-i)))
  :enable (owner-state-unq
           i-resp-i-state-unq
           cache-process-response)
  :use ((:instance owner-state-necc)
        (:instance i-resp-i-state-necc
                   (i (v-dir-state->owner-id
                       (dir->dir-state
                        (vi->dir m)))))))

(defrule cpr-owner-state
  (implies (and (vi-p m)
                (owner-state m)
                (i-resp-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (owner-state (cache-process-response m i response-i)))
  :expand (owner-state (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; req-state
;; i-get-getter-state
;; i-ack-i-state
;; dir-i-i-state

(defrule dpr-req-state-unq
  (implies (and (vi-p m)
                (req-state m)
                (two-reqs-same-cache m)
                (owner-state m)
                (request-index-p m req-i-idx)
                (request-index-p (dir-process-request m req-i-idx)
                                 req-j-idx))
           (req-state-unq (dir-process-request m req-i-idx)
                          req-j-idx))
  :enable (req-state-unq
           two-reqs-same-cache-unq
           owner-state-unq
           dir-process-request)
  :disable nth
  :use ((:instance req-state-necc (req-i-idx req-j-idx))
        (:instance nth-remove-nth
                   (i req-i-idx)
                   (j req-j-idx)
                   (x (dir->requests (vi->dir m))))
        (:instance two-reqs-same-cache-necc)
        (:instance two-reqs-same-cache-necc
                   (req-j-idx (1+ req-j-idx)))
        (:instance req-state-necc (req-i-idx (1+ req-j-idx)))
        (:instance owner-state-necc)))

(defrule dpr-req-state
  (implies (and (vi-p m)
                (req-state m)
                (two-reqs-same-cache m)
                (owner-state m)
                (request-index-p m req-i-idx))
           (req-state (dir-process-request m req-i-idx)))
  :expand (req-state (dir-process-request m req-i-idx)))

(defrule i-fwd-i-state
  (implies (and (vi-p m)
                (cache-index-p m i)
                (i-get-i-state m)
                (i-ack-i-state m)
                (consp (cache->forwards (nth i (vi->caches m)))))
           (not (equal (cache-state-kind (cache->cache-state
                                          (nth i (vi->caches m))))
                       :i)))
  :enable (i-get-i-state-unq
           i-ack-i-state-unq)
  :use ((:instance i-get-i-state-necc)
        (:instance i-ack-i-state-necc)))

(defrule i-resp-i-state-i
  (implies (and (vi-p m)
                (cache-index-p m i)
                (i-resp-i-state m)
                (consp (cache->responses (nth i (vi->caches m)))))
           (and (not (equal (cache-state-kind (cache->cache-state
                                               (nth i (vi->caches m))))
                            :i))
                (not (equal (cache-state-kind (cache->cache-state
                                               (nth i (vi->caches m))))
                            :v))))
  :enable (i-resp-i-state-unq)
  :use ((:instance i-resp-i-state-necc)))

;; This could still use some cleanup; takes about 50 mil proof steps (30
;; seconds in parallel).
(defrule cpc-req-state-unq
  (implies (and (vi-p m)
                (req-state m)
                (i-get-i-state m)
                (i-ack-i-state m)
                (i-resp-i-state m)
                (owner-state m)
                (core-event-p cevent)
                (request-index-p (cache-process-cevent m cevent)
                                 req-i-idx))
           (req-state-unq (cache-process-cevent m cevent)
                          req-i-idx))
  :enable (req-state-unq
           i-get-i-state-unq
           i-ack-i-state-unq
           i-resp-i-state-unq
           owner-state-unq
           cache-process-cevent)
  :use ((:instance req-state-necc)
        (:instance req-state-necc (req-i-idx (1- req-i-idx)))
        (:instance owner-state-necc)
        (:instance i-ack-i-state-necc (i (cevict->cache-id cevent)))))

(defrule cpc-req-state
  (implies (and (vi-p m)
                (req-state m)
                (i-get-i-state m)
                (i-ack-i-state m)
                (i-resp-i-state m)
                (owner-state m)
                (core-event-p cevent))
           (req-state (cache-process-cevent m cevent)))
  :expand (req-state (cache-process-cevent m cevent)))

(define dir-req-i-get-same-cache-unq
  ((m vi-p)
   (i (cache-index-p m i))
   (req-i-idx (request-index-p m req-i-idx)))
  (b* (((vi m) m)
       ((dir dir) m.dir)
       (req (nth req-i-idx dir.requests))
       ((cache cachei) (nth i m.caches))
       ((unless (consp cachei.forwards)) t)
       (fwd (car (last cachei.forwards))))
    (request-case
     req
     (:get
      (forward-case
       fwd
       (:get (not (= req.cache-id fwd.cache-id)))
       (:put-ack t)))
     (:put
      (forward-case
       fwd
       (:get (not (= req.cache-id fwd.cache-id)))
       (:put-ack t))))))

(defun-sk dir-req-i-get-same-cache (m)
  (forall (i req-i-idx)
          (implies (and (vi-p m)
                        (cache-index-p m i)
                        (request-index-p m req-i-idx))
                   (dir-req-i-get-same-cache-unq m i req-i-idx))))

(in-theory (disable dir-req-i-get-same-cache
                    dir-req-i-get-same-cache-necc))

(defrule cpf-req-state-unq
  (implies (and (vi-p m)
                (req-state m)
                (dir-req-i-get-same-cache m)
                (cache-index-p m i)
                (request-index-p (cache-process-forward m i)
                                 req-i-idx))
           (req-state-unq (cache-process-forward m i)
                          req-i-idx))
  :enable (req-state-unq
           dir-req-i-get-same-cache-unq
           cache-process-forward)
  :disable nth
  :use ((:instance req-state-necc)
        (:instance dir-req-i-get-same-cache-necc)))

(defrule cpf-req-state
  (implies (and (vi-p m)
                (req-state m)
                (dir-req-i-get-same-cache m)
                (cache-index-p m i))
           (req-state (cache-process-forward m i)))
  :expand (req-state (cache-process-forward m i)))

(defrule cpr-req-state-unq
  (implies (and (vi-p m)
                (req-state m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (request-index-p (cache-process-response m i response-i)
                                 req-i-idx))
           (req-state-unq (cache-process-response m i response-i)
                          req-i-idx))
  :enable (req-state-unq
           cache-process-response)
  :use ((:instance req-state-necc)))

(defrule cpr-req-state
  (implies (and (vi-p m)
                (req-state m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (req-state (cache-process-response m i response-i)))
  :expand (req-state (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; i-get-getter-state
;; i-ack-i-state
;; dir-i-i-state
;; dir-req-i-get-same-cache

(defrule dpr-i-get-getter-state-unq
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (dir-req-i-get-same-cache m)
                (req-state m)
                (request-index-p m req-i-idx)
                (cache-index-p m i))
           (i-get-getter-state-unq (dir-process-request m req-i-idx)
                                   i))
  :enable (i-get-getter-state-unq
           req-state-unq
           dir-req-i-get-same-cache-unq
           dir-process-request)
  :use ((:instance i-get-getter-state-necc)
        (:instance req-state-necc)
        (:instance dir-req-i-get-same-cache-necc)))

(defrule dpr-i-get-getter-state
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (dir-req-i-get-same-cache m)
                (req-state m)
                (request-index-p m req-i-idx))
           (i-get-getter-state (dir-process-request m req-i-idx)))
  :expand (i-get-getter-state (dir-process-request m req-i-idx)))

(defrule cpc-i-get-getter-state-unq
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (core-event-p cevent)
                (cache-index-p m i))
           (i-get-getter-state-unq (cache-process-cevent m cevent)
                                   i))
  :enable (i-get-getter-state-unq
           cache-process-cevent)
  :use ((:instance i-get-getter-state-necc)))

(defrule cpc-i-get-getter-state
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (core-event-p cevent))
           (i-get-getter-state (cache-process-cevent m cevent)))
  :expand (i-get-getter-state (cache-process-cevent m cevent)))

(define i-get-j-get-same-cache-unq
  ((m vi-p)
   (i (cache-index-p m i))
   (j (cache-index-p m j)))
  (b* (((vi m) m)
       ((cache cachei) (nth i m.caches))
       ((cache cachej) (nth j m.caches))
       ((when (= i j)) t)
       ((unless (consp cachei.forwards)) t)
       (fwdi (car (last cachei.forwards)))
       ((unless (consp cachej.forwards)) t)
       (fwdj (car (last cachej.forwards))))
    (forward-case
     fwdi
     (:get
      (forward-case
       fwdj
       (:get (not (= fwdi.cache-id fwdj.cache-id)))
       (& t)))
     (& t))))

(defun-sk i-get-j-get-same-cache (m)
  (forall (i j)
          (implies (and (vi-p m)
                        (cache-index-p m i)
                        (cache-index-p m j))
                   (i-get-j-get-same-cache-unq m i j))))

(in-theory (disable i-get-j-get-same-cache
                    i-get-j-get-same-cache-necc))

(defrule cpf-i-get-getter-state-unq
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (i-ack-i-state m)
                (i-get-j-get-same-cache m)
                (cache-index-p m i)
                (cache-index-p m j))
           (i-get-getter-state-unq (cache-process-forward m i)
                                   j))
  :enable (i-get-getter-state-unq
           i-ack-i-state-unq
           i-get-j-get-same-cache-unq
           cache-process-forward)
  :use ((:instance i-get-getter-state-necc (i j))
        (:instance i-ack-i-state-necc)
        (:instance i-get-j-get-same-cache-necc)))

(defrule cpf-i-get-getter-state
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (i-ack-i-state m)
                (i-get-j-get-same-cache m)
                (cache-index-p m i))
           (i-get-getter-state (cache-process-forward m i)))
  :expand (i-get-getter-state (cache-process-forward m i)))

(defrule cpr-i-get-getter-state-unq
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j))
           (i-get-getter-state-unq (cache-process-response m i response-i)
                                   j))
  :enable (i-get-getter-state-unq
           cache-process-response)
  :use ((:instance i-get-getter-state-necc)
        (:instance i-get-getter-state-necc (i j))))

(defrule cpr-i-get-getter-state
  (implies (and (vi-p m)
                (i-get-getter-state m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (i-get-getter-state (cache-process-response m i response-i)))
  :expand (i-get-getter-state (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; i-ack-i-state
;; dir-i-i-state
;; dir-req-i-get-same-cache
;; i-get-j-get-same-cache

(defrule dpr-i-ack-i-state-unq
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (req-state m)
                (owner-state m)
                (request-index-p m req-i-idx)
                (cache-index-p m i))
           (i-ack-i-state-unq (dir-process-request m req-i-idx)
                              i))
  :enable (i-ack-i-state-unq
           req-state-unq
           owner-state-unq
           dir-process-request)
  :use ((:instance i-ack-i-state-necc)
        (:instance req-state-necc)
        (:instance owner-state-necc)))

(defrule dpr-i-ack-i-state
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (req-state m)
                (owner-state m)
                (request-index-p m req-i-idx))
           (i-ack-i-state (dir-process-request m req-i-idx)))
  :expand (i-ack-i-state (dir-process-request m req-i-idx)))

(defrule cpc-i-ack-i-state-unq
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (core-event-p cevent)
                (cache-index-p m i))
           (i-ack-i-state-unq (cache-process-cevent m cevent)
                              i))
  :enable (i-ack-i-state-unq
           cache-process-cevent)
  :use ((:instance i-ack-i-state-necc)))

(defrule cpc-i-ack-i-state
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (core-event-p cevent))
           (i-ack-i-state (cache-process-cevent m cevent)))
  :expand (i-ack-i-state (cache-process-cevent m cevent)))

(defrule cpf-i-ack-i-state-unq
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (cache-index-p m i)
                (cache-index-p m j))
           (i-ack-i-state-unq (cache-process-forward m i)
                              j))
  :enable (i-ack-i-state-unq
           cache-process-forward)
  :use ((:instance i-ack-i-state-necc (i j))))

(defrule cpf-i-ack-i-state
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (cache-index-p m i))
           (i-ack-i-state (cache-process-forward m i)))
  :expand (i-ack-i-state (cache-process-forward m i)))

(defrule cpr-i-ack-i-state-unq
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j))
           (i-ack-i-state-unq (cache-process-response m i response-i)
                              j))
  :enable (i-ack-i-state-unq
           cache-process-response)
  :use ((:instance i-ack-i-state-necc)
        (:instance i-ack-i-state-necc (i j))))

(defrule cpr-i-ack-i-state
  (implies (and (vi-p m)
                (i-ack-i-state m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (i-ack-i-state (cache-process-response m i response-i)))
  :expand (i-ack-i-state (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; dir-i-i-state
;; dir-req-i-get-same-cache
;; i-get-j-get-same-cache

(defrule dpr-dir-i-i-state-unq
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (req-state m)
                (owner-state m)
                (one-has-data m)
                (i-get-i-state m)
                (i-ack-i-state m)
                (i-resp-i-state m)
                (request-index-p m req-i-idx)
                (cache-index-p m i))
           (dir-i-i-state-unq (dir-process-request m req-i-idx)
                              i))
  :enable (dir-i-i-state-unq
           req-state-unq
           owner-state-unq
           dir-has-data
           cache-has-data
           i-get-i-state-unq
           i-ack-i-state-unq
           i-resp-i-state-unq
           dir-process-request)
  :use ((:instance dir-i-i-state-necc)
        (:instance owner-state-necc)
        (:instance req-state-necc)
        (:instance dir-has-data-i-has-data-necc)
        (:instance i-get-i-state-necc)
        (:instance i-ack-i-state-necc)
        (:instance i-resp-i-state-necc)))

(defrule dpr-dir-i-i-state
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (req-state m)
                (owner-state m)
                (one-has-data m)
                (i-get-i-state m)
                (i-ack-i-state m)
                (i-resp-i-state m)
                (request-index-p m req-i-idx))
           (dir-i-i-state (dir-process-request m req-i-idx)))
  :expand  (dir-i-i-state (dir-process-request m req-i-idx)))

(defrule cpc-dir-i-i-state-unq
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (core-event-p cevent)
                (cache-index-p m i))
           (dir-i-i-state-unq (cache-process-cevent m cevent)
                              i))
  :enable (dir-i-i-state-unq
           cache-process-cevent)
  :use ((:instance dir-i-i-state-necc)))

(defrule cpc-dir-i-i-state
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (core-event-p cevent))
           (dir-i-i-state (cache-process-cevent m cevent)))
  :expand (dir-i-i-state (cache-process-cevent m cevent)))

(defrule cpf-dir-i-i-state-unq
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (one-has-data m)
                (i-ack-i-state m)
                (cache-index-p m i)
                (cache-index-p m j))
           (dir-i-i-state-unq (cache-process-forward m i)
                              j))
  :enable (dir-i-i-state-unq
           dir-has-data
           cache-has-data
           i-ack-i-state-unq
           cache-process-forward)
  :use ((:instance dir-i-i-state-necc (i j))
        (:instance dir-has-data-i-has-data-necc)
        (:instance i-ack-i-state-necc)))

(defrule cpf-dir-i-i-state
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (one-has-data m)
                (i-ack-i-state m)
                (cache-index-p m i))
           (dir-i-i-state (cache-process-forward m i)))
  :expand (dir-i-i-state (cache-process-forward m i)))

(defrule cpr-dir-i-i-state-unq
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (one-has-data m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j))
           (dir-i-i-state-unq (cache-process-response m i response-i)
                              j))
  :enable (dir-i-i-state-unq
           dir-has-data
           cache-has-data
           cache-process-response)
  :use ((:instance dir-has-data-i-has-data-necc)
        (:instance dir-has-data-i-has-data-necc (i j))
        (:instance dir-i-i-state-necc (i j))))

(defrule cpr-dir-i-i-state
  (implies (and (vi-p m)
                (dir-i-i-state m)
                (one-has-data m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (dir-i-i-state (cache-process-response m i response-i)))
  :expand  (dir-i-i-state (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; dir-req-i-get-same-cache
;; i-get-j-get-same-cache

(defrule dpr-dir-req-i-get-same-cache-unq
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (two-reqs-same-cache m)
                (request-index-p m req-i-idx)
                (cache-index-p m i)
                (request-index-p (dir-process-request m req-i-idx)
                                 req-j-idx))
           (dir-req-i-get-same-cache-unq (dir-process-request m req-i-idx)
                                         i req-j-idx))
  :enable (dir-req-i-get-same-cache-unq
           two-reqs-same-cache-unq
           dir-process-request)
  :disable nth
  :hints (("Subgoal 24"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 23"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 22"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (req-get->cache-id
                                (nth req-i-idx
                                     (dir->requests
                                      (vi->dir m)))))
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (req-get->cache-id
                                (nth req-i-idx
                                     (dir->requests
                                      (vi->dir m)))))
                            (req-i-idx req-j-idx))))
          ("Subgoal 21"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (req-get->cache-id
                                (nth req-i-idx
                                     (dir->requests
                                      (vi->dir m)))))
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (req-get->cache-id
                                (nth req-i-idx
                                     (dir->requests
                                      (vi->dir m)))))
                            (req-i-idx req-j-idx))))
          ("Subgoal 20"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 19"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 18"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (v-dir-state->owner-id
                                (dir->dir-state
                                 (vi->dir m))))
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (v-dir-state->owner-id
                                (dir->dir-state
                                 (vi->dir m))))
                            (req-i-idx req-j-idx))))
          ("Subgoal 17"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance two-reqs-same-cache-necc
                            (req-j-idx (1+ req-j-idx)))
                 (:instance two-reqs-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance two-reqs-same-cache-necc)))
          ("Subgoal 16"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 15"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 14"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 13"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 12"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (req-put->cache-id
                                (nth req-i-idx
                                     (dir->requests
                                      (vi->dir m)))))
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (req-put->cache-id
                                (nth req-i-idx
                                     (dir->requests
                                      (vi->dir m)))))
                            (req-i-idx req-j-idx))))
          ("Subgoal 10"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 9"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 8"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (v-dir-state->owner-id
                                (dir->dir-state
                                 (vi->dir m))))
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (v-dir-state->owner-id
                                (dir->dir-state
                                 (vi->dir m))))
                            (req-i-idx req-j-idx))))
          ("Subgoal 7"
           :use ((:instance nth-remove-nth
                            (i req-i-idx)
                            (j req-j-idx)
                            (x (dir->requests (vi->dir m))))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1+ req-j-idx)))
                 (:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 4"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 3"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 2"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))
          ("Subgoal 1"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx req-j-idx))))

          ))

(defrule dpr-dir-req-i-get-same-cache
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (two-reqs-same-cache m)
                (request-index-p m req-i-idx))
           (dir-req-i-get-same-cache (dir-process-request m req-i-idx)))
  :expand (dir-req-i-get-same-cache (dir-process-request m req-i-idx)))

(defrule cpc-dir-req-i-get-same-cache-unq
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (i-get-getter-state m)
                (core-event-p cevent)
                (cache-index-p m i)
                (request-index-p (cache-process-cevent m cevent)
                                 req-i-idx))
           (dir-req-i-get-same-cache-unq (cache-process-cevent m cevent)
                                         i req-i-idx))
  :enable (dir-req-i-get-same-cache-unq
           i-get-getter-state-unq
           cache-process-cevent)
  :disable nth
  :hints (("Subgoal 33"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 32"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 31"
           :use ((:instance i-get-getter-state-necc
                            (i (cload->cache-id cevent)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (cload->cache-id cevent))
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 29"
           :use ((:instance i-get-getter-state-necc)))
          ("Subgoal 28"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 27"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 26"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 25"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 24"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 21"
           :use ((:instance i-get-getter-state-necc
                            (i (cevict->cache-id cevent)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (cevict->cache-id cevent))
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 20"
           :use ((:instance i-get-getter-state-necc)))
          ("Subgoal 19"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 18"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 17"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 16"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 15"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 14"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 13"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 10"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (i (cstore->cache-id cevent)))))
          ("Subgoal 9"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 8"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 7"
           :use ((:instance i-get-getter-state-necc
                            (i (cstore->cache-id cevent)))
                 (:instance dir-req-i-get-same-cache-necc
                            (i (cstore->cache-id cevent))
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 4"
           :use ((:instance i-get-getter-state-necc)))
          ("Subgoal 3"
           :use ((:instance dir-req-i-get-same-cache-necc
                            (req-i-idx (1- req-i-idx)))))
          ("Subgoal 2"
           :use ((:instance dir-req-i-get-same-cache-necc)))
          ("Subgoal 1"
           :use ((:instance dir-req-i-get-same-cache-necc)))))

(defrule cpc-dir-req-i-get-same-cache
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (i-get-getter-state m)
                (core-event-p cevent))
           (dir-req-i-get-same-cache (cache-process-cevent m cevent)))
  :expand (dir-req-i-get-same-cache (cache-process-cevent m cevent)))

(defrule cpf-dir-req-i-get-same-cache-unq
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (i-ack-i-state m)
                (cache-index-p m i)
                (cache-index-p m j)
                (request-index-p (cache-process-forward m i)
                                 req-i-idx))
           (dir-req-i-get-same-cache-unq (cache-process-forward m i)
                                         j req-i-idx))
  :enable (dir-req-i-get-same-cache-unq
           i-ack-i-state-unq
           cache-process-forward)
  :disable nth
  :use ((:instance dir-req-i-get-same-cache-necc (i j))
        (:instance i-ack-i-state-necc)))

(defrule cpf-dir-req-i-get-same-cache
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (i-ack-i-state m)
                (cache-index-p m i))
           (dir-req-i-get-same-cache (cache-process-forward m i)))
  :expand (dir-req-i-get-same-cache (cache-process-forward m i)))

(defrule cpr-dir-req-i-get-same-cache-unq
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j)
                (request-index-p (cache-process-response m i response-i)
                                 req-i-idx))
           (dir-req-i-get-same-cache-unq
            (cache-process-response m i response-i)
            j req-i-idx))
  :enable (dir-req-i-get-same-cache-unq
           cache-process-response)
  :use ((:instance dir-req-i-get-same-cache-necc)
        (:instance dir-req-i-get-same-cache-necc (i j))))

(defrule cpr-dir-req-i-get-same-cache
  (implies (and (vi-p m)
                (dir-req-i-get-same-cache m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (dir-req-i-get-same-cache (cache-process-response m i response-i)))
  :expand (dir-req-i-get-same-cache (cache-process-response m i response-i)))

;; Okay, so what's left?
;;
;; i-get-j-get-same-cache

(defrule dpr-i-get-j-get-same-cache-unq
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (dir-req-i-get-same-cache m)
                (request-index-p m req-i-idx)
                (cache-index-p m i)
                (cache-index-p m j))
           (i-get-j-get-same-cache-unq (dir-process-request m req-i-idx)
                                       i j))
  :enable (i-get-j-get-same-cache-unq
           dir-req-i-get-same-cache-unq
           dir-process-request)
  :use ((:instance i-get-j-get-same-cache-necc)
        (:instance dir-req-i-get-same-cache-necc)
        (:instance dir-req-i-get-same-cache-necc (i j))))

(defrule dpr-i-get-j-get-same-cache
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (dir-req-i-get-same-cache m)
                (request-index-p m req-i-idx))
           (i-get-j-get-same-cache (dir-process-request m req-i-idx)))
  :expand (i-get-j-get-same-cache (dir-process-request m req-i-idx)))

(defrule cpc-i-get-j-get-same-cache-unq
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (core-event-p cevent)
                (cache-index-p m i)
                (cache-index-p m j))
           (i-get-j-get-same-cache-unq (cache-process-cevent m cevent)
                                       i j))
  :enable (i-get-j-get-same-cache-unq
           cache-process-cevent)
  :use ((:instance i-get-j-get-same-cache-necc)))

(defrule cpc-i-get-j-get-same-cache
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (core-event-p cevent))
           (i-get-j-get-same-cache (cache-process-cevent m cevent)))
  :expand (i-get-j-get-same-cache (cache-process-cevent m cevent)))

(defrule cpf-i-get-j-get-same-cache-unq
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (i-ack-i-state m)
                (cache-index-p m i)
                (cache-index-p m j)
                (cache-index-p m k))
           (i-get-j-get-same-cache-unq (cache-process-forward m i)
                                       j k))
  :enable (i-get-j-get-same-cache-unq
           cache-process-forward
           i-ack-i-state-unq)
  :use ((:instance i-get-j-get-same-cache-necc (i j) (j k))
        (:instance i-ack-i-state-necc)))

(defrule cpf-i-get-j-get-same-cache
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (i-ack-i-state m)
                (cache-index-p m i))
           (i-get-j-get-same-cache (cache-process-forward m i)))
  :expand (i-get-j-get-same-cache (cache-process-forward m i)))

(defrule cpr-i-get-j-get-same-cache-unq
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (cache-index-p m i)
                (response-index-p m i response-i)
                (cache-index-p m j)
                (cache-index-p m k))
           (i-get-j-get-same-cache-unq (cache-process-response m i response-i)
                                       j k))
  :enable (i-get-j-get-same-cache-unq
           cache-process-response)
  :use ((:instance i-get-j-get-same-cache-necc (j k))
        (:instance i-get-j-get-same-cache-necc)
        (:instance i-get-j-get-same-cache-necc (i j) (j k))))

(defrule cpr-i-get-j-get-same-cache
  (implies (and (vi-p m)
                (i-get-j-get-same-cache m)
                (cache-index-p m i)
                (response-index-p m i response-i))
           (i-get-j-get-same-cache (cache-process-response m i response-i)))
  :expand (i-get-j-get-same-cache (cache-process-response m i response-i)))

;; Okay, we're done. Now to wrap it all up.

(defun big-invariant (m)
  (and (one-has-data m)
       (two-reqs-same-cache m)
       (i-resp-i-state m)
       (i-get-i-state m)
       (owner-state m)
       (req-state m)
       (i-get-getter-state m)
       (i-ack-i-state m)
       (dir-i-i-state m)
       (dir-req-i-get-same-cache m)
       (i-get-j-get-same-cache m)))

(defrule dpr-big-invariant
  (implies (and (vi-p m)
                (big-invariant m)
                (request-index-p m request-i))
           (big-invariant (dir-process-request m request-i))))

(defrule cpc-big-invariant
  (implies (and (vi-p m)
                (big-invariant m)
                (core-event-p cevent))
           (big-invariant (cache-process-cevent m cevent))))

(defrule cpf-big-invariant
  (implies (and (vi-p m)
                (big-invariant m)
                (cache-index-p m i))
           (big-invariant (cache-process-forward m i))))

(defrule cpr-big-invariant
  (implies (and (vi-p m)
                (big-invariant m)
                (cache-index-p m i))
           (big-invariant (cache-process-forward m i))))

(define i-v-j-v-unq
  ((m vi-p)
   (i (cache-index-p m i))
   (j (cache-index-p m j)))
  (b* (((vi m) m)
       ((cache cachei) (nth i m.caches))
       ((cache cachej) (nth j m.caches)))
    (implies (and (equal (cache-state-kind cachei.cache-state) :v)
                  (not (= i j)))
             (not (equal (cache-state-kind cachej.cache-state) :v)))))

(defun-sk i-v-j-v (m)
  (forall (i j)
          (implies (and (vi-p m)
                        (cache-index-p m i)
                        (cache-index-p m j))
                   (i-v-j-v-unq m i j))))

(in-theory (disable i-v-j-v
                    i-v-j-v-necc))

(defrule big-invariant-implies-i-v-j-v-unq
  (implies (and (vi-p m)
                (big-invariant m)
                (cache-index-p m i)
                (cache-index-p m j))
           (i-v-j-v-unq m i j))
  :enable (i-v-j-v-unq
           cache-has-data)
  :use ((:instance i-has-data-j-has-data-necc)))

(defrule big-invariant-implies-i-v-j-v
  (implies (and (vi-p m)
                (big-invariant m))
           (i-v-j-v m))
  :expand (i-v-j-v m))

#|
; High-level things remaining to prove:
(defrule big-invariant-vi-step
  (implies (and (vi-p m)
                (big-invariant m)
                (m-oracle-p m oracle))
           (big-invariant (vi-step m oracle)))
  :enable vi-step
  :disable big-invariant)

(defrule golden-invariant
  (implies (and (natp num-caches)
                (integerp data)
                (oracle-p oracle))
           (i-v-j-v (vi-run (start-state num-caches data) oracle))))
|#