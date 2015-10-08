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

(define num-caches ((m vi-p))
  :enabled t
  :returns (n natp)
  (b* (((vi m) m))
    (len m.caches)))

(defrule nth-caches
  (implies (and (vi-p m)
                (natp cache-id)
                (< cache-id (num-caches m)))
           (cache-p (nth cache-id (vi->caches m))))
  :enable num-caches)

(define num-dir-requests ((m vi-p))
  :enabled t
  :returns (n natp)
  (b* (((vi m) m)
       ((dir dir) m.dir))
    (len dir.requests)))

(defrule nth-dir-requests
  (implies (and (vi-p m)
                (natp request-i)
                (< request-i (num-dir-requests m)))
           (request-p (nth request-i (dir->requests (vi->dir m)))))
  :enable num-dir-requests)

(define num-forwards
  :enabled t
  ((m vi-p)
   (cache-id (and (natp cache-id)
                  (< cache-id (num-caches m)))))
  (b* (((vi m) m)
       ((cache cache) (nth cache-id m.caches)))
    (len cache.forwards)))

(define num-responses
  :enabled t
  ((m vi-p)
   (cache-id (and (natp cache-id)
                  (< cache-id (num-caches m)))))
  (b* (((vi m) m)
       ((cache cache) (nth cache-id m.caches)))
    (len cache.responses)))

(defrule num-caches-dir-process-request
  (equal (num-caches (dir-process-request m request-i))
         (num-caches m))
  :enable (dir-process-request))

(defrule num-caches-cache-process-cevent
  (equal (num-caches (cache-process-cevent m cevent))
         (num-caches m))
  :enable (cache-process-cevent))

(defrule num-caches-cache-process-forward
  (implies (and (natp cache-id)
                (< cache-id (num-caches m)))
           (equal (num-caches (cache-process-forward m cache-id))
                  (num-caches m)))
  :enable (cache-process-forward))

(defrule num-caches-cache-process-response
  (implies (and (natp cache-id)
                (< cache-id (num-caches m))
                (natp response-i)
                (< response-i (num-responses m cache-id)))
           (equal (num-caches (cache-process-response m cache-id response-i))
                  (num-caches m)))
  :enable (cache-process-response))

(define cache-index-p ((m vi-p) i)
  :enabled t
  (and (natp i)
       (< i (num-caches m))))

(define request-index-p ((m vi-p) request-i)
  :enabled t
  (and (natp request-i)
       (< request-i (num-dir-requests m))))

(define response-index-p
  :enabled t
  ((m vi-p)
   (i (cache-index-p m i))
   response-i)
  (and (natp response-i)
       (< response-i (num-responses m i))))

;; useful rules about transition functions

(defrule len-requests-dir-process-request
  (implies (and (vi-p m)
                (request-index-p m request-i))
           (<= (len (dir->requests
                     (vi->dir
                      (dir-process-request m request-i))))
               (len (dir->requests (vi->dir m)))))
  :enable dir-process-request
  :rule-classes :linear)

;; misc

(defrule nth-implies-<-len
  (implies (and (natp i)
                (nth i x))
           (< i (len x))))

(defrule nth-cons
  (equal (nth i (cons x y))
         (if (zp i) x (nth (1- i) y))))

;; start state

(define start-caches ((num-caches natp))
  :returns (caches cache-list-p)
  (if (zp num-caches) nil
    (cons (cache (i-state) nil nil)
          (start-caches (1- num-caches)))))

(define start-state ((num-caches natp)
                     (data integerp))
  :returns (m vi-p)
  (vi (start-caches num-caches)
      (dir (i-dir-state data) nil)))

;; oracle
;; Stimulus and step function
(fty::deftagsum stimulus
  (:dir-req ((req-idx natp)) :base-name stim-dir-req)
  (:cache-cevent ((cevent core-event-p)) :base-name stim-cache-cevent)
  (:cache-forward ((cache-id natp)) :base-name stim-cache-forward)
  (:cache-response ((cache-id natp) (resp-idx natp)) :base-name
                   stim-cache-response))

(define m-stimulus-p ((m vi-p) (stim stimulus-p))
  (stimulus-case
   stim
   (:dir-req (request-index-p m stim.req-idx))
   (:cache-cevent
    (core-event-case
     stim.cevent
     (:cload  (cache-index-p m stim.cevent.cache-id))
     (:cstore (cache-index-p m stim.cevent.cache-id))
     (:cevict (cache-index-p m stim.cevent.cache-id))))
   (:cache-forward (cache-index-p m stim.cache-id))
   (:cache-response (and (cache-index-p m stim.cache-id)
                         (response-index-p m stim.cache-id stim.resp-idx)))))


(fty::deflist oracle :elt-type stimulus :true-listp t)

(define vi-step
  ((m vi-p)
   (stim stimulus-p))
  :returns (m-prime vi-p :hyp :fguard)
  (stimulus-case
   stim
   (:dir-req
    (dir-process-request m stim.req-idx))
   (:cache-cevent
    (cache-process-cevent m stim.cevent))
   (:cache-forward
    (cache-process-forward m stim.cache-id))
   (:cache-response
    (cache-process-response m stim.cache-id stim.resp-idx))))

(define m-oracle-p ((m vi-p) (oracle oracle-p))
  (if (endp oracle)
      t
    (and (m-stimulus-p m (car oracle))
         (m-oracle-p (vi-step m (car oracle))
                     (cdr oracle))))
  :measure (acl2-count oracle))

(defrule m-oracle-p-vi-step
  (implies (and (m-oracle-p m oracle)
                (consp oracle))
           (m-oracle-p (vi-step m (car oracle))
                       (cdr oracle)))
  :enable m-oracle-p)

(define vi-run
  ((m vi-p)
   (oracle oracle-p))
  :returns (m-prime vi-p :hyp :fguard)
  (if (endp oracle)
      m
    (vi-run (vi-step m (car oracle))
            (cdr oracle))))
