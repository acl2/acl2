#|$ACL2s-Preamble$;
;; Amr Helmy
;; Generic departure control of GeNoC

;;31st october 2007
;; File: GeNoC-departure.lisp
;; Octobre 2nd, 2007
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "GeNoC-nodeset")
(include-book "GeNoC-misc") ;; imports also GeNoC-types
(include-book "GeNoC-ntkstate");



(defspec GenericR4d
  ;;this is the module of the network access control
  ;;the function has 4 inputs:
  ;; 1) the list of messages to be tested
  ;; 2) the first accumulator for delayed messages
  ;; 3) the second accumulator for departing messages
  ;; 4) the condition to use for the test (by default it's time, but
  ;; it can be used along something else)
  (((readyfordeparture * * * *) => (mv * *)))


  (local
   (defun readyfordeparture (missives delayed departing time)
     (declare (ignore delayed departing))
     (let ((mundertest (car missives)))
       (mv
        ;; TrLst updated
        (if  (< time (TimeTm mundertest))
            ;;it's finished and we send back the missives
            missives
          nil)
        ;; arrived messages
        (if (< time (TimeTm mundertest))
            ;; no one has the clearance to depart.
            nil
          missives)))))
  ;; the first two theorems prove simply that if we pass no messages to
  ;; the function it will return an empty list for te two return values
  (defthm nil-r4d-nil-mv0
    (not (mv-nth 0 (readyfordeparture nil nil nil time))))

  (defthm nil-r4d-nil-mv1
    (not (mv-nth 1 (readyfordeparture nil nil nil time))))
  ;; The next theorem prove that the type of the FIRST return value of the
  ;; function is a Tmissives
  (defthm tmissivesp-ready-4-departure-mv-0
    (implies (tmissivesp m nodeset)
             (tmissivesp (mv-nth 0 (readyfordeparture m nil nil time))
                         nodeset)))
  ;; The next theorem prove that the type of the SECOND return value of the
  ;; function is a Tmissives
  (defthm tmissivesp-ready-4-departure-mv-1
    (implies (tmissivesp m nodeset)
             (tmissivesp (mv-nth 1 (readyfordeparture m nil nil time))
                         nodeset)))

  ;; The Identifiers of the first list (delayed) is a subset of the
  ;; identifiers of messages passed to the function as input
  (defthm subset-ready-for-departure
    (implies (tmissivesp m nodeset)
             (subsetp (tm-ids (mv-nth 0 (readyfordeparture m  nil nil
                                                           time)))
                      (tm-ids m))))
  ;; The Identifiers of the second list (departing) is a subset of the
  ;; identifiers of messages passed to the function as input
  (defthm subset-ready-for-departure-2
    (implies (tmissivesp m nodeset)
             (subsetp (tm-ids (mv-nth 1 (readyfordeparture m nil nil
                                                           time)))
                      (tm-ids m))))
  ;; The elements second list (departing) is a subset of the
  ;; messages passed to the function as input
  (defthm subset-ready-for-departure-3
    (implies (tmissivesp m nodeset)
             (subsetp  (mv-nth 1 (readyfordeparture m nil nil time))
                       m)))
  ;; The elements First list (deLAYED) is a subset of the
  ;; messages passed to the function as input
  (defthm subset-ready-for-departure-4
    (implies (tmissivesp m nodeset)
             (subsetp  (mv-nth 0 (readyfordeparture m nil nil time))
                       m)))
  ;; The IDENTIFIERS of the first output list are distinct of those of
  ;; the second (the next two theorem prove the same thing but it is
  ;; needed in both forms)
  (defthm not-in-1-0-ready-for-dept
    (implies (tmissivesp m nodeset)
             (not-in (tm-ids (mv-nth 1 (readyfordeparture m nil nil time)))
                     (tm-ids (mv-nth 0 (readyfordeparture m nil nil time))))))

  (defthm not-in-1-0-ready-for-dept-reverse
    (implies (tmissivesp m nodeset)
             (not-in (tm-ids (mv-nth 0 (readyfordeparture m nil nil time)))
                     (tm-ids (mv-nth 1 (readyfordeparture m nil nil
                                                          time))))))

  );;end of encapsulate
