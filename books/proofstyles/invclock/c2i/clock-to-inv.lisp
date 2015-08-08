(in-package "ACL2")

#|

 clock-to-inv.lisp
 ~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Tue Jan 20 17:33:20 2004

In this book, we define a macro called clock-to-inv to convert from clock
function style proofs to inductive invariant style proofs. Both total and
partial correctness are concerned. The macro functionally instantiates the
generic theorems about clocks and invariants to produce the final theorems.

|#

(set-match-free-default :once)

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

;; (defun natp (n)
;;   (and (integerp n)
;;        (<= 0 n)))

(in-theory (disable natp))

;; The macro clock-to-inv below works exactly as you would expect, functionally
;; instantiating the generic functions to get the concrete theorems.

(defmacro clock-to-inv (name mode &key
                             (pre 'pre)
                             (next 'next)
                             (run 'run)
                             (external 'external)
                             (post 'post)
                             (clock 'clock))
  (declare (xargs :guard (and (symbolp name)
                              (keywordp mode)
                              (symbolp next)
                              (symbolp run)
                              (symbolp pre)
                              (symbolp post)
                              (symbolp clock))))


  ;; We create the invariant as name-inv, and create the concrete theorems as
  ;; name-thm for the corresponding abstract theorem. The user needs to check
  ;; that there are no name clashes.

  (let ((next next)
        (pre pre)
        (post post)
        (clock clock)
        (inv (packn (list name '-inv)))
        (m (packn (list name '-m))))

    (if (eq mode :total)

        ;; the theorems for total functions.

        (let* ((m-is-ordinal (packn (list name '-m-is-ordinal)))
               (m-decreases (packn (list name '-m-decreases)))
               (pre-has-inv (packn (list name '-pre-has-inv)))
               (inv-persists (packn (list name '-inv-persists)))
               (inv-and-external-implies-post
                (packn (list name '-inv-and-external-implies-post))))

        `(encapsulate

          (((,inv *) => *)
           ((,m *) => *))

          (local (include-book "c2i-total"))

          (local
           (defun-sk exists-pre-state (s)
             (exists (init i)
                     (and (,pre init)
                          (natp i)
                          (< i (,clock init))
                          (equal s (,run init i))))))

          (local (in-theory (disable mv-nth)))

          (local
           (defun ,inv (s)
             (and (exists-pre-state s)
                  (not (,external s)))))

          (local
           (defun find-external (s n)
             (declare (xargs :measure (nfix n)))
             (if (or (zp n) (,external s)) 0
               (1+ (find-external (,next s) (1- n))))))


          (local
           (defun ,m (s)
             (mv-let (p i)
                     (exists-pre-state-witness s)
                     (find-external s (- (,clock p) i)))))


          (local
           (defthm m-expands
             (equal (,m s)
                    (find-external
                     s
                     (- (,clock
                         (mv-nth
                          0
                          (exists-pre-state-witness s)))
                        (mv-nth 1 (exists-pre-state-witness s)))))))

          (local (in-theory (disable ,m)))

          ;; I dont need them any more.
          (local (in-theory (disable ,next ,pre ,post ,clock)))

          (defthm ,pre-has-inv
            (implies (,pre s)
                     (,inv s))
            :otf-flg t
            :hints (("Goal"
                     :in-theory (disable total-pre-has-total-inv)
                     :use ((:functional-instance
                            total-pre-has-total-inv
                            (total-pre ,pre)
                            (total-next ,next)
                            (total-run ,run)
                            (total-post ,post)
                            (total-clock-fn ,clock)
                            (total-inv ,inv)
                            (m ,m)
                            (total-external ,external)
                            (exists-total-pre-state-witness
                             exists-pre-state-witness)
                            (exists-total-pre-state exists-pre-state)
                            (find-total-external find-external))))))



           (defthm ,inv-persists
             (implies (and (,inv s)
                           (not (,external (,next s))))
                      (,inv (,next s)))
             :hints (("Goal"
                      :in-theory
                      (disable total-inv-implies-total-next-total-inv)
                       :use ((:functional-instance
                              total-inv-implies-total-next-total-inv
                              (total-pre ,pre)
                              (total-next ,next)
                              (total-run ,run)
                              (total-post ,post)
                              (total-clock-fn ,clock)
                              (total-inv ,inv)
                              (m ,m)
                              (total-external ,external)
                              (exists-total-pre-state-witness
                               exists-pre-state-witness)
                              (exists-total-pre-state exists-pre-state)
                              (find-total-external find-external))))))



          (defthm ,inv-and-external-implies-post
            (implies (and (,inv s)
                          (,external (,next s)))
                     (,post (,next s)))
             :hints (("Goal"
                      :in-theory
                      (disable total-inv-and-total-external-implies-total-post)
                     :use ((:functional-instance
                            total-inv-and-total-external-implies-total-post
                            (total-pre ,pre)
                            (total-next ,next)
                            (total-run ,run)
                            (total-post ,post)
                            (total-clock-fn ,clock)
                            (total-inv ,inv)
                            (m ,m)
                            (total-external ,external)
                            (exists-total-pre-state-witness exists-pre-state-witness)
                            (exists-total-pre-state exists-pre-state)
                            (find-total-external find-external))))))

          (defthm ,m-is-ordinal
            (e0-ordinalp (,m s))
            :otf-flg t
            :hints (("Goal"
                     :in-theory (disable m-is-an-ordinal)
                     :use ((:functional-instance
                            m-is-an-ordinal
                            (total-pre ,pre)
                            (total-next ,next)
                            (total-run ,run)
                            (total-post ,post)
                            (total-clock-fn ,clock)
                            (total-inv ,inv)
                            (m ,m)
                            (total-external ,external)
                            (exists-total-pre-state-witness
                             exists-pre-state-witness)
                            (exists-total-pre-state exists-pre-state)
                            (find-total-external find-external))))))


          (defthm ,m-decreases
            (implies (and (,inv s)
                          (not (,external (,next s))))
                     (e0-ord-< (,m (,next s))
                               (,m s)))
            :hints (("Goal"
                     :in-theory (disable exists-pre-state
                                         internal-steps-decrease-m)
                     :use ((:functional-instance
                            internal-steps-decrease-m
                            (total-pre ,pre)
                            (total-next ,next)
                            (total-run ,run)
                            (total-post ,post)
                            (total-clock-fn ,clock)
                            (total-inv ,inv)
                            (m ,m)
                            (total-external ,external)
                            (exists-total-pre-state-witness
                             exists-pre-state-witness)
                            (exists-total-pre-state exists-pre-state)
                            (find-total-external find-external))))))))

      ;; Not total. So use the partial conditions and also prove fewer
      ;; theorems.

             (let* ((pre-has-inv (packn (list name '-pre-has-inv)))
                    (inv-persists (packn (list name '-inv-persists)))
                    (inv-and-external-implies-post
                     (packn (list name '-inv-and-external-implies-post))))

               `(encapsulate

                 (((,inv *) => *))

                  (local (include-book "c2i-partial"))

                  (local
                   (defun-sk exists-pre-state (s)
                     (exists (init i)
                             (and (,pre init)
                                  (natp i)
                                  (< i (,clock init))
                                  (equal s (,run init i))))))

                  (local
                   (defun-sk no-external-run (s)
                     (forall i (not (,external (,run s i))))))

                  (local
                   (defthm no-external-run-expanded
                     (implies (,external (,run s i))
                              (,external (,run s (no-external-run-witness s))))
                     :hints (("Goal"
                              :in-theory (disable no-external-run-necc)
                              :use ((:instance no-external-run-necc))))))

                   (local (in-theory (disable mv-nth)))

                   (local
                    (defun ,inv (s)
                      (if (no-external-run s) T
                        (and (exists-pre-state s)
                             (not (,external s))))))

                   (local (in-theory (disable ,pre ,inv
                                              ,clock ,post)))

                   (defthm ,pre-has-inv
                     (implies (,pre s)
                              (,inv s))
                     :hints (("Goal"
                              :in-theory (disable partial-pre-has-partial-inv)
                              :use ((:functional-instance
                                     partial-pre-has-partial-inv
                                     (partial-pre ,pre)
                                     (partial-next ,next)
                                     (partial-run ,run)
                                     (partial-post ,post)
                                     (partial-clock-fn ,clock)
                                     (partial-inv ,inv)
                                     (partial-external ,external)
                                     (exists-partial-pre-state-witness
                                      exists-pre-state-witness)
                                     (exists-partial-pre-state exists-pre-state)
                                     (no-partial-external-partial-run
                                      no-external-run)
                                     (no-partial-external-partial-run-witness
                                      no-external-run-witness))))))



                   (defthm ,inv-persists
                     (implies (and (,inv s)
                                   (not (,external (,next s))))
                              (,inv (,next s)))
                     :hints (("Goal"
                              :in-theory
                              (disable
                               partial-inv-implies-partial-next-partial-inv)
                              :use ((:functional-instance
                                     partial-inv-implies-partial-next-partial-inv
                                     (partial-pre ,pre)
                                     (partial-next ,next)
                                     (partial-run ,run)
                                     (partial-post ,post)
                                     (partial-clock-fn ,clock)
                                     (partial-inv ,inv)
                                     (partial-external ,external)
                                     (exists-partial-pre-state-witness
                                      exists-pre-state-witness)
                                     (exists-partial-pre-state exists-pre-state)
                                     (no-partial-external-partial-run
                                      no-external-run)
                                     (no-partial-external-partial-run-witness
                                      no-external-run-witness))))))



                   (defthm ,inv-and-external-implies-post
                     (implies (and (,inv s)
                                   (,external (,next s)))
                              (,post (,next s)))
                     :hints
                     (("Goal"
                       :in-theory
                       (disable
                        partial-inv-and-partial-external-implies-partial-post)
                       :use ((:functional-instance
                              partial-inv-and-partial-external-implies-partial-post
                              (partial-pre ,pre)
                              (partial-next ,next)
                              (partial-run ,run)
                              (partial-post ,post)
                              (partial-clock-fn ,clock)
                              (partial-inv ,inv)
                              (partial-external ,external)
                              (exists-partial-pre-state-witness
                               exists-pre-state-witness)
                              (exists-partial-pre-state exists-pre-state)
                              (no-partial-external-partial-run no-external-run)
                              (no-partial-external-partial-run-witness
                               no-external-run-witness)))))))))))


;; Testing:

;; Example 1: Total correctness

(local
 (encapsulate
  ()

  (local (defun nextt (s) s))
  (local (defun pret (s) (declare (ignore s)) nil))
  (local (defun postt (s) (declare (ignore s)) nil))
  (local (defun externalt (s) (declare (ignore s)) nil))
  (defun clkt (s) (declare (ignore s)) 0)

  (local
   (defun runt (s n)
     (if (zp n) s (runt (nextt s) (1- n)))))

  (local
   (defthm standard-theorem-1
     (implies (pret s)
              (externalt (runt s (clkt s))))))

  (local
   (defthm standard-theorem-2
     (implies (pret s)
              (postt (runt s (clkt s))))))

  (local
   (defthm pre-not-external
     (implies (pret s)
              (not (externalt s)))))

  (local
   (defthm natp-true
     (natp (clkt s))))

  (local
   (defthm standard-thm-3
     (implies (and (pret s)
                   (externalt (runt s n)))
              (<= (clkt s) n))))


  (local
   (clock-to-inv try-total
                 :total
                 :pre pret
                 :next nextt
                 :external externalt
                 :post postt
                 :run runt
                 :clock clkt))))



;; Exampl2 2: Partial correctness

(set-match-free-default :all)

(local
 (encapsulate
  ()

  (local (defun nextp (s) s))
  (local (defun prep (s) (declare (ignore s)) nil))
  (local (defun postp (s) (declare (ignore s)) nil))
  (local (defun externalp (s) (declare (ignore s)) nil))
  (local (defun clkp (s) (declare (ignore s)) 0))

  (local
   (defun runp (s n)
     (if (zp n) s (runp (nextp s) (1- n)))))

  (local
   (defthm standard-theorem-1p
     (implies (and (prep s)
                   (externalp (runp s i)))
              (externalp (runp s (clkp s))))))

  (local
   (defthm standard-theorem-2p
     (implies (and (prep s)
                   (externalp (runp s i)))
              (postp (runp s (clkp s))))))

  (local
   (defthm pre-not-externalp
     (implies (prep s)
              (not (externalp s)))))

  (local
   (defthm natp-truep
     (natp (clkp s))))

  (local
   (defthm standard-thm-3p
     (implies (and (prep s)
                   (externalp (runp s n)))
              (<= (clkp s) n))))

  (local
   (clock-to-inv try-partial
                 :partial
                 :pre prep
                 :next nextp
                 :external externalp
                 :post postp
                 :run runp
                 :clock clkp))))
