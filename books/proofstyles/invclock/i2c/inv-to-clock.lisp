(in-package "ACL2")

#|

 clock-to-inv.lisp
 ~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Tue Jan 22 17:33:20 2004

In this book, we define a macro called inv-to-clock to convert from inductive
invariant style proofs to clock function style proofs. Both total and partial
correctness are concerned. The macro functionally instantiates the generic
theorems about clocks and invariants to produce the final theorems.

|#

(set-match-free-default :once)

;; Compatibility stuff.
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)


;; (defun natp (n)
;;   (and (integerp n)
;;        (<= 0 n)))

(in-theory (disable natp))

;; The macro clock-to-inv below works exactly as you would expect, functionally
;; instantiating the generic functions to get the concrete theorems.

(defmacro inv-to-clock (name mode &key
                             (pre 'pre)
                             (next 'next)
                             (external 'external)
                             (post 'post)
                             (inv 'inv)
                             (m 'm))
  (declare (xargs :guard (and (symbolp name)
                              (keywordp mode)
                              (symbolp next)
                              (symbolp pre)
                              (symbolp post)
                              (symbolp inv)
                              (symbolp m))))


  ;; We create the invariant as name-inv, and create the concrete theorems as
  ;; name-thm for the corresponding abstract theorem. The user needs to check
  ;; that there are no name clashes.

  (let ((next next)
        (pre pre)
        (post post)
        (inv inv)
        (m m)
        (clock (packn (list name '-clock))))

    (if (eq mode :total)

        ;; the theorems for total functions.

        (let* ((run (packn (list name '-run)))
               (standard-1 (packn (list name '-standard-theorem-about-clocks-1)))
               (standard-2 (packn (list name '-standard-theorem-about-clocks-2)))
               (standard-3 (packn (list name '-standard-theorem-about-clocks-3)))
               (clock-natp (packn (list name '-clock-is-natp))))

        `(encapsulate

          (((,clock *) => *))

          ;; Just throw in the book and do it.

          (local (include-book "i2c-total"))

          ;; I should not be required to open next, pre, post, etc.
          (in-theory (disable ,next ,pre, post ,inv))

          (defun ,run (s n)
            (if (zp n) s
              (,run (,next s) (1- n))))

          (local
           (defun clock-aux (s)
              (declare (xargs :measure (,m s)))
              (cond ((not (,inv s)) 0)
                    ((,external (,next s)) 0)
                    (t (1+ (clock-aux (,next s)))))))

          (local
           (defun ,clock (s)
             (1+ (clock-aux s))))

          (defthm ,clock-natp
            (natp (,clock s))
            :hints (("Goal"
                     :in-theory (disable clock-total--fn-is-natp)
                     :use ((:functional-instance
                            clock-total--fn-is-natp
                            (inv-total ,inv)
                            (pre-total ,pre)
                            (next-total ,next)
                            (external-total ,external)
                            (run-total ,run)
                            (post-total ,post)
                            (clock-total--fn ,clock)
                            (clock-total--fn-aux clock-aux)
                            (m ,m))))))


      (defthm ,standard-1
        (implies (,pre s)
                 (,external (,run s (,clock s))))
        :hints (("Goal"
                 :in-theory (disable  standard-theorem-about-clock-total-s-1)
                 :use ((:functional-instance
                         standard-theorem-about-clock-total-s-1
                        (inv-total ,inv)
                        (pre-total ,pre)
                        (next-total ,next)
                        (external-total ,external)
                        (run-total ,run)
                        (post-total ,post)
                        (clock-total--fn ,clock)
                        (clock-total--fn-aux clock-aux)
                        (m ,m))))))


      (defthm ,standard-2
        (implies (,pre s)
                 (,post (,run s (,clock s))))
        :hints (("Goal"
                 :in-theory (disable  standard-theorem-about-clock-total-s-2)
                 :use ((:functional-instance
                         standard-theorem-about-clock-total-s-2
                        (inv-total ,inv)
                        (pre-total ,pre)
                        (next-total ,next)
                        (external-total ,external)
                        (run-total ,run)
                        (post-total ,post)
                        (clock-total--fn ,clock)
                        (clock-total--fn-aux clock-aux)
                        (m ,m))))))


      (defthm ,standard-3
        (implies (and (,pre s)
                      (,external (,run s i)))
                 (<= (,clock s) i))
        :hints (("Goal"
                 :in-theory (disable  standard-theorem-about-clock-total-s-3)
                 :use ((:functional-instance
                         standard-theorem-about-clock-total-s-3
                        (inv-total ,inv)
                        (pre-total ,pre)
                        (next-total ,next)
                        (external-total ,external)
                        (run-total ,run)
                        (post-total ,post)
                        (clock-total--fn ,clock)
                        (clock-total--fn-aux clock-aux)
                        (m ,m))))))))

      ;; Not total. So use the partial conditions and also prove fewer
      ;; theorems.

      (let* ((run (packn (list name '-run)))
             (standard-1 (packn (list name '-standard-theorem-about-clocks-1)))
             (standard-2 (packn (list name '-standard-theorem-about-clocks-2)))
             (standard-3 (packn (list name '-standard-theorem-about-clocks-3)))
             (clock-natp (packn (list name '-clock-is-natp))))

        `(encapsulate

          (((,clock *) => *))

          (local (include-book "i2c-partial"))

          (in-theory (disable ,next ,pre ,post ,inv))

          (defun ,run (s n)
            (if (zp n) s
              (,run (,next s) (1- n))))

          (local
           (defun-sk for-all-inv (s i)
             (forall j
                     (implies (<= j i)
                              (,inv (,run s j))))))
           (local
            (defun-sk exists-run-to-external (s)
              (exists i (and (natp i)
                             (for-all-inv s i)
                             (,inv (,run s i))
                             (,external (,next (,run s i)))))))

            (local
             (defun ,clock (s)
               (if (exists-run-to-external s)
                   (1+ (exists-run-to-external-witness s))
                 0)))

            (local
             (defthm inv-witness-1
               (implies (and (for-all-inv s i)
                             (<= j i))
                        (,inv (,run s j)))
               :hints (("Goal"
                        :in-theory (disable for-all-inv-necc)
                        :use ((:instance for-all-inv-necc))))))

            (local
             (in-theory (disable for-all-inv-necc)))

          (defthm ,clock-natp
            (natp (,clock s))
            :otf-flg t
            :hints (("Goal"
                     :in-theory (disable clock-partial--is-a-natp)
                     :use ((:functional-instance
                            clock-partial--is-a-natp
                            (inv-partial ,inv)
                            (pre-partial ,pre)
                            (next-partial ,next)
                            (external-partial ,external)
                            (run-partial ,run)
                            (post-partial ,post)
                            (clock-partial--fn ,clock)
                            (exists-run-partial-to-external-partial
                             exists-run-to-external)
                            (exists-run-partial-to-external-partial-witness
                             exists-run-to-external-witness)
                            (for-all-inv-partial for-all-inv)
                            (for-all-inv-partial-witness
                             for-all-inv-witness))))))

          (defthm ,standard-1
            (implies (and (,pre s)
                          (,external (,run s i)))
                     (,external (,run s (,clock s))))
            :hints (("Goal"
                     :in-theory (disable  standard-theorem-for-clock-partial-s-1)
                     :use ((:functional-instance
                            standard-theorem-for-clock-partial-s-1
                           (inv-partial ,inv)
                            (pre-partial ,pre)
                            (next-partial ,next)
                            (external-partial ,external)
                            (run-partial ,run)
                            (post-partial ,post)
                            (clock-partial--fn ,clock)
                            (exists-run-partial-to-external-partial
                             exists-run-to-external)
                            (exists-run-partial-to-external-partial-witness
                             exists-run-to-external-witness)
                            (for-all-inv-partial for-all-inv)
                            (for-all-inv-partial-witness
                             for-all-inv-witness))))))


          (defthm ,standard-2
            (implies (and (,pre s)
                          (,external (,run s i)))
                     (,post (,run s (,clock s))))
            :hints (("Goal"
                     :in-theory (disable  standard-theorem-for-clock-partial-s-2)
                     :use ((:functional-instance
                            standard-theorem-for-clock-partial-s-2
                            (inv-partial ,inv)
                            (pre-partial ,pre)
                            (next-partial ,next)
                            (external-partial ,external)
                            (run-partial ,run)
                            (post-partial ,post)
                            (clock-partial--fn ,clock)
                            (exists-run-partial-to-external-partial
                             exists-run-to-external)
                            (exists-run-partial-to-external-partial-witness
                             exists-run-to-external-witness)
                            (for-all-inv-partial for-all-inv)
                            (for-all-inv-partial-witness
                             for-all-inv-witness))))))

          (defthm ,standard-3
            (implies (and (,pre s)
                          (,external (,run s i)))
                     (<= (,clock s) i))
            :hints (("Goal"
                     :in-theory (disable  standard-theorem-for-clock-partial-s-3)
                     :use ((:functional-instance
                            standard-theorem-for-clock-partial-s-3
                            (inv-partial ,inv)
                            (pre-partial ,pre)
                            (next-partial ,next)
                            (external-partial ,external)
                            (run-partial ,run)
                            (post-partial ,post)
                            (clock-partial--fn ,clock)
                            (exists-run-partial-to-external-partial
                             exists-run-to-external)
                            (exists-run-partial-to-external-partial-witness
                             exists-run-to-external-witness)
                            (for-all-inv-partial for-all-inv)
                            (for-all-inv-partial-witness
                             for-all-inv-witness)))))))))))



;; Testing:

;; Example 1: Total correctness

(local
 (encapsulate
  ()

  (local (defun nextt (s) s))
  (local (defun pret (s)(declare (ignore s)) nil))
  (local (defun postt (s) (declare (ignore s)) t))
  (local(defun externalt (s) (declare (ignore s)) t))
  (local (defun invt (s) (declare (ignore s)) nil))
  (local (defun meas (s) (declare (ignore s)) 0))

  (local
   (defthm pre-has-inv
     (implies (pret s)
              (invt s))))

  (local
   (defthm inv-persists
     (implies (and (invt s)
                 (not (externalt (nextt s))))
              (invt (nextt s)))))

  (local
   (defthm inv-implies-post
     (implies (and (invt s)
                   (externalt (nextt s)))
              (postt (nextt s)))))

  (local
   (defthm m-ordinal
     (e0-ordinalp (meas s))))


  (local
   (defthm m-decreases
     (implies (and (invt s)
                   (not (externalt (nextt s))))
              (e0-ord-< (meas (nextt s))
                        (meas s)))))

  (local
   (defthm inv-not-external
     (implies (invt s)
              (not (externalt s)))))
  (local
   (inv-to-clock try-total
                 :total
                 :pre pret
                 :next nextt
                 :external externalt
                 :post postt
                 :inv invt
                 :m meas))))



;; Example 2: Partial correctness

(local
 (encapsulate
  ()
  (local (defun nextp (s) s))
  (local (defun prep (s) (declare (ignore s)) nil))
  (local (defun postp (s) (declare (ignore s)) t))
  (local (defun externalp (s) (declare (ignore s)) nil))
  (local (defun invp (s) (declare (ignore s)) nil))


 (local
  (defthm  pre-has-inv
    (implies (prep s)
             (invp s))))

 (local
  (defthm inv-not-external
    (implies (invp s)
             (not (externalp s)))))

 (local
  (defthm inv-persists
    (implies (and (invp s)
                  (not (externalp (nextp s))))
             (invp (nextp s)))))

 (local
  (defthm inv-implies-post
    (implies (and (invp s)
                  (externalp (nextp s)))
             (postp (nextp s)))))

 (local
  (inv-to-clock try-partial
                :partial
                :pre prep
                :next nextp
                :external externalp
                :post postp
                :inv invp))))


;; Notice that to use the macro one might need to disable the bodies of the
;; functions next, pre, post etc. So some theory creation is important. I dont
;; do that since for all I know the body might have been stubbed out. But you
;; are pretty safe in a theory that keeps only the theorems specified as axioms.



