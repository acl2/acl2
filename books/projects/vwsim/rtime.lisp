
; rtime.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(in-package "ACL2")

; By using an abstract stobj for the time, we get a recognizer that represents
; the invariants we desire: see rtime$a.  During guard verification for
; functions, verification of stobj recognizer calls is optimized away, so we
; won't find ourselves repeatedly proving the conditions in rtime$a during
; guard verification.

; We start with our concrete stobj and the functions operating on it.

(defstobj rtime$c
  (time-list$c :initially (0))
  (hn-list$c :initially (0))
  :inline t
  :non-memoizable t)

(defun init-rtime$c (time rtime$c)

; [The following comment was previously in the definition of simulate.]
; Note: hn = the difference between the n and (n-1) time
; steps. At the first step, there was no previous value
; and thus the time step (hn) is 0.

  (declare (xargs :stobjs rtime$c
                  :guard (and (rationalp time)
                              (<= 0 time))))
  (let* ((rtime$c (update-time-list$c (list time) rtime$c)))
    (update-hn-list$c (list 0) rtime$c)))

(defun update-rtime$c (time hn rtime$c)
  (declare (xargs :stobjs rtime$c
                  :guard (and (rationalp time)
                              (rationalp hn)
                              (<= hn time))))
  (let* ((rtime$c (update-time-list$c (cons time (time-list$c rtime$c))
                                      rtime$c)))
    (update-hn-list$c (cons hn (hn-list$c rtime$c))
                      rtime$c)))

; Now define the logical functions for our abstract stobj.

(defun rtime$ap (x)
  ;; The rtime STOBJ holds 2 lists, the simulation times and
  ;; time-steps. We expect the following properties:

  ;; Both lists are rational-lists.
  ;; Both lists have at least one entry.
  (declare (xargs :guard t))
  (and (true-listp x)
       (= (length x) 2)
       (rational-listp (car x))
       (rational-listp (cadr x))
       (consp (car x))
       (consp (cadr x))
       (<= (car (cadr x))
           (car (car x)))))

(defun time-list$a (x)
  (declare (xargs :guard (rtime$ap x)))
  (car x))

(defun hn-list$a (x)
  (declare (xargs :guard (rtime$ap x)))
  (cadr x))

(defun create-rtime$a ()
  (declare (xargs :guard t))
  (list (list 0) (list 0)))

(defun init-rtime$a (time x)
; See also init-rtime$c.
  (declare (xargs :guard (and (rationalp time)
                              (<= 0 time)))
           (ignore x))
  (list (list time) (list 0)))

(defun update-rtime$a (time hn x)
  (declare (xargs :guard (and (rationalp time)
                              (rationalp hn)
                              (<= hn time)
                              (rtime$ap x))))
  (list (cons time (time-list$a x))
        (cons hn (hn-list$a x))))

(defun rtime$corr (rtime$c x)
  (declare (xargs :stobjs rtime$c))
  (and (rtime$ap x)
       (equal (time-list$c rtime$c)
              (time-list$a x))
       (equal (hn-list$c rtime$c)
              (hn-list$a x))))

(defthm create-rtime{correspondence}
        (rtime$corr (create-rtime$c)
                    (create-rtime$a))
        :rule-classes nil)

(defthm create-rtime{preserved}
        (rtime$ap (create-rtime$a))
        :rule-classes nil)

(defthm time-list{correspondence}
        (implies (and (rtime$corr rtime$c rtime)
                      (rtime$ap rtime))
                 (equal (time-list$c rtime$c)
                        (time-list$a rtime)))
        :rule-classes nil)

(defthm hn-list{correspondence}
        (implies (and (rtime$corr rtime$c rtime)
                      (rtime$ap rtime))
                 (equal (hn-list$c rtime$c)
                        (hn-list$a rtime)))
        :rule-classes nil)

(defthm init-rtime{correspondence}
        (implies (and (rtime$corr rtime$c rtime)
                      (rationalp time)
                      (<= 0 time))
                 (rtime$corr (init-rtime$c time rtime$c)
                             (init-rtime$a time rtime)))
        :rule-classes nil)

(defthm init-rtime{preserved}
        (implies (and (rtime$ap rtime)
                      (rationalp time)
                      (<= 0 time))
                 (rtime$ap (init-rtime$a time rtime)))
        :rule-classes nil)

(defthm update-rtime{correspondence}
        (implies (and (rtime$corr rtime$c rtime)
                      (rationalp time)
                      (rationalp hn)
                      (<= hn time)
                      (rtime$ap rtime))
                 (rtime$corr (update-rtime$c time hn rtime$c)
                             (update-rtime$a time hn rtime)))
        :rule-classes nil)

(defthm update-rtime{preserved}
        (implies (and (rationalp time)
                      (rationalp hn)
                      (<= hn time)
                      (rtime$ap rtime))
                 (rtime$ap (update-rtime$a time hn rtime)))
        :rule-classes nil)

(defabsstobj rtime
  :foundation rtime$c
  :recognizer (rtimep :logic rtime$ap :exec rtime$cp)
  :creator (create-rtime :logic create-rtime$a :exec create-rtime$c)
  :corr-fn rtime$corr
  :exports ((time-list :logic time-list$a :exec time-list$c)
            (hn-list :logic hn-list$a :exec hn-list$c)
            (init-rtime :logic init-rtime$a :exec init-rtime$c
                        :protect t)
            (update-rtime :logic update-rtime$a :exec update-rtime$c
                          :protect t)))
