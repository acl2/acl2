(in-package "ACL2S-HOOKS")

(include-book "canonical-print")
(include-book "categorize-input")

(include-book "hacking/hacker" :dir :system)
(include-book "hacking/defcode" :dir :system :ttags ((defcode)))
(include-book "hacking/redefun" :dir :system)
(include-book "hacking/rewrite-code" :dir :system)

(program)
(set-state-ok t)

(defconst *debug-super-history* nil)


;; SUPER-HISTORY STUFF

(defun super-history-activep (state)
  (and (boundp-global 'super-history state)
       (boundp-global 'super-history-reverted state)
       (boundp-global 'super-history-globals state)
       (boundp-global 'super-history-match-globals state)
       (consp (@ super-history))))


(defun put-trace-specs (trace-specs state)
  (let ((old-trace-specs (@ trace-specs)))
    (if (equal old-trace-specs trace-specs)
      state
      (mv-let (erp val state)
              (er-progn
               (untrace$-fn nil state)
               (trace$-lst trace-specs 'put-trace-specs state))
              (declare (ignore erp val))
              state))))


; unsafe stuff
(defttag :acl2s-super-history)

(progn+touchable :vars :all
  (defun put-globals (vars vals state)
    (if (endp vars)
         state
         (pprogn
          (f-put-global (car vars) (car vals) state)
          (put-globals (cdr vars) (cdr vals) state)))))

(progn+touchable :vars :all
  (defun restore-globals (vars vals state)
    (if (endp vars)
         state
         (pprogn
          (let ((var (car vars))
                (val (car vals)))
            (cond ((eq var 'trace-specs)
                   (put-trace-specs val state))
                  (t
                   (f-put-global var val state))))
          (restore-globals (cdr vars) (cdr vals) state)))))

(progn+touchable :fns set-w!
  (defun restore-current-super-history (state)
    (if (not (super-history-activep state))
      state
      (let* ((cur (car (@ super-history))))
        (pprogn
         (restore-globals (@ super-history-globals) (cdr cur) state)
         (set-w! (car cur) state))))))

(defttag nil)
; we're done with unsafe stuff for now, except for use of put-globals
; note that the ttag is used later as well!


(defun get-globals (vars state)
  (if (endp vars)
    nil
    (cons (f-get-global (car vars) state)
          (get-globals (cdr vars) state))))

(defun cmp-globals (vars vals state)
  (or (endp vars)
      (and (if (equal (car vals)
                      (f-get-global (car vars) state))
             t
             (if *debug-super-history*
               (cw "~%Super history: ~x0: ~x1 -> ~x2~%~%"
                   (car vars) (car vals)
                   (f-get-global (car vars) state))
               nil))
           (cmp-globals (cdr vars) (cdr vals) state))))

(defun unbound-globals (vars state)
  (if (endp vars)
    nil
    (if (boundp-global (car vars) state)
      (unbound-globals (cdr vars) state)
      (cons (car vars) (unbound-globals (cdr vars) state)))))

(defmacro current-super-history ()
  '(cons (w state)
         (get-globals (@ super-history-globals) state)))

(defun start-super-history (match-globals restore-only-globals state)
  (if (super-history-activep state)
    state
    (let* ((all-globals (append match-globals restore-only-globals))
           (unbound-vars (unbound-globals all-globals state))
           (nil-vals (make-list (len unbound-vars))))
      (pprogn
       (put-globals unbound-vars nil-vals state)
       (f-put-global 'super-history-globals
                     all-globals
                     state)
       (f-put-global 'super-history-match-globals
                     match-globals
                     state)
       (f-put-global 'super-history
                     (list (current-super-history))
                     state)
       (f-put-global 'super-history-reverted
                     nil
                     state)))))

(defun update-super-history (state)
  (if (not (super-history-activep state))
    state
    (let* ((hist (@ super-history))
           (prev (car hist)))
      (if (and (equal (car prev) (w state))
               (cmp-globals (@ super-history-match-globals) ; only compare those that aren't restore-only
                            (cdr prev)
                            state))
        state
        (pprogn
         (f-put-global 'super-history
                       (cons (current-super-history) hist)
                       state)
         (f-put-global 'super-history-reverted nil state))))))

(defun clear-reverted-super-history (state)
  (f-put-global 'super-history-reverted nil state))

(defun take-rev-prepend (n src dst)
;  (declare (xargs :guard (and (natp n)
;                              (true-listp src)
;                              (true-listp dst))))
  (if (or (zp n) (endp src))
    dst
    (take-rev-prepend (1- n) (cdr src) (cons (car src) dst))))

(defun revert-super-history (n state)
  (cond
   ((not (super-history-activep state))
    (er soft 'revert-super-history "SUPER-HISTORY not active"))
   ((not (posp n))
    (er soft 'top-level "Bad value for SUPER-HISTORY: ~x0." n))
   (t
    (let* ((hist     (@ super-history))
           (rvrt     (@ super-history-reverted))
           (histlen  (len hist))
           (rvrtlen  (len rvrt)))
      (cond
       ((= n histlen)
        (pprogn
         (restore-current-super-history state)
         (value :invisible)))
       ((< n histlen)
        (pprogn
         (f-put-global 'super-history
                       (nthcdr (- histlen n) hist)
                       state)
         (f-put-global 'super-history-reverted
                       (take-rev-prepend (- histlen n) hist rvrt)
                       state)
         (restore-current-super-history state)
         (value :invisible)))
       ((<= n (+ histlen rvrtlen)) ; and n > histlen
        (pprogn
         (f-put-global 'super-history-reverted
                       (nthcdr (- n histlen) rvrt)
                       state)
         (f-put-global 'super-history
                       (take-rev-prepend (- n histlen) rvrt hist)
                       state)
         (restore-current-super-history state)
         (value :invisible)))
       (t
        (er soft 'top-level "Bad value for SUPER-HISTORY: ~x0." n)))))))

(defmacro revert-super-history-on-error (form)
  `(let ((revert-super-history-on-error-temp
          (if (super-history-activep state)
            (len (@ super-history))
            (w state))))
     (acl2::acl2-unwind-protect
      "revert-super-history-on-error"
      (acl2::check-vars-not-free (revert-super-history-on-error-temp) ,form)
      (if (integerp revert-super-history-on-error-temp)
        (mv-let (erp val state)
                (revert-super-history revert-super-history-on-error-temp state)
                (declare (ignore erp val))
                state)
        (set-w! revert-super-history-on-error-temp state))
      state)))


(push-untouchable (super-history
                   super-history-reverted
                   super-history-globals
                   super-history-match-globals) nil)
(push-untouchable (put-globals
                   restore-globals) t)



;; Install use of revert-super-history-on-error at the top-level
(defttag :acl2s-super-history)

(progn+touchable :all
  (redefun+rewrite
   acl2::ld-read-eval-print
   (:carpat (acl2::revert-world-on-error %form%)
    :recvars %form%
    :mult 1 ; we might want to re-examine the situation if we get more than one
    :repl (if (= 1 (@ ld-level))
            (revert-super-history-on-error %form%)
            (acl2::revert-world-on-error %form%))))
  
  (redefun+rewrite
   acl2::ld-read-eval-print
   :seq
   (:carpat %body%
    :vars %body%
    :repl (let ((old-std-oi-super-history (standard-oi state)))
            %body%))
   (:carpat (acl2::ld-print-results %trans-ans% state)
    :vars %trans-ans%
    :mult 1
    :repl (pprogn
           (if (equal old-std-oi-super-history *standard-oi*)
             (update-super-history state)
             state)
           (acl2::ld-print-results %trans-ans% state)))))

(defttag nil)



;;SUPPORT FOR :UBT, :UBU

(defun superlen-for-maxevt1 (maxevt super-history)
  (if (endp super-history)
    0
    (let ((wrld (caar super-history)))
      (if (and (<= (max-absolute-event-number wrld) maxevt)
               (eq (caar wrld) 'acl2::command-landmark)
               (eq (cadar wrld) 'global-value))
         (len super-history)
         (superlen-for-maxevt1 maxevt (cdr super-history))))))
  
(defun superlen-for-maxevt (maxevt state)
  (superlen-for-maxevt1 maxevt (@ super-history)))

(defun ubt-cd-to-superlen (cd state)
  (er-let*
    ((cd-wrld (acl2::er-decode-cd cd (w state) ':ubt state)))
    (value (superlen-for-maxevt (max-absolute-event-number
                                 (scan-to-command (cdr cd-wrld)))
                                state))))

(defmacro print-ubt-superlen (cd)
  `(er-let*
     ((n (ubt-cd-to-superlen ',cd state)))
     (fmx-canonical "INDEX:~p0~%" n)))

(defun ubu-cd-to-superlen (cd state)
  (er-let*
    ((cd-wrld (acl2::er-decode-cd cd (w state) ':ubu state)))
    (value (superlen-for-maxevt (max-absolute-event-number cd-wrld)
                                state))))

(defmacro print-ubu-superlen (cd)
  `(er-let*
     ((n (ubu-cd-to-superlen ',cd state)))
     (fmx-canonical "INDEX:~p0~%" n)))
