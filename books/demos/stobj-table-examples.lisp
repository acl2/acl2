; Copyright (C) 2021, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;
;; First example: simple switch stobj with access and update through stobj-table..
;;

(include-book "std/stobjs/stobj-table" :dir :system)

(defstobj switch fld)

(defun flip-switch (stobj-table)
  (declare (xargs :stobjs (stobj-table)))
  (stobj-let ((switch (tbl-get 'switch stobj-table (create-switch))))
             (switch)  (update-fld (not (fld switch)) switch)  stobj-table))

(defun print-switch (stobj-table)
  (declare (xargs :stobjs (stobj-table)))
  (stobj-let ((switch (tbl-get 'switch stobj-table (create-switch))))
             (current)  (if (fld switch) "ON" "OFF")  current))

#|

ACL2 !>(print-switch stobj-table)
"OFF"
ACL2 !>(flip-switch stobj-table)
<stobj-table>
ACL2 !>(print-switch stobj-table)
"ON"
ACL2 !>(flip-switch stobj-table)
<stobj-table>
ACL2 !>(print-switch stobj-table)
"OFF"

;; Interestingly (maybe), the first call of (print-switch stobj-table) actually
;; calls (create-switch) to make a new switch stobj but that stobj is dropped
;; on the floor since it is not assigned back into the stobj-table. The first
;; call of (flip-switch stobj-table) also calls (create-switch), then flips the
;; fld value in the switch, and this switch is then actually put back into the
;; stobj-table and is used in subsequent print-switch and flip-switch calls.

|#


;;;;;;;;;;;;;;;;;;;;;;
;; Second example: A more elaborate use of stobj-tables in program refinement.
;;
;; a process scheduler which we define in the following program refinement
;; steps and definitions.. the purpose of this example is to show how
;; stobj-tables allow for the use of stobjs in program refinements in ACL2
;; using constrained functions .. this would not be possible before
;; stobj-tables since a generic stobj would need to be defined which supported
;; process local states, shared states, and scheduler states. In this example,
;; the top-level run function has no understanding of the state of the system,
;; the processes are only aware of their own state and communicate requests to
;; the scheduler through an interface of update requests. Each component of the
;; system is defined to only support the properties placed upon it as part of
;; the bigger system and to not interfere with the state of the other
;; components. Stobj-tables are critical to allowing this to work.
;;
;; NOTE -- the definitions here are all in one book for the sake of exposition
;;  and easy reference, but in general, the benefit of this approach of program
;;  refinement is to allow development in larger scale where separate books
;;  need to only include the imported definitions and properties required for
;;  the exported definitions and properties for the book.
;;


;; simple stobj we will use for storing the scheduler state, any shared state,
;; and all of the local states of the processes (each assumed to be in separate
;; stobjs stored in the stobj table field). We could have used the
;; std/stobjs/stobj-table stobj-table as in the previous example (and the
;; following st stobj could be marked congruent), but we decide to use a
;; different one here since one could (or may want to) add fields to st for the
;; sake of the scheduler

(defstobj st (stbl :type (stobj-table 100)))

;;;;;;;;;;;
;; Part 1. initial definitions for a run function with abstract scheduler and
;;    processes, we only need a rank which decreases to ensure that the run
;;    function will terminate if it keeps executing processes that are ready!
;;    The goal here is to admit a suitable run function with as few
;;    requirements placed on the component functions as possible.
;;

(encapsulate
  (((proc-ids)   => *)
   ((pick st)    => *)
   ((ready * st) => *  :formals (p st) :guard (symbolp p))
   ((exec * st)  => st :formals (p st) :guard (symbolp p))
   ((rank * st)  => *  :formals (p st) :guard (symbolp p)))
  
  (local (define proc-ids  () (list t)))
  (local (define pick    (st) (declare (ignore st))   t))
  (local (define ready (p st) (declare (ignore p st)) nil))
  (local (define exec  (p st) (declare (ignore p))    st))
  (local (define rank  (p st) (declare (ignore p st)) 0))

  ;; some "type" properties about the constrained functions:
  
  (defthm rank-is-natural      (natp (rank p st))  :rule-classes :type-prescription)
  (defthm pick-is-symbolp      (symbolp (pick st)) :rule-classes :type-prescription)
  (defthm proc-ids-are-symbols (symbol-listp (proc-ids)))
  
  ;; the basic required properties to allow definition and admittance of run:
  
  (defthm pick-is-proc-id
    (member-equal (pick st) (proc-ids)))
  
  (defthm exec-does-not-interfere
    (implies (not (equal p q)) (<= (rank p (exec q st)) (rank p st)))
    :rule-classes (:linear :rewrite))
  
  (defthm exec-rank-reduces
    (implies (ready p st) (< (rank p (exec p st)) (rank p st)))
    :rule-classes (:linear :rewrite)))

(define sum-rank ((lst symbol-listp) st)
  :returns (r natp)
  (if (atom lst) 0
    (+ (rank (first lst) st)
       (sum-rank (rest lst) st)))
  ///
  (defthm sum-rank-<-lst
    (implies (and (member-equal p lst)
                  (ready p st))
             (< (sum-rank lst (exec p st))
                (sum-rank lst st)))
    :hints (("goal" :induct (sum-rank lst st))
            (and stable-under-simplificationp
                 '(:cases ((equal (car lst) p)))))
    :rule-classes (:linear :rewrite)))

;; we define a constrained reporting function that we can later extend via
;; attachment (although we only attach a trivial report function here):

(encapsulate (((report-completion-or-error-and-return * st) => (mv * st)))  
  (local (define report-completion-or-error-and-return (p st) (mv p st))))

(define default-report-completion (p st) (mv p st))
(defattach report-completion-or-error-and-return default-report-completion)

;;;;;;
;; Now, we get to the run function which tries to pick a process and execute
;; it until it needs access to a shared resource or pauses or completes..

(defun run (st)
  (declare (xargs :measure (sum-rank (proc-ids) st) :stobjs (st)))
  (let ((p (pick st)))
    (if (ready p st) (let ((st (exec p st))) (run st))
      (report-completion-or-error-and-return p st))))


;;;;;;;;;;;
;; Part 2.
;;  We define the constraints on processes which are added to to the system. 
;;  Basically, each process should have a p-rank which reduces to completion
;;  and properties to ensure that the process does not effect any states in
;;  the stobj-table other than its own.
;;

(defmacro get-proc-st (p st)
  `(cdr (hons-assoc-equal ,p (car ,st))))

(fty::deftagsum sched-upd
  (:acquire ((lock symbolp)))
  (:release ((lock symbolp)))
  (:utilize ((lock symbolp) (op any-p))))

(fty::deflist sched-upd-list
  :elt-type sched-upd-p
  :true-listp t)

(encapsulate
  (((p-exec * st) => (mv * st) :formals (p st) :guard (symbolp p))
   ((p-rank * st) => *         :formals (p st) :guard (symbolp p))
   ((p-done * st) => *         :formals (p st) :guard (symbolp p))
   ((p-ids)       => *))

  (local (define p-exec ((p symbolp) st) (declare (ignore p)) :enabled t (mv nil st)))
  (local (define p-rank ((p symbolp) st) (declare (ignore p st)) 0))
  (local (define p-done ((p symbolp) st) (declare (ignore p st)) t))
  (local (define p-ids  () ()))

  (defthm p-ids-are-symbols (symbol-listp (p-ids)))
  (defthm p-exec-upd-list   (sched-upd-list-p (mv-nth 0 (p-exec p st))))
  (defthm p-rank-is-natural (natp (p-rank p st)) :rule-classes :type-prescription)

  ;; The 'sched and 'shared symbols cannot be in (p-ids) to avoid collision
  ;; with the schedule state and shared state and 'error and 'complete are
  ;; special pick return values that we need to reserve:
  (defthm sched-not-p-id    (not (member-equal 'sched    (p-ids))))
  (defthm shared-not-p-id   (not (member-equal 'shared   (p-ids))))
  (defthm error-not-p-id    (not (member-equal 'error    (p-ids))))
  (defthm complete-not-p-id (not (member-equal 'complete (p-ids))))

  (defthm p-fns-only-fn-of-proc-st
    ;; NOTE -- this property kind of stinks.. I would like to change
    ;;         this property to a useful rule, but it requires (I think)
    ;;         a function of (get-proc-st p st), but this requires constraining
    ;;         a function which needs to be attached to a function which takes
    ;;         the actual stobj as a parameter -- but that is not allowed, so
    ;;         we are left with only being able to define functions of the
    ;;         stobj-table holding st.. which is why we end up with this
    ;;         formula.. -- would love to refactor this as something more useful.
    (implies (equal (get-proc-st p st1) (get-proc-st p st2))
             (and (equal (p-rank p st1) (p-rank p st2))
                  (equal (p-done p st1) (p-done p st2))))
    :rule-classes nil)

  (defthm p-exec-p-rank-reduces
    (implies (not (p-done p st))
             (< (p-rank p (mv-nth 1 (p-exec p st)))
                (p-rank p st)))
    :rule-classes (:linear :rewrite))

  (defthm p-exec-does-not-interfere
    (implies (not (equal p q)) ;; insures only local state is changed!
             (equal (get-proc-st q (mv-nth 1 (p-exec p st)))
                    (get-proc-st q st)))))

;;;;;;;;;;;
;; Part 3.
;;  We now define a macro which can be used to add new processes to the system
;;  via attachments which extend the p-* functions from the encapsulate in the
;;  previous part. 

(define p-exec+p0 ((p symbolp) st) (declare (ignore p))    :enabled t (mv nil st))
(define p-rank+p0 ((p symbolp) st) (declare (ignore p st)) :enabled t 0)
(define p-done+p0 ((p symbolp) st) (declare (ignore p st)) :enabled t t)
(define p-ids+p0  () :enabled t ())

(defthm p-fns-only-fn-of-proc-st+p0
  (implies (equal (get-proc-st p st1) (get-proc-st p st2))
           (and (equal (p-rank+p0 p st1) (p-rank+p0 p st2))
                (equal (p-done+p0 p st1) (p-done+p0 p st2))))
  :rule-classes nil)

(define mk-str-fn (x)
  :returns (r stringp)
  (cond ((natp x)    (str::natstr x))
        ((stringp x) x)
        ((symbolp x) (symbol-name x))
        (t (prog2$ (raise "unexpected type for mk-str-fn:~x0" x) ""))))

(define mk-str-lst (lst)
  :returns (r stringp)
  (if (atom lst) "" (string-append (mk-str-fn (first lst)) (mk-str-lst (rest lst)))))

(define mk-sym-fn (lst)
  :returns (r symbolp)
  (intern-in-package-of-symbol (mk-str-lst lst) 'foo))

(defmacro mk-sym (&rest args)
  `(mk-sym-fn (list ,@args)))

(defconst *init-pc* 10) ;; starting pc value in processes below:

(define pc-fix ((pc natp))
  :returns (r natp)
  :inline t
  :enabled t
  (mbe :logic (if (natp pc) pc *init-pc*)
       :exec  pc))

(define add-process-i ((i posp))
  (b* ((ps           (mk-sym "P" i))
       (pci          (mk-sym "PC" i))
       (update-pci   (mk-sym "UPDATE-PC" i))
       (pi-exec      (mk-sym "P" i "-EXEC"))
       (create-pi    (mk-sym "CREATE-P" i))
       (p-exec+pi    (mk-sym "P-EXEC+P" i))
       (p-rank+pi    (mk-sym "P-RANK+P" i))
       (p-done+pi    (mk-sym "P-DONE+P" i))
       (p-ids+pi     (mk-sym "P-IDS+P" i))
       (p-exec+pi-1  (mk-sym "P-EXEC+P" (1- i)))
       (p-rank+pi-1  (mk-sym "P-RANK+P" (1- i)))
       (p-done+pi-1  (mk-sym "P-DONE+P" (1- i)))
       (p-ids+pi-1   (mk-sym "P-IDS+P" (1- i)))
       (init-pc      *init-pc*)
       (ai           (mk-sym "LOCK-P" i))
       ;; this introduces a "bug" in process p3:
       (ri           (mk-sym "LOCK-P" (if (eql i 3) 2 i)))
       (sched-not-p-id    (mk-sym "SCHED-NOT-P-ID+P" i))
       (shared-not-p-id   (mk-sym "SHARED-NOT-P-ID+P" i))
       (error-not-p-id    (mk-sym "ERROR-NOT-P-ID+P" i))
       (complete-not-p-id (mk-sym "COMPLETE-NOT-P-ID+P" i))
       (p-fns-only-fn-of-proc-st   (mk-sym "P-FNS-ONLY-FN-OF-PROC-ST+P" i))
       (p-fns-only-fn-of-proc-st-1 (mk-sym "P-FNS-ONLY-FN-OF-PROC-ST+P" (1- i)))
       (p-exec-p-rank-reduces      (mk-sym "P-EXEC-P-RANK-REDUCES+P" i))
       (p-exec-does-not-interfere  (mk-sym "P-EXEC-DOES-NOT-INTERFERE+P" i)))
    `(progn
       (defstobj ,ps (,pci :type (integer 0 *) :initially ,init-pc))
       (define ,pi-exec (,ps) :enabled t
         :returns (mv (r sched-upd-list-p) ,ps)
         (b* ((pc  (pc-fix (,pci ,ps)))
              (,ps (if (zp pc) ,ps (,update-pci (1- pc) ,ps))))
           (cond ((zp pc)    (mv nil ,ps))
                 ((eql pc 1) (mv (list (sched-upd-release (quote ,ri))) ,ps))
                 ((eql pc 2) (mv (list (sched-upd-acquire (quote ,ai))) ,ps))
                 (t (mv nil ,ps)))))
       (define ,p-exec+pi ((p symbolp) st)
         :returns (mv (r sched-upd-list-p) st)
         (if (eq p (quote ,ps))
             (stobj-let ((,ps (stbl-get (quote ,ps) st (,create-pi))))
                        (upds ,ps) (,pi-exec ,ps) (mv upds st))
           (,p-exec+pi-1 p st)))
       (define ,p-rank+pi ((p symbolp) st)
         :returns (r natp)
         (if (eq p (quote ,ps))
             (stobj-let ((,ps (stbl-get (quote ,ps) st (,create-pi))))
                        (rank) (pc-fix (,pci ,ps)) rank)
           (,p-rank+pi-1 p st)))
       (define ,p-done+pi ((p symbolp) st)
         (if (eq p (quote ,ps))
             (stobj-let ((,ps (stbl-get (quote ,ps) st (,create-pi))))
                        (done) (zp (pc-fix (,pci ,ps))) done)
           (,p-done+pi-1 p st)))
       (define ,p-ids+pi ()
         :returns (r symbol-listp)
         (cons (quote ,ps) (,p-ids+pi-1)))
       ;;;
       (defthm ,sched-not-p-id    (not (member-equal 'sched    (,p-ids+pi))))
       (defthm ,shared-not-p-id   (not (member-equal 'shared   (,p-ids+pi))))
       (defthm ,error-not-p-id    (not (member-equal 'error    (,p-ids+pi))))
       (defthm ,complete-not-p-id (not (member-equal 'complete (,p-ids+pi))))
       ;;;
       (defthm ,p-fns-only-fn-of-proc-st
         (implies (equal (get-proc-st p st1) (get-proc-st p st2))
                  (and (equal (,p-rank+pi p st1) (,p-rank+pi p st2))
                       (equal (,p-done+pi p st1) (,p-done+pi p st2))))
         :hints (("Goal" :in-theory (enable ,p-rank+pi ,p-done+pi)
                  :use ((:instance ,p-fns-only-fn-of-proc-st-1))))
         :rule-classes nil)
       ;;;
       (defthm ,p-exec-p-rank-reduces
         (implies (not (,p-done+pi p st))
                  (< (,p-rank+pi p (mv-nth 1 (,p-exec+pi p st)))
                     (,p-rank+pi p st)))
         :hints (("Goal" :in-theory (enable ,p-exec+pi ,p-rank+pi ,p-done+pi)))
         :rule-classes (:linear :rewrite))
       ;;;
       (defthm ,p-exec-does-not-interfere
         (implies (not (equal p q)) ;; insures only local state is changed!
                  (equal (get-proc-st q (mv-nth 1 (,p-exec+pi p st)))
                         (get-proc-st q st)))
         :hints (("Goal" :in-theory (enable ,p-exec+pi))))
       ;;;
       (defattach
         (p-exec ,p-exec+pi)
         (p-rank ,p-rank+pi)
         (p-done ,p-done+pi)
         (p-ids  ,p-ids+pi)
         :hints (("Goal" :use ((:instance ,p-fns-only-fn-of-proc-st)))))
       )))

(defmacro add-pi (i)
  (declare (xargs :guard (posp i)))
  (add-process-i i))

;; instantiate a couple of processes and add them to the attached functions:
(add-pi 1)
(add-pi 2)

;;;;;;;;;;;
;; Part 4. 
;;  We quickly define a simple example shared state which is used for updating
;;  a shared state via performing protected op.s (which require a lock). This
;;  is merely showing an example of what could be introduced with a 'shared
;;  stobj defining a shared state and updated through an attachment to
;;  perform-prot-op.
;;

(defstobj shared
  (shared-ctr   :type (integer 0 *) :initially 0)
  (shared-procs :type (satisfies symbol-listp)))

(encapsulate
  (((perform-prot-op * * * st) => st
    :formals (lock op proc st) :guard (and (symbolp lock) (symbolp proc))))

  (local (define perform-prot-op (lock op proc st)
           (declare (ignore lock op proc))
           :enabled t
           st))

  (defthm p-id-proc-state-perform-prot
    (implies (not (equal p 'shared))
             (equal (get-proc-st p (perform-prot-op lock op q st))
                    (get-proc-st p st)))))

;; simple shared resource state update (should add some error reporting though
;; for operation attempts without appropriate locks):

(define perform-prot-shared ((lock symbolp) op (proc symbolp) shared)
  (cond ((and (eq lock 'counter) (eq op 'incr-ctr))
         (update-shared-ctr (1+ (shared-ctr shared)) shared))
        ((and (eq lock 'counter) (eq op 'decr-ctr))
         (update-shared-ctr (nfix (1- (shared-ctr shared))) shared))
        ((and (eq lock 'procs) (eq op 'record-proc))
         (update-shared-procs (cons proc (shared-procs shared)) shared))
        (t shared)))

(define default-perform-prot-op ((lock symbolp) op (proc symbolp) st)
  (stobj-let ((shared (stbl-get 'shared st (create-shared))))
             (shared) (perform-prot-shared lock op proc shared) st)
  ///
  (defthm p-id-proc-state-default-perform-prot
    (implies (not (equal p 'shared))
             (equal (get-proc-st p (default-perform-prot-op lock op q st))
                    (get-proc-st p st)))))

(defattach perform-prot-op default-perform-prot-op)

;;;;;;;;;;;
;; Part 5. 
;;  We define a simple scheduler and an interface between processes and the
;;  scheduler.. in particular, calling (exec p st) will now return (mv <upds>
;;  st) where <upds> is a list of requests, releases, etc. being returned from
;;  the process to the scheduler which the scheduler will use to update its
;;  state. A process can read the scheduler state but cannot update it.. there
;;  is also a special stobj 'shared which processes can modify but otherwise,
;;  they are only allowed to modify
;;

(defstobj sched
  (lock-tbl    :type (hash-table eq 100)) 
  (owned-tbl   :type (hash-table eq 100))
  (wait-tbl    :type (hash-table eq 100))
  (blocked-tbl :type (hash-table eq 100))
  (run-clk     :type (integer 0 *) :initially 0)
  (prev-picks  :type (satisfies symbol-listp))
  (sched-error))

(define record-sch-error (err &key (sched 'sched))
  (update-sched-error err sched))

(define acquire-lock ((lock symbolp) (proc symbolp) sched)
  (b* (((mv prev exists) (owned-tbl-get? proc sched)))
    (if exists ;; we already own a lock, can't get another:
        (record-sch-error (list "process cannot own more than one lock!"
                                proc prev lock))
      (b* (((mv owner exists) (lock-tbl-get? lock sched)))
        (cond
         ((not exists)
          (b* ((sched (lock-tbl-put lock proc sched)))
            (owned-tbl-put proc lock sched)))
         ((eq owner proc) sched) ;; already owner
         (t ;; otherwise, we block and wait:
          (b* ((sched (blocked-tbl-put proc t sched))
               (waits (wait-tbl-get lock sched))
               (sched (wait-tbl-put lock (cons proc waits) sched)))
            sched)))))))

(define clear-each-block (procs sched)
  (if (atom procs) sched
    (b* ((proc (first procs)))
      (if (not (symbolp proc))
          (record-sch-error (list "Internal error: proc is not symbolp!" procs))
        (b* ((sched (blocked-tbl-rem proc sched)))
          (clear-each-block (rest procs) sched))))))

(define release-lock ((lock symbolp) (proc symbolp) sched)
  (b* (((mv owner exists) (lock-tbl-get? lock sched)))
    (cond
     ((not exists) ;; throw an error:
      (record-sch-error (list "process trying to release a lock but there is no lock!"
                              proc lock)))
     ((not (eq owner proc)) ;; and here:
      (record-sch-error (list "process trying to release a lock it does not own!"
                              proc lock)))
     (t (b* ((sched (lock-tbl-rem lock sched))
             (sched (owned-tbl-rem proc sched))
             (sched (clear-each-block (wait-tbl-get lock sched) sched))
             (sched (wait-tbl-rem lock sched)))
          sched)))))

;; wrapper functions which lift the sched operations to st:

(define acquire-lock-st ((lock symbolp) (proc symbolp) st)
  (stobj-let ((sched (stbl-get 'sched st (create-sched))))
             (sched) (acquire-lock lock proc sched) st)
  ///
  (defthm acquire-lock-only-sched
    (implies (not (equal p 'sched))
             (equal (get-proc-st p (acquire-lock-st lock proc st))
                    (get-proc-st p st)))))

(define release-lock-st ((lock symbolp) (proc symbolp) st)
  (stobj-let ((sched (stbl-get 'sched st (create-sched))))
             (sched) (release-lock lock proc sched) st)
  ///
  (defthm release-lock-only-sched
    (implies (not (equal p 'sched))
             (equal (get-proc-st p (release-lock-st lock proc st))
                    (get-proc-st p st)))))

(define owns-lock-st ((lock symbolp) (proc symbolp) st)
  (stobj-let ((sched (stbl-get 'sched st (create-sched))))
             (owns)
             (b* (((mv owner exists) (lock-tbl-get? lock sched)))
               (and exists (eq owner proc)))
             owns))

(define report-error-st (obj &key (st 'st))
  (stobj-let ((sched (stbl-get 'sched st (create-sched))))
             (sched) (record-sch-error obj) st)
  ///
  (defthm report-error-only-sched
    (implies (not (equal p 'sched))
             (equal (get-proc-st p (report-error-st obj))
                    (get-proc-st p st)))))

(define sched-error-st (st)
  (stobj-let ((sched (stbl-get 'sched st (create-sched))))
             (sch-err) (sched-error sched) sch-err))

(define utilize-lock-st ((lock symbolp) op (proc symbolp) st)
  (if (owns-lock-st lock proc st)
      (perform-prot-op lock op proc st)
    (report-error-st (list "process does not own lock for protected op!" lock
                           op proc)))
  ///
  (defthm utilize-lock-only-sched-shared
    (implies (and (not (equal p 'sched))
                  (not (equal p 'shared)))
             (equal (get-proc-st p (utilize-lock-st lock op proc st))
                    (get-proc-st p st)))))

;; sched-update function which takes an update from a process and does the
;; corresponding action:

(define sched-update ((upd sched-upd-p) (proc symbolp) st)
  (case (sched-upd-kind upd)
    (:acquire (acquire-lock-st (sched-upd-acquire->lock upd)
                               proc st))
    (:release (release-lock-st (sched-upd-release->lock upd)
                               proc st))
    (:utilize (utilize-lock-st (sched-upd-utilize->lock upd)
                               (sched-upd-utilize->op upd)
                               proc st))
    (t (report-error-st (list "Internal error! bad sched-upd:"
                              proc upd))))
  ///
  (defthm sched-update-only-sched-shared
    (implies (and (not (equal p 'sched))
                  (not (equal p 'shared)))
             (equal (get-proc-st p (sched-update upd proc st))
                    (get-proc-st p st)))))

(define incr-sched-pick ((proc symbolp) sched)
  (b* ((sched (update-run-clk (1+ (run-clk sched)) sched))
       (sched (update-prev-picks (cons proc (prev-picks sched)) sched)))
    sched))

(define increment-sched-pick-st ((proc symbolp) st)
  (stobj-let ((sched (stbl-get 'sched st (create-sched))))
             (sched) (incr-sched-pick proc sched) st)
  ///
  (defthm increment-sched-only-sched
    (implies (not (equal p 'sched))
             (equal (get-proc-st p (increment-sched-pick-st proc st))
                    (get-proc-st p st)))))

(define sched-updates ((upds sched-upd-list-p) (proc symbolp) st)
  (if (atom upds)
      (increment-sched-pick-st proc st)
    (b* ((st (sched-update (first upds) proc st)))
      (sched-updates (rest upds) proc st)))
  ///
  (defthm sched-updates-only-sched-shared
    (implies (and (not (equal p 'sched))
                  (not (equal p 'shared)))
             (equal (get-proc-st p (sched-updates upds proc st))
                    (get-proc-st p st)))))
;;

(defthm subsetp-equal-over-cons
  (implies (subsetp-equal x y)
           (subsetp-equal x (cons a y))))

(defthm subsetp-equal-reflex (subsetp-equal x x))

(defthm subsetp-equal-transits
  (implies (and (subsetp-equal x y) (subsetp-equal y z))
           (subsetp-equal x z))
  :rule-classes nil)

;;

(encapsulate
  (((final-pick-choice * st) => *
    :formals (x st) :guard (symbol-listp x)))

  (local (define final-pick-choice ((x symbol-listp) st)
           (declare (ignore st))
           :enabled t
           (and (consp x) (first x))))

  (defthm final-pick-choice-member-equal
    (implies (and (consp x) (subsetp-equal x y))
             (member-equal (final-pick-choice x st) y)))

  (defthm final-pick-choice-is-symbolp
    (implies (symbol-listp x)
             (symbolp (final-pick-choice x st)))))

(define default-final-pick-choice ((x symbol-listp) st)
  (declare (ignore st))
  :enabled t
  (and (consp x) (first x)))

(defattach final-pick-choice default-final-pick-choice)

;;

(define find-undone ((ps symbol-listp) st)
  :returns (r symbol-listp :hyp (symbol-listp ps))
  (if (endp ps) ()
    (b* ((p (first ps)))
      (if (p-done p st)
          (find-undone (rest ps) st)
        (cons p (find-undone (rest ps) st)))))
  ///
  (defthm find-undone-subsetp-equal
    (subsetp-equal (find-undone ps st) ps)))

(define find-unblocked ((ps symbol-listp) sched)
  :returns (r symbol-listp :hyp (symbol-listp ps))
  (if (endp ps) ()
    (b* ((p (first ps)))
      (if (blocked-tbl-get p sched)
          (find-unblocked (rest ps) sched)
        (cons p (find-unblocked (rest ps) sched)))))
  ///
  (defthm find-unblocked-subsetp-equal
    (subsetp-equal (find-unblocked ps st) ps)))

(defthm find-unblocked-undone-chain
  (subsetp-equal (find-unblocked (find-undone p s1) s2) p)
  :hints (("Goal" :use ((:instance subsetp-equal-transits
                                   (x (find-unblocked (find-undone p s1) s2))
                                   (y (find-undone p s1))
                                   (z p))))))

(define find-pick-sched ((procs symbol-listp) st)
  :returns (r symbolp :hyp (symbol-listp procs))
  (b* ((undone (find-undone procs st)))
    (if (endp undone) 'complete
      (b* ((unblocked (stobj-let ((sched (stbl-get 'sched st (create-sched))))
                                 (ps) (find-unblocked undone sched) ps)))
        (if (endp unblocked) 'error
          (final-pick-choice unblocked st)))))
  ///
  (defthm find-pick-sched-member-equal
    (member-equal (find-pick-sched ps st)
                  (list* 'complete 'error ps))))

;; define final top-level functions which add in the scheduler and process
;; functions (defined through previous constrained "p-" functions):

(define proc-ids+sched () (list* 'complete 'error (p-ids)))

(define pick+sched (st) (find-pick-sched (p-ids) st))

(define ready+sched ((p symbolp) st)
  (not (or (member-eq p '(complete error sched shared))
           (sched-error-st st)
           (stobj-let ((sched (stbl-get 'sched st (create-sched))))
                      (chk) (blocked-tbl-get p sched) chk)
           (p-done p st))))

(define exec+sched ((p symbolp) st)
  (b* (((mv upds st) (p-exec p st))) (sched-updates upds p st)))
     
(define rank+sched ((p symbolp) st)
  (if (member-eq p '(complete error sched shared)) 0 (p-rank p st)))


;; required properties of our functions to allow these functions to be
;; attached to the top level functions:

(defthm rank+sched-is-natural (natp (rank+sched p st)))
(defthm pick+sched-is-symbolp (symbolp (pick+sched st))
  :hints (("Goal" :in-theory (e/d (proc-ids+sched pick+sched) ((proc-ids+sched))))))
(defthm proc-ids+sched-are-symbols (symbol-listp (proc-ids+sched))
  :hints (("Goal" :in-theory (e/d (proc-ids+sched) ((proc-ids+sched))))))

(defthm pick+sched-is-proc-id
  (member-equal (pick+sched st) (proc-ids+sched))
  :hints (("Goal" :in-theory (e/d (proc-ids+sched pick+sched) ((proc-ids+sched))))))

(defthm exec+sched-does-not-interfere
  (implies (not (equal p q))
           (<= (rank+sched p (exec+sched q st))
               (rank+sched p st)))
  :hints (("Goal" :in-theory (enable rank+sched exec+sched)
           :use ((:instance p-fns-only-fn-of-proc-st
                            (st1 (SCHED-UPDATES (MV-NTH 0 (P-EXEC q ST)) q (MV-NTH 1 (P-EXEC q ST))))
                            (st2 st))))))

(defthm exec+sched-rank-reduces
  (implies (ready+sched p st)
           (< (rank+sched p (exec+sched p st))
              (rank+sched p st)))
  :hints (("Goal" :in-theory (enable ready+sched rank+sched exec+sched)
           :use ((:instance p-fns-only-fn-of-proc-st
                            (st1 (SCHED-UPDATES (MV-NTH 0 (P-EXEC p ST)) p (MV-NTH 1 (P-EXEC p ST))))
                            (st2 (MV-NTH 1 (P-EXEC p ST))))))))

;; and now we attach the functions to the top-level constrained functions:

(defattach
  (proc-ids proc-ids+sched)
  (pick     pick+sched)
  (ready    ready+sched)
  (exec     exec+sched)
  (rank     rank+sched))

;;;;;;;;;;;
;; Part 6. Testing
;;   We add some (commented out) tests to basically test the run function and
;;   in large part make sure we have actually attached definitions for all of
;;   the constrained functions :)

(define updated-report-completion (p st)
  (b* ((err (stobj-let ((sched (stbl-get 'sched st (create-sched))))
                       (err) (sched-error sched) err)))
    (mv (or err p) st)))

(defattach report-completion-or-error-and-return updated-report-completion)

(defstobj-clone st-copy st :suffix "-copy")

(define reset-run (st)
  ;; NOTE -- in order to "reset" the top-level st before we do a run, we simply
  ;;         swap the top-level st with a fresh local-stobj using the following:
  (with-local-stobj st-copy
    (mv-let (st st-copy) (swap-stobjs st st-copy) st)))

#| 

Example run below where we include this book (which instantiates 2 processes).
We (run st) which runs to completion without error, but then (add-pi 3) to add
a 3rd process, and then when we run again, we get an error (due to bug injected
for 3rd process above in add-process-i).

; ACL2 !>(include-book "examples")
; ACL2 !>(reset-run st)
; ACL2 !>(run st)
; (COMPLETE <st>)
; ACL2 !>(add-pi 3)
; ACL2 !>(reset-run st)
; ACL2 !>(run st)
; (("process trying to release a lock but there is no lock!" P3 LOCK-P2) <st>)

|#
