(in-package "ACL2")
(include-book "utils")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; file generates-theorems.lisp, this file generates theorems
;; for a formalization in ACL2                                             ;
;                                                                                                    ;
;   Written by : Philippe Georgelin                                        ;
;   Email : Philippe.Georgelin@imag.fr
;                                                                          ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-lemma-putst (name-ent name_arch
			 channel
			 state)
  (declare (xargs :stobjs state
		:mode :program))
  (fms "
;; the type of putst is true-list when
;; st is a true-listp. This theorem is necessary
;; to satisfy hypothesis of all theorems using putst
(defthm ~x0
  (implies (true-listp st)
	   (true-listp (~x1 var value st)))
  :rule-classes (:type-prescription :rewrite))"
(list (cons #\0 (make-name name-ent name_arch "-lemma-putst"))
      (cons #\1 (make-name name-ent name_arch "-putst")))
channel
state
nil))


(defun name_of_conc_stat (name-ent name-arch list_of_process)
  (if (endp list_of_process)
      nil
      (let ((name-update-sig (make-name name-ent name-arch "-update-signals")))
    `((,name-update-sig (,(make-name (concatenate 'string
			       (string name-ent)
			       (string name-arch)
			       "-")
		  (caar list_of_process)
		  "-cycle")
       ,(make-onename "st")))
	  ,@(name_of_conc_stat name-ent name-arch (cdr list_of_process))))))


(defun name-only-rec (name-ent name-arch list_of_process)
  (if (endp list_of_process)
      nil
      (cons (make-name (concatenate 'string
			       (string name-ent)
			       (string name-arch)
			       "-")
		  (caar list_of_process)
		  "-cycle")
	  (name-only-rec name-ent name-arch (cdr list_of_process)))))


(defun make-rec-concurrent-stat-lemma (name-ent name_architecture
				 concurrent-stat channel state)
     (declare (xargs :stobjs state
		  :mode :program))
  (cond ((endp concurrent-stat) state)
	(t (let ((name_conc (name_of_conc_stat name-ent name_architecture concurrent-stat))
		 (name-only (cons (make-name name-ent name_architecture "-update-signals")
			        (name-only-rec name-ent name_architecture concurrent-stat))))

(fms "~%~%;;======== Function rec-concurrent-stat  =====~%~%

(defthm ~x2 ~%
(and (equal (~x0 0 st) st)
       (implies (naturalp n)
		(equal
		 (~x0 (1+ n) st)
		 (~x0 n
		      ~x1))))
:hints ((\"Goal\" :in-theory ~x3))) ~%"

(list
(cons #\0 (make-name name-ent name_architecture "-rec-conc-stat"))
(cons #\1 (append '(seq st) name_conc))
(cons #\2 (make-name name-ent name_architecture "unfld-rec-conc-stat"))
(cons #\3 (cons 'disable name-only))
)
channel
state
nil)))))



(defun make-lemma-cycle (name-ent name_arch
			 channel
			 state)
  (declare (xargs :stobjs state
		:mode :program))
  (fms "
; Simulation step maps well-formed states to well-formed states.
;(defthm ~x0
;  (implies (~x1 st)
;	   (~x1 (~x2 st))))"
(list (cons #\0 (make-name name-ent name_arch "-cycle-lemma"))
      (cons #\1 (make-name name-ent name_arch "-stp"))
      (cons #\2 (make-name name-ent name_arch "-cycle")))
channel
state
nil))


(defun make-unfold-simul (name-ent name_arch
			  channel
			  state)
  (declare (xargs :stobjs state
		:mode :program))
  (fms "
;; Unfold one step of simulation function.
(defthm ~x0
  (and (equal (~x1 0 st) st)
       (implies (naturalp n)
		(equal
		 (~x1 (1+ n) st)
		 (~x1 n
		      (~x2
		       (~x3 st))))))
  :hints ((\"Goal\" :in-theory (disable ~x2
					~x3))))"

(list (cons #\0 (make-name name-ent name_arch "-unfold-simul"))
      (cons #\1 (make-name name-ent name_arch "-simul"))
      (cons #\2 (make-name name-ent name_arch "-cycle"))
      (cons #\3 (make-name name-ent name_arch "-update-signals")))
channel
state
nil))

