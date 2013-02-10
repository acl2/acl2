;; This file is ordinary (non-ACL2) LISP code for the interface between
;; the ACL2 code and the external theorem provers.
;;
;; Since this is loaded after the IVY books, we must make sure that
;; none of these functions overrides any of the IVY functions (except
;; external-prover and external-modeler below, which are supposed
;; to override the IVY defstubs).
;;
;;------------------------------------------------------

;; Global variables.

(defvar problem-name nil)  ;; a string used for temporary filenames
(defvar otter-binary nil)  ;; Otter binary
(defvar mace-binary nil)   ;; MACE binary
(defvar mace-parms "6 60 -m1 -I -c")

;; The default MACE parameters:
;; domainsize<=6, 60 sec, 1 model, IVY format, unique constants.

;;------------------------------------------------------

(defun cat-2-strings (s1 s2)
  (coerce (append (coerce s1 'list) (coerce s2 'list)) 'string))

(defun cat-strings (lst)
  (if (atom lst)
      ""
      (cat-2-strings (car lst) (cat-strings (cdr lst)))))

;;------------------------------------------------
;; Function external-prover takes an initial proof object which
;; represents a set of input clauses for a theorem prover.
;;
;; external-prover is a defstub in the ACL2 code, and this function takes its place.
;;
;; This uses global variables problem-name and otter-binary.

(defun external-prover (initial-proof-object)

  (progn

    ;; Problem-name is a global variable, used here for temporary filenames.
    ;; If problem-name is nil, use "otter" instead.

    (setq pname (or problem-name "otter"))
    (setq otter-in-filename (cat-strings (list pname ".in")))
    (setq otter-obj-filename (cat-strings (list pname ".proof-obj")))

    ;; Build an Otter input file.

    (with-open-file (fp otter-in-filename :direction :output)
		    (format fp "set(auto).~%")
		    (format fp "set(build_proof_object_2).~%")
		    (format fp "clear(sigint_interact).~%")
		    (format fp "assign(max_seconds, 10).~%")
		    (format fp "initial_proof_object(junk).~%")
		    (format fp "~%")
		    (print initial-proof-object fp)
		    (format fp "~%")
		    )

    ;; Run Otter and look for a proof object in the output.

    (setq unix-command
	  (cat-strings
	   (list
	    otter-binary
	    " < "
	    otter-in-filename
	    " | awk '/BEGINNING OF PROOF OBJECT/,/END OF PROOF OBJECT/' > "
	    otter-obj-filename)))

    (format t "~%~%The initial proof object:~%")
    (print initial-proof-object)
    (format t "~%~%Starting Otter search ...~%")
    (finish-output)
    
    (LISP::system unix-command)

    ;; We're supposed to return a proof object.  If Otter didn't produce
    ;; one, we can return either NIL (the empty proof object), or the
    ;; initial proof object.  At this point in the project, it doesn't
    ;; matter which.

    (with-open-file (fp otter-obj-filename)
		    (if (equal (file-length fp) 0)
			nil
		      (read fp)))))

;;------------------------------------------------
;; Function external-modeler takes an initial proof object which
;; represents a set of input clauses.
;;
;; external-modeler is a defstub in the ACL2 code, and this
;; function takes its place.
;;
;; This uses global variables problem-name, mace-binary, and mace-parms.

(defun external-modeler (initial-proof-object)

  (progn

    ;; Problem-name is a global variable, used here for temporary filenames.
    ;; If problem-name is nil, use "mace" instead.

    (setq pname (or problem-name "mace"))
    (setq mace-in-filename (cat-strings (list pname ".in")))
    (setq mace-model-filename (cat-strings (list pname ".model")))

    ;; Build a MACE input file.

    (with-open-file (fp mace-in-filename :direction :output)
		    (format fp "set(build_proof_object_2).~%")
		    (format fp "clear(sigint_interact).~%")
		    (format fp "initial_proof_object(junk).~%")
		    (format fp "~%")
		    (print initial-proof-object fp)
		    (format fp "~%")
		    )

    ;; Run MACE and look for a model in the output.

    (setq system-command
	  (cat-strings
	   (list
	    mace-binary
	    " "
	    mace-in-filename
	    " "
	    mace-parms
	    " | awk '/BEGINNING OF IVY MODEL/,/END OF IVY MODEL/' > "
	    mace-model-filename)))

    (format t "~%~%The input clauses:~%")
    (print initial-proof-object)
    (format t "~%~%Starting MACE search ...~%~%")
    (finish-output)
    
    (LISP::system system-command)

    (with-open-file (fp mace-model-filename)
		    (if (equal (file-length fp) 0)
			nil
		      (read fp)))))
