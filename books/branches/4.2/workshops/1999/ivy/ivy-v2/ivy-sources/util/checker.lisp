;; This (common lisp) code is used when checking stand-alone proof objects,
;; that is, proof objects found independently from Ivy.

(defun read-rest-of-file (fp)
  (progn (setq x (read fp nil 'end-of-file))
	 (if (eq x 'end-of-file)
	     nil
	   (cons x (read-rest-of-file fp)))))

(defun my-read-file (filename)
  (with-open-file (fp filename)
		  (read-rest-of-file fp)))

(defun check-each-proof-object (prfs)
  (cond ((atom prfs) nil)
	(t (cons (bcheck (car prfs))
		 (check-each-proof-object (cdr prfs))))))

(defun lengths (prfs)
  (cond ((atom prfs) nil)
	(t (cons (length (car prfs))
		 (lengths (cdr prfs))))))

(defun checker (filename)

  (progn

    (format t "~%~%We are checking the proof objects in ~a.~%" filename)

    (setq proof-objects (my-read-file filename))

    (setq lengths (lengths proof-objects))

    (setq results (check-each-proof-object proof-objects))

    (format t "~%There are ~a proof objects.~%" (length proof-objects))
    
    (format t "~%The lengths of the proof objects are ~a.~%" lengths)

    (format t "~%The result of the check is ~a.~%" results)

    (if (member nil results)
	(format t "~%At least one check failed.~%" results)
      (format t "~%All proofs have been checked and are correct!~%" results))

    results))
