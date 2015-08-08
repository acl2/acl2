

;; This code sets up a file that tests whether the axioms of the file
;; firewallworks.lisp are consistent with the axioms introduced in the
;; encapsulates of the files separation.lisp and firewallspec.lisp.

;; It would be better if ACL2 provided this capability directly, but
;; with some sneaky coding we arrange things so that ACL2 checks that
;; the axioms are consistent.

(defun read-forms (ifile)
  (let ((form (read ifile nil nil)))
    (and
     form
     (cons form (read-forms ifile)))))

(defun read-all-forms (file)
  (with-open-file
   (ifile file :direction :input)
   (read-forms ifile)))

;; The forms we need to execute in the consistency test
(defun test-forms ()
  `(
    (include-book "../../../../data-structures/set-theory")
    (ld "separation.lisp")
    (puff :x)
    (ld "firewallspec.lisp")
    (puff :x)

    ;; load all the axioms from the file, changing the axioms to defthms
    ,@(remove nil
	      (mapcar
	       #'(lambda (x)
		   (if (equal (car x) 'defaxiom)
		       `(defthm ,@(cdr x))
		     nil))
	       (read-all-forms "firewallworks.lisp")))
    (ubt! 1)
    (certify-book "consistency-test-passed")))

(defun make-test (file)
  (with-open-file
   (ofile file :direction :output)
   (mapcar #'(lambda (x) (format ofile "~%~S" x)) (test-forms))))


