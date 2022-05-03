(in-package "ACL2")

;;
;; An example showing off the basic use of itest?
;;

(include-book "../top")
(include-book "../acl2s-utils/top")

(in-package "ACL2S")

:q

(import '(acl2s-interface::itest?-query))

;;;
;;; These are some helper functions
;;;

;;; See the definitions of acl2s-query-error?, itest?-query-res-ok?, and itest?-query in acl2-interface-utils.lsp and acl2s-utils/additions.lsp

(defun get-let-binding-value (var binding)
  (let ((pair (assoc var binding)))
    (if (not pair)
        nil
      (cadr pair))))

;;;
;;; Say we want to generate a (possibly improper) list with a certain length.
;;; We can do this by asking test? whether it can find a counterexample to the
;;; statement that "x is a list implies x cannot be of length <l>"
;;;

(defun get-list-of-length (length)
  (when (not (numberp length)) (error "~S is not a number!" length))
  (let ((res (itest?-query `(implies (listp x) (not (equal (len x) ,length))))))
    (if (car res) ;; i.e. if a counterexample was found
        (get-let-binding-value 'x (car (second res)))
      nil)))

(get-list-of-length 0)
(get-list-of-length 1)
(get-list-of-length 5)

;;; Sometimes test? will be able to prove that it can never find a
;;; counterexample to the statement you've given it. Currently you
;;; cannot distinguish this case from the case where test? was not
;;; able to prove that no counterexample exists, but also was not able
;;; to find a counterexample.

;; test? can't find a counterexample to the non-existence of a length 200 list, though one exists.
(get-list-of-length 200)
;; test? is able to prove that no list with length -5 exists.
(get-list-of-length -5)

;;;
;;; Note that this is a little inefficient if we want to generate many
;;; lists of a given length - we make a separate call to itest? for each list.
;;;
;;; Instead, one can ask itest? to generate more counterexamples, and
;;; use them.
;;;

(defun get-lists-of-length (length num-lists)
  (when (not (numberp length)) (error "~S is not a number!" length))
  (let ((res (itest?-query `(implies (listp x) (not (equal (len x) ,length))) :num-counterexamples num-lists)))
    (if (car res)
        (mapcar #'(lambda (ctrex) (get-let-binding-value 'x ctrex)) (second res))
      nil)))

;;;
;;; Asking itest? to generate n counterexamples doesn't mean it will
;;; be able to.
;;; For example, in this case we're asking for 5 lists of length
;;; 0. But only one list of length 0 exists. itest? will try to
;;; produce distinct counterexamples, so in this case it only returns
;;; one.
;;;
(get-lists-of-length 0 5)

;;; Similarly, when we ask for 10 lists of length 5, itest? only generates 2 examples.
(get-lists-of-length 5 10)

;;; In this case it is able to find the desired number of counterexamples.
(get-lists-of-length 1 10)

#|
(defun get-lists-of-length-that-start-with (length start num-lists)
  (when (not (numberp length)) (error "~S is not a number!" length))
  (acl2s-event `(acl2s-defaults :set num-counterexamples ,num-lists))
  (acl2s-event `(acl2s-defaults :set num-print-counterexamples ,num-lists))
  (let ((res (itest?-query `(implies (and (listp x) (consp x) (equal (car x) ,start)) (not (equal (len x) ,length))))))
    (if (car res)
        (mapcar #'(lambda (ctrex) (get-let-binding-value 'x ctrex)) (second res))
      nil)))

(get-lists-of-length-that-start-with 1 3 10)

(get-lists-of-length-that-start-with 8 3 10)

(get-lists-of-length-that-start-with 8 '#\A 10)
|#

;;;
;;; Additionally, note that itest? will sometimes generate
;;; counterexamples that don't satisfy the top level form being
;;; tested.
;;; Currently the information as to which counterexamples are not
;;; consistent is not provided by itest?, but it may be provided in
;;; the future.
;;;
