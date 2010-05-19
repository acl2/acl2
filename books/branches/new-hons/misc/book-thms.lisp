; Utility for finding theorems defined non-redundantly in a file
; Matt Kaufmann
; October, 2007

; This file introduces two utilities, which require that the indicated book
; already be included when running them.

;   (theorems-introduced-in "book-name" state)
;   returns a list of names of all the theorems (i.e. defthm event names) and
;   axioms (i.e., defaxiom event names) introduced in the book or its
;   certifification world (portcullis), not including those introduced in
;   sub-books.

;   (book-thms "book-name" translated-p)
;   is similar to the above, but returns an alist associating names with their
;   formulas (in translated form if translated-p is t, but untranslated if
;   translated-p is nil).

; Thanks to Jared Davis for requesting and trying out this book.

(in-package "ACL2")

(program)

(defun newly-defined-top-level-thms-rec (trips collect-p full-book-name acc
                                               translated-p)

; See newly-defined-top-level-fns-rec in the sources.  Translated-p is true if
; we want translated theorems, else is false.

  (cond ((endp trips)
         acc)
        ((and (eq (caar trips) 'include-book-path)
              (eq (cadar trips) 'global-value)) 
         (newly-defined-top-level-thms-rec (cdr trips)
                                           (equal (car (cddar trips))
                                                  full-book-name)
                                           full-book-name
                                           acc
                                           translated-p))
        ((not collect-p)
         (newly-defined-top-level-thms-rec (cdr trips) nil full-book-name acc
                                           translated-p))
        ((eq (cadar trips) (if translated-p 'theorem 'untranslated-theorem))
         (newly-defined-top-level-thms-rec
          (cdr trips)
          collect-p
          full-book-name
          (acons (caar trips) (cddar trips) acc)
          translated-p))
        (t
         (newly-defined-top-level-thms-rec (cdr trips) collect-p full-book-name
                                          acc translated-p))))

(defun reversed-world-since-boot-strap (wrld acc)
  (cond ((or (endp wrld)
             (let ((trip (car wrld)))
               (and
                (eq (car trip) 'command-landmark)
                (eq (cadr trip) 'global-value)
                (equal (access-command-tuple-form (cddr trip))
                       '(exit-boot-strap-mode)))))
         acc)
        (t (reversed-world-since-boot-strap (cdr wrld)
                                            (cons (car wrld) acc)))))

(defun book-thms-fn (book-name translated-p state)

; This function assumes that book-name has already been included.  Translated-p
; is true if we want translated theorems, else is false.

  (declare (xargs :stobjs state))
  (mv-let
    (full-book-name directory-name familiar-name)
    (parse-book-name (cbd) book-name ".lisp" state) ; (os (w state)) in v3.2.1
    (declare (ignore directory-name familiar-name))
    (newly-defined-top-level-thms-rec
     (reversed-world-since-boot-strap (w state) nil)
      nil
      full-book-name
      nil
      translated-p)))

(defmacro book-thms (book-name translated-p)

; This macro assumes that book-name has already been included.  Translated-p is
; true if we want translated theorems, else is false.

  `(book-thms-fn ,book-name ,translated-p state))

(defun theorems-introduced-in (book-name state)

; This function assumes that book-name has already been included.  Translated-p
; is true if we want translated theorems, else is false.

  (declare (xargs :stobjs state))
  (strip-cars (book-thms-fn book-name t state)))
