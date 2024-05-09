; Replaying many books with proof advice
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: change to HELP package

;; NOTE: See eval-models for a similar but newer tool.

(include-book "replay-book-with-advice")
(include-book "kestrel/strings-light/string-starts-withp" :dir :system)
(include-book "kestrel/utilities/shuffle-list2" :dir :system)

(defun cons-with-string-carp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (stringp (car x))))

(defun string<-cars (x1 x2)
  (declare (xargs :guard (and (cons-with-string-carp x1)
                              (cons-with-string-carp x2))))
  (string< (car x1) (car x2)))

(defmergesort merge-sort-string<-of-cadr
  merge-string<-of-cadr
  string<-cars
  cons-with-string-carp
  :extra-theorems nil)

;; Returns (mv cdrs-for-car new-pairs).
(defun cdrs-for-pairs-with-car (car pairs acc)
  (declare (xargs :guard (and (true-listp pairs)
                              (all-cons-with-string-carp pairs)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable all-cons-with-string-carp)))))
  (if (endp pairs)
      (mv (reverse acc) nil)
    (let* ((pair (first pairs))
           (this-car (car pair)))
      (if (not (equal car this-car))
          (mv (reverse acc) pairs)
        (cdrs-for-pairs-with-car car (rest pairs) (cons (cdr pair) acc))))))

;; The PAIRS come in sorted by cars.
(defun group-pairs (pairs acc)
  (declare (xargs :guard (and (true-listp pairs)
                              (all-cons-with-string-carp pairs)
                              (alistp acc))
                  :measure (len pairs)
                  :mode :program ; todo
                  ))
  (if (endp pairs)
      (reverse acc)
    (let* ((pair (first pairs))
           (car (car pair)))
      (mv-let (cdrs new-pairs)
        (cdrs-for-pairs-with-car car (rest pairs) (cons (cdr pair) nil))
        (and (mbt (< (len new-pairs) (len pairs)))
             (group-pairs new-pairs (acons car cdrs acc)))))))

;move
(defun string-starts-any-withp (string prefixes)
  (declare (xargs :guard (and (stringp string)
                              (string-listp prefixes))))
  (if (endp prefixes)
      nil
    (or (string-starts-withp string (first prefixes))
        (string-starts-any-withp string (rest prefixes)))))

(defun clear-keys-with-matching-prefixes (alist prefixes acc)
  (declare (xargs :guard (and (alistp alist)
                              (string-listp (strip-cars alist))
                              (string-listp prefixes)
                              (alistp acc))))
  (if (endp alist)
      (reverse acc)
    (let* ((pair (first alist))
           (key (car pair)))
      (if (string-starts-any-withp key prefixes)
          ;; Drop it:
          (clear-keys-with-matching-prefixes (rest alist) prefixes acc)
        (clear-keys-with-matching-prefixes (rest alist) prefixes (cons pair acc))))))

;; Walks through the BOOK-TO-THEOREMS-ALIST, replaying each book with advice.
;; Returns (mv erp event state).
(defun replay-books-with-advice-fn-aux (book-to-theorems-alist
                                        base-dir
                                        num-recs-per-model
                                        print
                                        model-info-alist
                                        timeout
                                        yes-count no-count maybe-count trivial-count error-count
                                        done-book-count
                                        state)
  (declare (xargs :guard (and (alistp book-to-theorems-alist)
                              (stringp base-dir)
                              (natp num-recs-per-model)
                              (acl2::print-levelp print)
                              (help::model-info-alistp model-info-alist)
                              (natp timeout)
                              (natp yes-count)
                              (natp no-count)
                              (natp maybe-count)
                              (natp trivial-count)
                              (natp error-count)
                              (natp done-book-count))
                  :mode :program
                  :stobjs state)
           ;; (irrelevant maybe-count) ; since we don't allow :add-hyp
           )
  (if (endp book-to-theorems-alist)
      (mv nil '(value-triple :invisible) state)
    (b* ((- (cw "~%======================================================================~%"))
         (entry (first book-to-theorems-alist))
         (book (car entry))
         (theorems-to-try (cdr entry))
         ((mv erp counts state)
          (revert-world (replay-book-with-advice-fn-aux (concatenate 'string base-dir "/" book)
                                                        theorems-to-try
                                                        num-recs-per-model
                                                        nil ; don't spend time trying to improve recs
                                                        print
                                                        model-info-alist
                                                        timeout
                                                        state)))
         (- (and erp (cw "WARNING: Error replaying ~x0.~%" book)))
         ;; Extract the individual counts:
         ((list book-yes-count book-no-count book-maybe-count book-trivial-count book-error-count) counts)
         (yes-count (+ yes-count book-yes-count))
         (no-count (+ no-count book-no-count))
         (maybe-count (+ maybe-count book-maybe-count))
         (trivial-count (+ trivial-count book-trivial-count))
         (error-count (+ error-count book-error-count))
         (done-book-count (+ 1 done-book-count))
         (- (progn$ (cw "~%RUNNING TOTAL after ~x0 books:~%" done-book-count)
                    (cw "ADVICE FOUND    : ~x0~%" yes-count)
                    (cw "NO ADVICE FOUND : ~x0~%" no-count)
                    ;; (cw "ADD HYP ADVICE FOUND : ~x0~%" maybe-count)
                    (cw "NO HINTS NEEDED : ~x0~%" trivial-count)
                    (cw "ERROR           : ~x0~%~%" error-count))))
      (replay-books-with-advice-fn-aux (rest book-to-theorems-alist) base-dir num-recs-per-model print model-info-alist timeout yes-count no-count maybe-count trivial-count error-count done-book-count state))))

;; Returns (mv erp event state).
(defun replay-books-with-advice-fn (tests base-dir excluded-prefixes seed num-recs-per-model print timeout models num-tests state)
  (declare (xargs :guard (and (alistp tests)
                              (string-listp (strip-cars tests))
                              (symbol-listp (strip-cdrs tests))
                              (stringp base-dir)
                              (string-listp excluded-prefixes)
                              (or (eq :random seed)
                                  (minstd-rand0p seed))
                              (natp num-recs-per-model)
                              (acl2::print-levelp print)
                              (natp timeout)
                              (or (eq :all models)
                                  (help::model-namep models) ; special case for a single model
                                  (help::model-namesp models))
                              (or (eq :all num-tests)
                                  (natp num-tests)))
                  :mode :program
                  :stobjs state))
  (b* ( ;; Elaborate options:
       (model-info-alist (help::make-model-info-alist models (w state)))
       ((mv seed state)
        (if (eq :random seed)
            (random$ *m31* state)
          (mv seed state)))
       (- (cw "(Using random seed of ~x0.)~%" seed))
       (- (cw "(Trying ~x0 recommendations per model.)~%" num-recs-per-model))
       (tests (clear-keys-with-matching-prefixes tests excluded-prefixes nil))
       ((when (and (not (eq :all num-tests))
                   (> num-tests (len tests))))
        (mv :not-enough-tests nil state))
       (tests (if (eq :all num-tests)
                  tests
                (take num-tests (shuffle-list2 tests seed))))
       (tests-sorted (merge-sort-string<-of-cadr tests))
       (book-to-theorems-alist (group-pairs tests-sorted nil))
       (book-to-theorems-alist (shuffle-list2 book-to-theorems-alist (minstd-rand0-next seed)))
       (- (cw "(Processing ~x0 tests in ~x1 books.)~%" num-tests (len book-to-theorems-alist)))
       )
    (replay-books-with-advice-fn-aux book-to-theorems-alist base-dir num-recs-per-model print model-info-alist timeout 0 0 0 0 0 0 state)))

;; TODO: Record the kinds of recs that work (note that names may get combined with /)?
;; Rec names should not include slash or digits?
(defmacro replay-books-with-advice (tests ; pairs of the form (book-name . theorem-name) where book-names are relative to BASE-DIR and have the .lisp extension
                                    base-dir ; no trailing slash
                                    &key
                                    (excluded-prefixes 'nil) ; relative to BASE-DIR
                                    (seed ':random)
                                    (n '10) ; num-recs-per-model
                                    (timeout '40) ; for both connection timeout and read timeout
                                    (models ':all) ; which ML models to use
                                    (num-books ':all) ; how many books to evaluate (TODO: Better to chose a random subset of theorems, rather than books?)
                                    (print 'nil)
                                    )
  `(make-event (replay-books-with-advice-fn ,tests ,base-dir ,excluded-prefixes ,seed ,n ,print ,timeout ,models ,num-books state)))
