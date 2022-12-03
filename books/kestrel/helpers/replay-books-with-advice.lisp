; Replaying many books with proof advice
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: change to HELP package

(include-book "kestrel/helpers/replay-book-with-advice" :dir :system)
(include-book "kestrel/strings-light/string-starts-withp" :dir :system)
(include-book "kestrel/utilities/shuffle-list2" :dir :system)

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

;; Returns (mv erp event state).
(defun replay-books-with-advice-fn-aux (book-to-theorems-alist base-dir n server-url models yes-count no-count maybe-count trivial-count error-count done-book-count state)
  (declare (xargs :mode :program
                  :guard (and (alistp book-to-theorems-alist)
                              (stringp base-dir)
                              (natp n)
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (natp done-book-count))
                  :stobjs state)
           (irrelevant maybe-count) ; since we don't allow :add-hyp
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
                                                        n
                                                        nil ; print
                                                        server-url
                                                        models
                                                        state)))
         ((list book-yes-count book-no-count book-maybe-count book-trivial-count book-error-count) counts)
         (- (and erp (cw "WARNING: Error replaying ~x0.~%" book)))
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
      (replay-books-with-advice-fn-aux (rest book-to-theorems-alist) base-dir n server-url models yes-count no-count maybe-count trivial-count error-count done-book-count state))))

;; Returns (mv erp event state).
;; TODO: Need a way to set and use a random seed?
(defun replay-books-with-advice-fn (book-to-theorems-alist base-dir excluded-prefixes seed n server-url models num-books state)
  (declare (xargs :mode :program
                  :guard (and (alistp book-to-theorems-alist)
                              (stringp base-dir)
                              (string-listp excluded-prefixes)
                              (or (eq :random seed)
                                  (minstd-rand0p seed))
                              (natp n)
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (or (eq :all models)
                                  (help::model-namep models) ; special case for a single model
                                  (help::model-namesp models))
                              (or (eq :all num-books)
                                  (natp num-books)))
                  :stobjs state))
  (b* ( ;; Elaborate options:
       (models (if (eq models :all)
                   help::*known-models*
                 (if (help::model-namep models)
                     (list models) ; single model stands for singleton list of that model
                   models)))
       (book-to-theorems-alist (clear-keys-with-matching-prefixes book-to-theorems-alist excluded-prefixes nil))
       ((mv seed state)
        (if (eq :random seed)
            (random$ *m31* state)
          (mv seed state)))
       (- (cw "Using random seed of ~x0.~%" seed))
       (- (cw "Trying ~x0 recommendations per model set.~%" n)))
    (if (and (not (eq :all num-books))
             (> num-books (len book-to-theorems-alist)))
        (mv :not-enough-books nil state)
      (b* ((shuffled-book-to-theorems-alist (shuffle-list2 book-to-theorems-alist seed))
           (final-book-to-theorems-alist
            (if (eq :all num-books)
                shuffled-book-to-theorems-alist
              (take num-books shuffled-book-to-theorems-alist))))
        (replay-books-with-advice-fn-aux final-book-to-theorems-alist base-dir n server-url models 0 0 0 0 0 0 state)))))

;; TODO: Skip ACL2s stuff (don't even train on it!) since it can't be replayed in regular acl2?
;; TODO: Record the kinds of recs that work (note that names may get combined with /)?
;; Rec names should not include slash or digits?
(defmacro replay-books-with-advice (book-to-theorems-alist ; maps book names (relative to BASE-DIR, with .lisp extension) to lists of defthm names.
                                    base-dir ; no trailing slash
                                    &key
                                    (seed ':random)
                                    (excluded-prefixes 'nil) ; relative to BASE-DIR
                                    (n '10) ; number of recs from each model
                                    (num-books ':all) ; how many books to evaluate (TODO: Better to chose a random subset of theorems, rather than books?)
                                    (server-url 'nil) ; nil means get from environment var
                                    (models ':all) ; which ML models to use
                                    )
  `(make-event (replay-books-with-advice-fn ,book-to-theorems-alist ,base-dir ,excluded-prefixes ,seed ,n ,server-url ,models ,num-books state)))
