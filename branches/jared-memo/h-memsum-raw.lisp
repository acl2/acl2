;; BOZO copyright stuff.

; h-memsum-raw.lisp
;
; Memoize summary stuff.

(in-package "ACL2")


#+Clozure
(defg *watch-if-branches-ht* (make-hash-table :test 'eq))

#+Clozure
(defg *watch-if-branches-taken-ht* (make-hash-table :test 'eq))

(declaim (hash-table *watch-if-branches-ht*
                     *watch-if-branches-taken-ht*))





(defn compute-calls-and-times ()
  (let ((ma *memoize-call-array*)
        (2m *2max-memoize-fns*)
        (ca *compute-array*)
        (n (the fixnum (1+ *max-symbol-to-fixnum*))))
    (declare (type (simple-array mfixnum (*)) ma)
             (type (simple-array t (*)) ca)
             (type fixnum 2m n))
    (cond ((eql (length ca) n)
           (loop for i fixnum below n
                 do (setf (aref ca i) nil)))
          (t (setq *compute-array*
                   (make-array n :initial-element nil))
             (setq ca *compute-array*)))
    (loop for i fixnum below (the fixnum (* 2 n))
          do (setf (aref ma i) 0))
    (loop for i fixnum
          from *ma-initial-max-symbol-to-fixnum*
          to *max-symbol-to-fixnum* do
          (let ((2im (the fixnum (* i 2m))))
            (declare (type fixnum 2im))
            (loop for j fixnum
                  from *ma-initial-max-symbol-to-fixnum*
                  to *max-symbol-to-fixnum* do
                  (let* ((2j (the fixnum (* 2 j)))
                         (index (the fixnum (+ 2j 2im))))
                    (declare (type fixnum 2j index))
                    (let ((calls (the mfixnum (aref ma index))))
                      (declare (type mfixnum calls))
                      (when (> calls 0)
                        (let ((time (aref ma (the mfixnum
                                               (1+ index)))))
                          (declare (type mfixnum time))
                          (setf (aref ma 2j)
                                (the mfixnum (+ (aref ma 2j) calls)))
                          (setf (aref ma (the mfixnum (1+ 2j)))
                                (the mfixnum (+ (aref
                                                ma
                                                (the mfixnum (1+ 2j)))
                                               time)))
                          (push i (aref ca j))))))))))
  #+Clozure
  (clrhash *watch-if-branches-ht*)
  #+Clozure
  (clrhash *watch-if-branches-taken-ht*)
  #+Clozure
  (maphash
   (lambda (k v) (declare (ignore k))
     (setf (gethash (cadr v) *watch-if-branches-ht*)
           (+ 2 (or (gethash (cadr v)
                             *watch-if-branches-ht*)
                    0)))
     (setf (gethash (cadr v) *watch-if-branches-taken-ht*)
           (+ (signum (aref *if-true-array* (the fixnum (car v))))
              (signum (aref *if-false-array* (the fixnum (car v))))
              (or (gethash (cadr v)
                           *watch-if-branches-taken-ht*)
                  0))))
   *form-ht*))


(defn1 number-of-calls (x)
  (setq x (coerce-index x))

; One must call COMPUTE-CALLS-AND-TIMES before invoking NUMBER-OF-CALLS to get
; sensible results.

  (aref *memoize-call-array*
        (the mfixnum (* 2 (the mfixnum x)))))


(defn1 total-time (x)

  (setq x (coerce-index x))

; One must call COMPUTE-CALLS-AND-TIMES before invoking TOTAL-TIME to get
; sensible results.

  (/ (aref *memoize-call-array*
           (the fixnum (1+ (the fixnum (* 2 x)))))
     (acl2h-ticks-per-second)))



(defv *report-bytes* t
  "If *REPORT-BYTES* is not NIL, then MEMOIZE-SUMMARY prints the
  number of bytes allocated on the heap.")

(defv *report-calls* t
  "If *REPORT-CALLS* is not NIL, MEMOIZE-SUMMARY prints the number of
  calls.")

(defv *report-calls-from* t
  "If *REPORT-CALLS-FROM* is not NIL, MEMOIZE-SUMMARY prints which
functions called a function, how many times, and how long the calls
took.")

(defv *report-calls-to* t
  "If *REPORT-CALLS-TO* is not NIL, MEMOIZE-SUMMARY prints which
functions were called by given function, how many times, and how long
the calls took.")

(defv *report-hits* t
  "If *REPORT-HITS* is not NIL, MEMOIZE-SUMMARY prints the number of
  times that a previously computed answer was reused.")

(defv *report-mht-calls* t
  "If *REPORT-MHT-CALLS* is not NIL, then MEMOIZE-SUMMARY prints the
  number of times that a memo hash-table for the function was created.
  This may be of interest to those who memoize functions that deal in
  changing stobjs; the memoization machinery sometimes 'forgets' an
  entire memoization hash table out of an abundance of caution, and
  then may later need to create it afresh.")

(defv *report-time* t
  "If *REPORT-TIME* is not NIL, MEMOIZE-SUMMARY prints the total time
  used to compute the outermost calls.")

(defv *report-on-memo-tables* t
  "If *REPORT-ON-MEMO-TABLES* is not NIL, MEMOIZE-SUMMARY prints
  information about memo tables.")

(defv *report-on-pons-tables* t
  "If *REPORT-ON-PONS-TABLES* is not NIL, MEMOIZE-SUMMARY prints
  information about pons tables.")

(defv *report-ifs* t
  "If *REPORT-ON-IFS* is not NIL, information about IF coverage is
  printed for those functions memoized with :WATCH-IFS option T.")


(defn1 memoize-summary ()

  ;; User-Level.  See memoize.lisp.

  "(MEMOIZE-SUMMARY) reports data stored during the execution of the functions
  in (MEMOIZED-FUNCTIONS).

  Typically each call of a memoized function, fn, is counted.  The elapsed time
  until an outermost function call of fn ends, the number of heap bytes
  allocated in that period (CCL only), and other 'charges' are 'billed' to fn.
  That is, quantities such as elapsed time and heap bytes allocated are not
  charged to subsidiary recursive calls of fn while an outermost call of fn is
  running.  Recursive calls of fn, and memoized 'hits', are counted, unless fn
  was memoized with NIL as the value of the :INLINE parameter of MEMOIZE.

  In Clozure Common Lisp, the :WATCH-IFS keyword parameter of MEMOIZE-FN
  determines whether IFs in the body of the function being memoized are
  monitored.

  The settings of the following determine, at the time that MEMOIZE-SUMMARY is
  called, what information is printed:

         *REPORT-BYTES*       boolean   (sensible in CCL only)
         *REPORT-CALLS*       boolean
         *REPORT-CALLS-FROM*  boolean
         *REPORT-CALLS-TO*    boolean
         *REPORT-HITS*        boolean
         *REPORT-MHT-CALLS*   boolean
         *REPORT-TIME*        boolean
         *REPORT-IFS*         boolean

         *REPORT-ON-MEMO-TABLES*   boolean
         *REPORT-ON-PONS-TABLES*   boolean
         *MEMOIZE-SUMMARY-LIMIT*            (or integerp null)
         *MEMOIZE-SUMMARY-ORDER-LIST*       (symbol symbol ... symbol)
         *MEMOIZE-SUMMARY-ORDER-REVERSED*   boolean

  Functions are sorted lexicographically according to the ordering
  induced by the function names in *MEMOIZE-SUMMARY-ORDER-LIST*, each
  member of which must be a unary function that returns a rational.

  The times reported by MEMOIZE-SUMMARY are always elapsed times, that
  is, wall-clock times in seconds, unless 'run-time' is explicitly
  mentioned in the output that WATCH prints.

  (CLEAR-MEMOIZE-TABLES) forgets the remembered values of all memoized
  function calls.  It does not alter a function's status as being a
  memoized function, nor does not it the monitoring data accumulated.

  (UNMEMOIZE-ALL) undoes the memoization status of all memoized
  functions.

  (CLEAR-MEMOIZE-CALL-ARRAY) zeroes out the monitoring information for
  all functions.  It does not alter any function's status as a
  memoized function nor does it change the values remembered for any
  memoized function.

  Here is an example of hacking with *MEMOIZE-SUMMARY-ORDER-LIST* that
  instructs MEMOIZE-SUMMARY to print information about, say,
  1ST-MOD-ERR first:

    (PUSH (LAMBDA (FN)
            (IF (EQ FN '1ST-MOD-ERR) 1 0))
          *MEMOIZE-SUMMARY-ORDER-LIST*)."

  (compute-calls-and-times)
  (memoize-summary-after-compute-calls-and-times)
  nil)



(defg *memoize-summary-order-list*
  '(total-time number-of-calls)

  "*MEMOIZE-SUMMARY-ORDER-LIST* is a raw Lisp variable.  It is a list
  of functions that MEMOIZE-SUMMARY uses to sort all functions that
  are currently memoized in preparation for displaying information
  about them.  The order used is lexicographical, with the first order
  having the most weight.  Each order function takes one argument, a
  symbol, and returns a rational.

  The default is '(total-time number-of-calls).

  Options for the functions include:

     bytes-allocated
     bytes-allocated/call
     event-number
     execution-order
     hits/calls
     number-of-calls
     number-of-hits
     number-of-memoized-entries
     number-of-mht-calls
     symbol-name-order
     time-for-non-hits/call
     time/call
     total-time.
  ")

(defg *memoize-summary-order-reversed* nil

  "*MEMOIZE-SUMMARY-ORDER-REVERSED* is a raw Lisp variable.  When it
  is not NIL, then MEMOIZE-SUMMARY reports on functions in order from
  least to greatest.")


(defn lex-> (l1 l2)
  (cond ((or (atom l1)
             (atom l2))
         nil)
        ((> (car l1) (car l2)) t)
        ((< (car l1) (car l2)) nil)
        (t (lex-> (cdr l1) (cdr l2)))))

(defn1 memoize-summary-sort ()
  (let (pairs)
    (maphash
     (lambda (fn v)
       (when (symbolp fn)
       (let ((num (access memoize-info-ht-entry v :num)))
         (declare (type fixnum num))
         (when (< 0 (number-of-calls num))
           (push (cons fn (loop for order
                                in *memoize-summary-order-list*
                                collect (funcall order fn)))
                 pairs)))))
     *memoize-info-ht*)
    (sort pairs
          (if *memoize-summary-order-reversed*
              (lambda (x y) (lex-> y x))
            #'lex->)
          :key #'cdr)))






(defn short-symbol-name (sym)
  (let ((str    (symbol-name sym))
        (cutoff 30))
    (cond ((> (length str) cutoff)
           (intern (format nil "~a..." (subseq str 0 cutoff))
                   (symbol-package sym)))
          (t sym))))

(defn1 outside-p (x)
  (or (<= x *ma-initial-max-symbol-to-fixnum*)
      (null (gethash x *memoize-info-ht*))))


(defg *sort-to-from-by-calls* nil)

(defn1 memoize-summary-after-compute-calls-and-times ()

;  If COMPUTE-CALLS-AND-TIMES is not called shortly before this
;  function, MEMOIZE-SUMMARY-AFTER-COMPUTE-CALLS-AND-TIMES, is called,
;  the information reported may be quite untimely.

 (let* ((fn-pairs (memoize-summary-sort))
        (ma *memoize-call-array*)
        (len-orig-fn-pairs (len fn-pairs))
        (len-fn-pairs 0)
        (global-total-time 0)
        (global-bytes-allocated 0)
        )
   (declare (type (simple-array mfixnum (*)) ma)
            (type fixnum len-orig-fn-pairs len-fn-pairs))
   (when (and *memoize-summary-limit*
              (> len-orig-fn-pairs *memoize-summary-limit*))
     (setq fn-pairs
           (loop for i fixnum from 1 to *memoize-summary-limit* as
                 x in fn-pairs collect x)))
   (setq len-fn-pairs (len fn-pairs))
   (when (> len-fn-pairs 0)
     (format t "~%Sorted by *memoize-summary-order-list* = ~a."
             *memoize-summary-order-list*)
     (when (< len-fn-pairs len-orig-fn-pairs)
       (format t "~%Reporting on ~:d of ~:d functions because ~
                  *memoize-summary-limit* = ~a."
            len-fn-pairs
            len-orig-fn-pairs
            *memoize-summary-limit*)))
   (setq global-total-time
     (loop for pair in fn-pairs sum (total-time (car pair))))
   (setq global-bytes-allocated
     (+ 1 (loop for pair in fn-pairs sum
                (bytes-allocated (car pair)))))
   (when (null fn-pairs)
     (format t "~%(memoize-summary) has nothing to report.~%"))
   (loop for pair in fn-pairs do
    (let* ((fn (car pair))
           (l (gethash fn *memoize-info-ht*))
           (tablename
            (symbol-value
             (access memoize-info-ht-entry l :tablename)))
           (ponstablename
            (symbol-value
             (access memoize-info-ht-entry l :ponstablename)))
           (start-time
            (the mfixnum
              (symbol-value
               (access memoize-info-ht-entry l :start-time))))
           (num (the fixnum (access memoize-info-ht-entry l :num)))
           (nhits (the mfixnum (number-of-hits num)))
           (nmht (the mfixnum (number-of-mht-calls num)))
           (ncalls
            (the mfixnum (max 1 (the mfixnum (number-of-calls num)))))
           (no-hits (or (not *report-hits*)
                        (null (memoize-condition fn))))
           (bytes-allocated (bytes-allocated num))
           (tt (max .000001 (total-time num)))
           (t/c (time/call num))
           (tnh (time-for-non-hits/call num))
           (in-progress-str
            (if (eql start-time -1) " " ", running, "))
           (selftime tt))
      (declare (type integer start-time)
               (type fixnum num)
               (type mfixnum nhits nmht ncalls bytes-allocated))
      (print-alist
       `((,(ofn "(defun ~s~a~a"
                (short-symbol-name fn)
                (if no-hits
                    (ofn " call~a" (if (eql nhits 1) "" "s"))
                  " hits/calls")
                in-progress-str)
          ,(if (or *report-calls* *report-hits*)
               (if no-hits
                   (ofn "~a" (ofnum ncalls))
                 (ofn "~8,2e/~8,2e = ~4,1f%"
                      nhits
                      ncalls
                      (* 100 (/ nhits (float ncalls)))))
          ""))
         ,@(if (and *report-mht-calls* (>= nmht 2))
               `((" Number of calls to mht" ,(ofnum nmht))))
         ,@(if *report-time*
               `((" Time of all outermost calls"
                  ,(ofn "~a; ~4,1f%"
                        (ofnum tt)
                        (* 100 (/ tt global-total-time))))
                 (" Time per call" ,(ofnum t/c))))

         ,@(if (let ((v (gethash fn *memoize-info-ht*)))
                 (and (null (access memoize-info-ht-entry v
                                    :condition))
                      (null (access memoize-info-ht-entry v
                                    :inline))
                      (< t/c 1e-6)))
               `((,(ofn " Doubtful timing info for ~a." fn)
                  "Heisenberg effect.")))
         ,@(if (and (> bytes-allocated 0) *report-bytes*)
               `((" Heap bytes allocated"
                  ,(ofn "~a; ~4,1f%"
                        (ofnum bytes-allocated)
                        (* 100 (/ bytes-allocated
                                  global-bytes-allocated))))
                 (" Heap bytes allocated per call"
                  ,(ofnum (/ bytes-allocated ncalls)))))
         #+Clozure
         ,@(if (and *report-ifs* (gethash fn *watch-if-branches-ht*))
               `((" IF branch coverage"
                  ,(ofn "~a taken out of ~a"
                        (ofnum (gethash
                                fn *watch-if-branches-taken-ht*))
                        (ofnum (gethash
                                fn *watch-if-branches-ht*))))))
         ,@(if (and *report-hits* *report-time* (not (eql 0 nhits)))
               `((" Time per missed call" ,(ofnum tnh))))
         ,@(if *report-calls-to*
               (let ((l nil)
                     (outside-fn-time 0)
                     (outside-fn-count 0))
                 (declare (type mfixnum outside-fn-count))
                 (loop for callern in
                  (loop for i below (length *compute-array*)
                        when (member num (aref *compute-array* i))
                        collect i) do
                  (let* ((call-loc
                          (the fixnum
                            (+ (* 2 callern)
                               (the fixnum
                                 (* num *2max-memoize-fns*)))))
                         (calls (aref ma call-loc)))
                    (declare (fixnum call-loc)
                             (type mfixnum calls))
                    (let* ((time-loc (the fixnum (1+ call-loc)))
                           (time (aref ma time-loc))
                           (ltt (/ time (acl2h-ticks-per-second))))
                      (decf selftime ltt)
                      (cond ((or (outside-p callern)
                                 (< (* 100 ltt) tt))
                             (incf outside-fn-time ltt)
                             (incf outside-fn-count calls))
                            (t (push
                                `((,(ofn " To ~a"
                                         (fixnum-to-symbol callern))
                                   ,(ofn
                                     "~8,2e calls took~8,2e;~5,1f%"
                                     calls ltt
                                     (if (> (* 10000 ltt) tt)
                                         (* 100 (/ ltt tt))
                                       '?)))
                                  . ,(if *sort-to-from-by-calls*
                                         calls
                                       time))
                                l))))))
                 (when (> outside-fn-time 0)
                   (push
                    `((,(ofn " To other functions")
                       ,(ofn "~8,2e calls took~8,2e;~5,1f%"
                             outside-fn-count
                             outside-fn-time
                             (if (> (* 10000 outside-fn-time) tt)
                                 (* 100 (/ outside-fn-time tt))
                               '?)))
                      . ,(if *sort-to-from-by-calls*
                             outside-fn-count
                           outside-fn-time))
                    l))

                 (when (and (> selftime 0)
                            (not (= selftime tt)))
                   (push `((,(ofn " To self/unprofiled functions")
                            ,(ofn "~8,2e;~5,1f%"
                                  selftime
                                  (if (> (* 10000 selftime) tt)
                                      (* 100 (/ selftime tt))
                                    '?)))
                           . ,(if *sort-to-from-by-calls*
                                  0 ;; ?
                                (* selftime (acl2h-ticks-per-second))))
                         l))
                 (setq l (sort l #'> :key #'cdr))
                 ; (cw "l: ~x0~%" l)
                 (strip-cars l)))
         ,@(if *report-calls-from*
               (let ((l nil)
                     (2num (the fixnum (* 2 num)))
                     (outside-caller-time 0)
                     (outside-caller-count 0))
                 (declare (fixnum 2num))
                 (loop
                  for callern in (aref *compute-array* num) do
                  (let* ((call-loc
                          (the fixnum
                            (+ 2num
                               (the fixnum
                                 (* callern *2max-memoize-fns*)))))
                         (calls (aref ma call-loc)))
                    (declare (fixnum call-loc)
                             (type mfixnum calls))
                    (let* ((time-loc (the fixnum (1+ call-loc)))
                           (time (aref ma time-loc))
                           (ltt (/ time (acl2h-ticks-per-second))))
                      (cond
                       ((or (outside-p callern) (< (* 100 ltt) tt))
                        (incf outside-caller-time ltt)
                        (incf outside-caller-count calls))
                       (t (push
                           `((,(ofn " From ~a"
                                    (fixnum-to-symbol callern))
                              ,(ofn "~8,2e calls took~8,2e;~5,1f%"
                                    calls
                                    ltt
                                    (if (< .001 ltt tt)
                                        (* 100 (/ ltt tt))
                                      '?)))
                             . ,(if *sort-to-from-by-calls*
                                    calls
                                  time))
                           l))))))
                 (when (> outside-caller-time 0)
                   (push
                    `((,(ofn " From other functions")
                       ,(ofn "~8,2e calls took~8,2e;~5,1f%"
                             outside-caller-count
                             outside-caller-time
                             (if (< .001 outside-caller-time tt)
                                 (* 100 (/ outside-caller-time tt))
                               '?)))
                      . ,(if *sort-to-from-by-calls*
                             outside-caller-count
                           outside-caller-time))
                    l))
                 (setq l (sort l #'> :key #'cdr))
                 (strip-cars l)))
             .
         ,(if (and (not *report-on-memo-tables*)
                   (not *report-on-pons-tables*))
              nil
            (let ((spsub 0) (nponses 0) (npsubs 0))
              (declare (type mfixnum spsub nponses npsubs))
              (and
               (and ponstablename *report-on-pons-tables*)
               (maphash
                (lambda (key value)
                  (declare (ignore key))
                  (cond
                   ((not (listp value))
                    (very-unsafe-incf spsub (hash-table-size value)
                                      memoize-summary)
                    (very-unsafe-incf nponses (hash-table-count value)
                                      memoize-summary)
                    (very-unsafe-incf npsubs 1 memoize-summary))
                   (t
                    (very-unsafe-incf nponses (length value)
                                      memoize-summary))))
                ponstablename))
              `(,@(and
                   (and tablename *report-on-memo-tables*)
                   `((,(ofn " Memoize table count/size")
                      ,(ofn "~8,2e/~8,2e = ~4,1f%"
                            (hash-table-count tablename)
                            (hash-table-size tablename)
                            (* 100
                               (/ (hash-table-count tablename)
                                  (hash-table-size tablename)))))))
                  ,@(and
                     (and ponstablename *report-on-pons-tables*)
                     `((" (Pons table count/size"
                        ,(ofn "~:d/~:d = ~4,1f%)"
                              (hash-table-count ponstablename)
                              (hash-table-size ponstablename)
                              (* 100
                                 (/ (hash-table-count ponstablename)
                                    (hash-table-size ponstablename)))))
                       (" (Number of pons sub tables"
                        ,(ofn "~a)" (ofnum npsubs)))
                       (" (Sum of pons sub table sizes"
                        ,(ofn "~a)" (ofnum spsub)))
                       (" (Number of ponses"
                        ,(ofn "~a)" (ofnum nponses)))))))))
       5))
         (format t ")"))))