;; BOZO copyright stuff.

; h-gc-raw.lisp
;
; This is garbage collection stuff that Jared pulled out of memoize-raw.lisp.
; This probably ought to go into the centaur/books/memory-mgmt-raw book.


(defn looking-at (str1 str2 &key (start1 0) (start2 0))

; (LOOKING-AT str1 str2 :start1 s1 :start2 s2) is non-NIL if and only if string
; STR1, from location S1 to its end, is an initial segment of string STR2, from
; location S2 to its end.

  (unless (typep str1 'simple-base-string)
    (error "looking at:  ~a is not a string." str1))
  (unless (typep str2 'simple-base-string)
    (error "looking at:  ~a is not a string." str2))
  (unless (typep start1 'fixnum)
    (error "looking at:  ~a is not a fixnum." start1))
  (unless (typep start2 'fixnum)
    (error "looking at:  ~a is not a fixnum." start2))

  ;; [Jared]: ugh, we should not care at all about performance here

  (locally
    (declare (simple-base-string str1 str2)
             (fixnum start1 start2))
    (let ((l1 (length str1)) (l2 (length str2)))
      (declare (fixnum l1 l2))
      (loop
       (when (>= start1 l1) (return t))
       (when (or (>= start2 l2)
                 (not (eql (char str1 start1)
                           (char str2 start2))))
         (return nil))
       (incf start1)
       (incf start2)))))

(defn1 meminfo (pat)

; General comment about PROBE-FILE.  PROBE-FILE, according to Gary Byers, may
; reasonably cause an error.  He is undoubtedly right.  In such cases, however,
; Boyer generally thinks and wishes that it returned NIL, and generally,
; therefore, ensconces a PROBE-FILE within an IGNORE-ERROR in his code.

  (or
   (and
    (ignore-errors (probe-file "/proc/meminfo"))
    (with-standard-io-syntax
     (with-open-file (stream "/proc/meminfo")
       (let (line)
         (loop while (setq line (read-line stream nil nil)) do
               (when (looking-at pat line)
                 (return
                  (values
                   (read-from-string line nil nil
                                     :start (length pat))))))))))
   0))

(defn1 physical-memory ()
  (meminfo "MemTotal:"))



(defg *max-mem-usage* (expt 2 32)

  "*MAX-MEM-USAGE* an upper bound, in bytes of memory used, that when
  exceeded results in certain garbage collection actions.")

(defg *gc-min-threshold* (expt 2 30))

#+Clozure
(defn1 set-and-reset-gc-thresholds ()
  (let ((n (max (- *max-mem-usage* (ccl::%usedbytes))
                *gc-min-threshold*)))
    (cond ((not (eql n (ccl::lisp-heap-gc-threshold)))
           (ccl::set-lisp-heap-gc-threshold n)
           )))
  (ccl::use-lisp-heap-gc-threshold)
  (cond ((not (eql *gc-min-threshold*
                   (ccl::lisp-heap-gc-threshold)))
         (ccl::set-lisp-heap-gc-threshold *gc-min-threshold*)
         )))

(defvar *sol-gc-installed* nil)





;          Sol Swords's scheme to control GC in CCL
;
; The goal is to get CCL to perform a GC whenever we're using almost
; all the physical memory, but not otherwise.
;
; The usual way of controlling GC on CCL is via LISP-HEAP-GC-THRESHOLD.
; This value is approximately amount of memory that will be allocated
; immediately after GC.  This means that the next GC will occur after
; LISP-HEAP-GC-THRESHOLD more bytes are used (by consing or array
; allocation or whatever.)  But this means the total memory used by the
; time the next GC comes around is the threshold plus the amount that
; remained in use at the end of the previous GC.  This is a problem
; because of the following scenario:
;
;  - We set the LISP-HEAP-GC-THRESHOLD to 3GB since we'd like to be able
;    to use most of the 4GB physical memory available.
;
;  - A GC runs or we say USE-LISP-HEAP-GC-THRESHOLD to ensure that 3GB
;    is available to us.
;
;  - We run a computation until we've exhausted this 3GB, at which point
;    a GC occurs.
;
;  - The GC reclaims 1.2 GB out of the 3GB used, so there is 1.8 GB
;    still in use.
;
;  - After GC, 3GB more is automatically allocated -- but this means we
;    won't GC again until we have 4.8 GB in use, meaning we've gone to
;    swap.
;
; What we really want is, instead of allocating a constant additional
; amount after each GC, to allocate up to a fixed total amount including
; what's already in use.  To emulate that behavior, we use the hack
; below.  This operates as follows (assuming the same 4GB total physical
; memory as in the above example:)
;
; 1. We set the LISP-HEAP-GC-THRESHOLD to (3.5G - used bytes) and call
; USE-LISP-HEAP-GC-THRESHOLD so that our next GC will occur when we've
; used a total of 3.5G.
;
; 2. We set the threshold back to 1GB without calling
; USE-LISP-HEAP-GC-THRESHOLD.
;
; 3. Run a computation until we use up the 3.5G and the GC is called.
; Say the GC reclaims 1.2GB so there's 2.3GB in use.  1GB more (the
; current LISP-HEAP-GC-THRESHOLD) is allocated so the ceiling is 3.3GB.)
;
; 4. A post-GC hook runs which again sets the threshold to (3.5G -
; used bytes), calls USE-LISP-HEAP-GC-THRESHOLD to raise the ceiling to
; 3.5G, then sets the threshold back to 1GB, and the process repeats.
;
; A subtlety about this scheme is that post-GC hooks runs in a separate
; thread from the main execution.  A possible bug is that in step 4,
; between checking the amount of memory in use and calling
; USE-LISP-HEAP-GC-THRESHOLD, more memory might be used up by the main
; execution, which would set the ceiling higher than we intended.  To
; prevent this, we interrupt the main thread to run step 4.



#+Clozure
(defn1 start-sol-gc ()

; The following settings are highly heuristic.  We arrange that gc
; occurs at 1/8 of the physical memory size in bytes, in order to
; leave room for the gc point to grow (as per
; set-and-reset-gc-thresholds).  If we can determine the physical
; memory; great; otherwise we assume that it it contains at least 4GB,
; a reasonable assumption we think for anyone using the HONS version
; of ACL2.

  (let* ((phys (physical-memory))
         (memsize (cond ((> phys 0) (* phys 1024)) ; to bytes
                        (t (expt 2 32)))))
    (setq *max-mem-usage* (min (floor memsize 8)
                               (expt 2 32)))
    (setq *gc-min-threshold* (floor *max-mem-usage* 4)))

; OLD COMMENT:
; Trigger GC after we've used all but (1/8, but not more than 1 GB) of
; the physical memory.

  (unless *sol-gc-installed*
    (ccl::add-gc-hook
     #'(lambda ()
         (ccl::process-interrupt
          (slot-value ccl:*application* 'ccl::initial-listener-process)
          #'set-and-reset-gc-thresholds))
     :post-gc)
    (setq *sol-gc-installed* t))

  (set-and-reset-gc-thresholds))

#+Clozure
(defn1 set-gc-threshold (bound)
  (when (< (ccl::lisp-heap-gc-threshold) bound)
    (ofv "*hons-init-hook*:  Setting (ccl::lisp-heap-gc-threshold) ~
          to ~:d bytes."
         bound)
    (ccl::set-lisp-heap-gc-threshold bound)
    (ccl::use-lisp-heap-gc-threshold))
  nil)

#+Clozure
(defun maybe-set-gc-threshold (&optional (fraction 1/32))
  (let (n)
    (setq n (physical-memory))
    (cond ((and (integerp n) (> n (* 2 (expt 10 9))))
           (setq n (floor (* n fraction)))
           (set-gc-threshold n)))))



#+Clozure
(defun rwx-size (&optional verbose)

  "(RWX-SIZE) returns two numbers: (a) the number of bytes that are in
  use by the current CCL process, according to Gary Byers, as detailed
  below, and (b) the number of bytes that are not in use by the
  current Lisp process, but that have been merely imagined in secret
  correspondence between CCL and Gnu-Linux.  Do not worry about (b).

  If the optional argument, VERBOSE, is T, then information about
  memory chunks that both contribute to (a) and that exceed
  1 million bytes are printed to *debug-io*."

;; From an email sent by Gary Byers:

;; If you want a meaningful and accurate answer to the question of how
;; much memory the process is using, I don't know of a more accurate
;; or meaningful answer than what you'd get if you looked at each line
;; in the pseudofile

;; /proc/<pid>/maps

;; on Linux (where <pid> is the process ID of the process) and totaled
;; the sizes of each region that was readable, writable, or
;; executable.  The regions are described by lines that look something
;; like:

;; 300040eef000-300042f60000 rwxp 300040eef000 00:00 0
;; 300042f60000-307c00000000 ---p 300042f60000 00:00 0

;; The first of these lines describes a region that's readable (r),
;; writable (w), and executable (x); the second line descibes a much
;; larger region that has none of these attributes.  The first region
;; costs something: we have to have some physical memory in order to
;; read/write/execute the contents of those pages (and if we're low on
;; physical memory the OS might move those contents to swap space, and
;; if this happens a lot we'll see delays like those that you
;; describe.)  It's sometimes said that the first region is
;; "committed" memory (the OS has to commit some real resources in
;; order for you to be able to read and write to it) and the second
;; region isn't committed.

; The following code by Boyer is not to be blamed on Byers.

  (let ((fn (format nil "/proc/~a/maps" (ccl::getpid)))
        (count '?)
        potential
        int1 int2 pos1 pos2 next)
    (with-standard-io-syntax
     (when (ignore-errors (probe-file fn))
       (setq count 0)
       (setq potential 0)
       (with-open-file (s fn)
         (loop while (setq next (read-line s nil nil)) do
               (multiple-value-setq (int1 pos1)
                 (parse-integer next :radix 16 :junk-allowed t))
               (multiple-value-setq (int2 pos2)
                 (parse-integer next :start (1+ pos1)
                                :radix 16 :junk-allowed t))
               (let ((add (- int2 int1)))
                 (cond ((loop for i from (+ pos2 1) to (+ pos2 3)
                              thereis
                              (member (char next i) '(#\r #\w #\x)))
                        (incf count add)
                        (when verbose
                          (format *debug-io*
                                  "~&~a~%adds ~:d"
                                  next (- int2 int1))))
                       (t (incf potential add))))))))
    (when verbose (format *debug-io* "~%(rwx-size)=~:d" count))
    (values count potential)))





(defun acl2h-initialize-gc ()
  ;; called by hons-init-hook

  #+Clozure
  (progn

    ;; It is usually best for the user to know what the garbage collector is
    ;; doing when using HONS and MEMOIZE."

    (unless (equal '(t t) (multiple-value-list (ccl::gc-verbose-p)))
      (ofv "*hons-init-hook*:  Setting CCL's gc to verbose.")
      (ccl::gc-verbose t t))

    ;; CCL's ephemeral gc doesn't seem to work well with honsing and memoizing,
    ;; so we always shut it off.

    (when (ccl::egc-active-p)
      (ofv "*hons-init-hook*:  Turning off CCL's ephemeral gc.")
      (ccl::egc nil))

    ;; Sol Swords's scheme to control GC in CCL.  See long comment in
    ;; h-gc-raw.lisp

    (start-sol-gc)

    ))