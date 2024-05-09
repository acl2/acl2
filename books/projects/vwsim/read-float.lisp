
; expt10.lisp

; Copyright (C) 2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; Written by Matt Kaufmann

; This book defines the function read-float, where in raw Lisp, (read-float pos
; str) returns a double-float.  The precondition (guard) is that pos is a
; natural number less than the length of str, pos points to the start of a
; floating-point number, and the first character in str after that number's
; termination is a space.

; I did considerable experimentation to try to get good speed and memory
; performance.  The best improvement was to replace (expt 10 e) by (expt 10.0
; e) for integer exponent e, which for all vwsim was doing reduced the time
; from 7.98 seconds to 2.52 seconds, and memory from 3.6G to 1.3G -- this is
; by improving just the reading of the rec and st-vals stobjs.  But that caused
; noticeable loss of accuracy.  In the running example used here,
; dualRailTest.cir, use of (expt 10.0 e) caused derivative variables to take on
; very different values.  Fortunately, removing the derivative variables causes
; the comparison to succeed even then, as follows -- so maybe it will be deemed
; worthwhile at some point to make this change.

#|
; Could use remove-derivs here, defined in driver.lsp.
(compare-vwsims (loop for x in (strip-cars (cddddr (@ resume-sim1)))
                      when (not (eql (char (symbol-name x) 0) #\!))
                      collect x)
                1/100000000
                (@ resume-sim1)
                (@ full-sim))
|#

; Something still doesn't add up, though.  I counted 5,363,750 calls of
; read-float.  Dividing this by 201.0 yields 26685.  So I did the following:

#|
(defun f () (loop for i from 1 to 26685 do
                  (loop for j from -100 to 100
                        when (zerop (float (* (+ j 101) (expt 10.0d0 j))
                                           0.0d0)) ; always false
                        do (return-from f j))))
(time$ f)
|#

; This resulted in 0.006 seconds of real time.  When I replaced (expt 10.0d0 j)
; by (expt10 j), that ballooned to 1.828 seconds of real time.  But 1.8 seconds
; doesn't nearly account for the full slowdown from 7.98 seconds to 2.52
; seconds.  Maybe there's garbage collection time that I'm missing; anyhow, I'm
; baffled.  I wondered if there's an issue with the use of defabbrev when the
; :inline keyword is present in a defstobj call, but apparently not; see a
; comment in read-rec-ar-1 about the use of defabbrev.

; I wonder if shifting the scale so that the exponent is never negative might
; help.  Consider if we change the experiment above by letting j vary from 1 to
; 100 instead, and using expt10.  One might expect about halft he time of 1.828
; seconds, but it's much less: 0.150 seconds of real time.

; Anyhow....

; By using various features I tried several things, actually (the "rf" prefix
; used below suggests "read-float").  Each of these features should only be set
; when #+raw.  If the first, :rf-cl, is set, then reading is done directly with
; Common Lisp's read-from-string function, so none of the other three features
; below is relevant.  If however :rf-cl is not set, the other three features
; below are relevant.  So there are five experiments to do: one with none of
; these four features set, and one each for each of these four features set.
; Results are reported below.  Here is a short description of each feature's
; effect.

;   :rf-cl
;     Use Common Lisp read-from-string.  Note that this causes -0.0 to be read
;     as -0.0 rather than 0.0.

;   :rf-no-array
;     Use (expt 10 e) instead of (expt10 e)

;   :rf-expt-float
;     Use (expt 10.0d0 e) instead of (expt10 e), as described above

;   :rf-cheat
;     Avoid using expt at all (so, wrong answer, but shows cost of expt)

; Experimental results when used with vwsim are at the end of this file.

; If we decide to pursue this further, we could look at what LispWorks has done
; with parse-float
; (http://www.lispworks.com/documentation/lw51/RNIG/html/readme-377.htm#pgfId-934652)
; or look at the Quicklisp parse-float function
; (https://quickref.common-lisp.net/parse-float.html).

(in-package "ACL2")

(include-book "expt10")
(include-book "std/util/bstar" :dir :system)

(defmacro char-code-0 ()
  (char-code #\0))

; Read-float isn't sufficiently precise in ccl.  See discussion below for the
; effect of pushing :rf-cl onto *features*; in short, it causes the native Lisp
; reader to do the float reading.
#+(and raw (not sbcl))
(push :rf-cl *features*)

#+raw
(declaim (ftype (function ((unsigned-byte 60) string (unsigned-byte 60))
                          (values (unsigned-byte 60) (unsigned-byte 60)))
                read-nat))

(defun read-nat (pos str acc)
  (declare (type (unsigned-byte 60) pos acc)
           (type string str)
           (xargs :guard (< pos (length str))
                  :mode :program))
  (b* (((the character c)
        (the character (char str pos)))
       ((the (signed-byte 60) n)
        (the (signed-byte 60) (- (char-code c) (char-code-0))))
       ((when (or (< n 0) (> n 9)))
        (mv pos acc)))
    (read-nat (the (unsigned-byte 60) (1+ pos))
              str
              (the (unsigned-byte 60) (+ (the (unsigned-byte 60) (* 10 acc))
                                         (the (unsigned-byte 60) n))))))

#+raw
(declaim (ftype (function ((unsigned-byte 60) string)
                          (values (unsigned-byte 60) (signed-byte 60)))
                read-int))

(defmacro the-values (type-lst expr)
  #-raw (declare (ignore type-lst))
  #-raw expr
  #+raw `(the (values ,@type-lst) ,expr))

(defun-inline read-int (pos str)
  (declare (type (unsigned-byte 60) pos)
           (type string str)
           (xargs :guard (< pos (length str))
                  :mode :program))
  (b* (((mv (the (unsigned-byte 60) pos) negp)
        (the-values ((unsigned-byte 60) t)
                    (cond ((eql (char str pos) #\-)
                           (mv (the (unsigned-byte 60) (1+ pos)) t))
                          ((eql (char str pos) #\+)
                           (mv (the (unsigned-byte 60) (1+ pos)) nil))
                          (t (mv pos nil)))))
       ((mv (the (unsigned-byte 60) pos)
            (the (unsigned-byte 60) n))
        (read-nat pos str 0)))
    (mv pos
        (the (unsigned-byte 60)
             (if negp (the (unsigned-byte 60) (- n)) n)))))

(defconst *df-exponents* '(#\e #\E #\d #\D))

#+raw
(declaim (ftype (function ((unsigned-byte 60) string)
                          (values (unsigned-byte 60)
                                  (signed-byte 60)
                                  (signed-byte 60)))
                read-float-1$inline))

(defun-inline read-float-1 (pos str)

; Returns (mv pos n e), where the float is n*10^e.

  (declare (type (unsigned-byte 60) pos)
           (type string str)
           (xargs :guard (< pos (length str))
                  :mode :program))
  (b* (((mv (the (unsigned-byte 60) pos) negp)
        (the-values ((unsigned-byte 60) t)
                    (if (eql (char str pos) #\-)
                        (mv (the (unsigned-byte 60) (1+ pos)) t)
                      (mv pos nil))))
       ((mv (the (unsigned-byte 60) pos) n1)
        (read-nat pos str 0))
       ((mv (the (unsigned-byte 60) pos) dotp)
        (the-values ((unsigned-byte 60) t)
                    (if (eql (char str pos) #\.)
                        (mv (the (unsigned-byte 60) (1+ pos)) t)
                      (mv pos nil))))
       ((mv (the (unsigned-byte 60) pos2)
            (the (unsigned-byte 60) n2))
        (the-values ((unsigned-byte 60) (unsigned-byte 60))
                    (if dotp
                        (read-nat pos str 0)
                      (mv pos 0))))
       ((the (unsigned-byte 60) n2-digits)
        (the (unsigned-byte 60) (- pos2 pos)))
       (exp-p (member-eq (char str pos2) *df-exponents*))
       (- (or dotp
              exp-p
              (er hard 'read-float
                  "Unexpected character at position ~x0 (found neither dot ~
                   nor exponent): ~x1.~|(subseq str (- pos2 10) pos) = ~
                   ~x2~|(subseq str pos (+ pos2 10)) = ~x3~|"
                  pos2
                  (char str pos2)
                  (subseq str
                          (max 0 (- pos2 10))
                          pos2)
                  (subseq str
                          pos2
                          (min (length str) (+ pos2 10))))))
       ((mv (the (unsigned-byte 60) pos3)
            (the (signed-byte 60) exp))
        (the-values ((unsigned-byte 60) (signed-byte 60))
                    (if exp-p
                        (read-int (1+ pos2) str)
                      (mv pos2 0))))
       (- (or (eql (char str pos3) #\Space)
              (er hard 'read-float
                  "Unexpected character at position ~x0 (found neither dot ~
                   nor exponent): ~x1.~|(subseq str (- pos3 10) (+ pos3 10)) = ~
                   ~x2"
                  pos3
                  (char str pos3)
                  (subseq str
                          (max 0 (- pos3 10))
                          (min (length str) (+ pos3 10))))))
       ((the (unsigned-byte 60) n3)
        (the (unsigned-byte 60)
; Note that (expt 10 18) is an (unsigned-byte 60).  However, GCL has generated
; a compiler error if we replace (expt 10 n2-digits) by (the (unsigned-byte 60)
; (expt 10 n2-digits)) below.
             (+ (* (expt 10 n2-digits) n1)
                n2)))
       ((the (signed-byte 60) n)
        (the (signed-byte 60) (if negp (the (signed-byte 60) (- n3)) n3))))
    (mv (the (unsigned-byte 60) (1+ pos3))
        (the (signed-byte 60) n)
        (the (signed-byte 60) (- exp n2-digits)))))

#+raw
(declaim (ftype (function ((unsigned-byte 60) string)
                          (values (unsigned-byte 60) double-float))
                read-float$inline))

#-rf-cl
(defun-inline read-float (pos str)
  (declare (type string str)
           (type (unsigned-byte 60) pos)
           (xargs :mode :program))
  (b* (((mv (the (unsigned-byte 60) pos)
            (the (signed-byte 60) n)
            (the (signed-byte 60) e))
        (read-float-1 pos str)))
    (mv pos
        #+rf-expt-float
        (* n (expt 10.0d0 e))
        #-rf-expt-float
        (let ((val (* n
                      #+rf-no-array (expt 10 e)
                      #+rf-cheat e
                      #-(or rf-no-array rf-cheat) (expt10 e))))
          (declare (type integer val))
          #-raw val #+raw (float val 0.0d0)))))

#+rf-cl
(defun-inline read-float (pos str)
  (declare (type string str)
           (type (unsigned-byte 60) pos)
           (xargs :mode :program))
  (b* (((mv #-raw val #+raw (the double-float val)
            (the (signed-byte 60) pos))
        (read-from-string str t nil :start pos)))
    (mv pos val)))

;;; I used the following commands to test these various approaches for reading
;;; a float.  Explanation and results are shown below these commands.

#|
(ld ; line break to avoid confusing book dependency analysis
 "driver.lsp")

(! input-file "Testing/test-circuits/cirs/dualRailTest.cir")
(! output-save-file
   "Testing/test-circuits/saved-sims/dualRailTest-saved.lisp")

; Skip this except (if necessary) for the first time.
;(!s sim1
;    (vwsim (@ input-file)
;           :time-step (* 1/4 *pico*)
;           :time-stop (* 500 *pico*)
;           :save-sim (@ output-save-file)))

(time$ (vwsim (@ output-save-file)
              :time-stop (* 1000 *pico*)
              :load-sim t
              :save-var 'resume-sim1))

(vwsim (@ input-file)
       :time-step (* 1/4 *pico*)
       :time-stop (* 1000 *pico*)
       :save-var 'full-sim)

; Use equalp instead of equal here because there can be discrepancies due to
; 0.0 vs. -0.0.  Note that equal fails for example if we don't push any
; features (except #+raw).
(equalp (@ resume-sim1) (@ full-sim))

; If this equalp call fails, we use the following.

(load "josim-compare-help.lisp")

(defun compare-vwsims (list-of-names prec vwsim1-result vwsim2-result)
  (if (atom list-of-names)
      t
    (let* ((name (car list-of-names))
           (vwsim1-vals (cdr (assoc-equal name vwsim1-result)))
           (vwsim2-vals (cdr (assoc-equal name vwsim2-result))))
      (if (not (compare vwsim1-vals vwsim2-vals prec))
          (cw "compare-results: Results not the same for ~p0.~%" name)
        (compare-results (cdr list-of-names) prec vwsim1-result vwsim2-result)))))

(compare-vwsims (strip-cars (cddddr (@ resume-sim1)))
                1
                (@ resume-sim1)
                (@ full-sim))

|#

;;; Below are results from the time$ call above, in each case just below:
; (VWSIM (@ OUTPUT-SAVE-FILE) ...) took 
;;; Each of the five cases concludes with a brief summary.

;; No extra features:
; 7.98 seconds realtime, 7.98 seconds runtime
; (3,629,674,048 bytes allocated).
; SUMMARY: This was the best time for which the equalp test (above) succeeded.

;; :q (push :rf-no-array *features*) (lp)
; 8.65 seconds realtime, 8.65 seconds runtime
; (4,024,039,168 bytes allocated).
; SUMMARY: This is a bit worse than above, so it helps to use the expt10
; macro, which uses an array to look up (expt 10 n) for n from -100 to 100.

;; :q (push :rf-expt-float *features*) (lp)
; 2.52 seconds realtime, 2.52 seconds runtime
; (1,341,327,232 bytes allocated).
; SUMMARY: This is much faster, but the equalp test failed and in fact results
; are way off.  The compare-vwsims call above produced the following.
#|
compare: 2.0838891838792506e-6 and -8.451526767316864e-8 are not equal within precision.
compare-results: Results not the same for 
!VRAMPSPPL@0/XBIASC/XMERGET@4/XORFOUR@3.
|#
; It turns out though that the results are only way off for derivative
; variables, as noted earlier in this file (search from the top for
; compare-vwsims).

;; :q (push :rf-cheat *features*) (lp)
; 2.43 seconds realtime, 2.43 seconds runtime
; (1,427,190,064 bytes allocated).
; SUMMARY: as just above, the equalp test failed -- but of course that had to
; be the case, since we cheated by avoiding expt.  The point of this test is to
; show that calling (float (* n e) 0.0d0) instead of (float (* n (expt 10 e))
; 0.0d0) made a huge difference -- and it's much more because of float than
; because of expt.  I know this because I replaced the call of (expt10 e) in
; the no-added-features version of read-float by (my-expt 10 e), and then after
; (ld "driver.lsp"), I evaluated (defun my-expt (x n) (expt x n)) in raw Lisp
; followed by the unchanged definitions of read-rec-ar-1 and read-stv-1
; (necessary because read-float is inlined in those), and profile results
; showed 0.79 seconds for the 5.36e+6 calls of my-expt.  That's not nothing,
; but some of that is because my-expt isn't inlined (so that I could profile
; it), and some may be due to profiling itself -- but more importantly, 0.79 is
; a lot less than the difference between 7.99 seconds without cheating and 2.39
; seconds with cheating.  In summary: the preponderance of that difference,
; which is from removing the expt call, is due to the more expensive call of
; float on the resulting large integer, much more than the integer expt call.
; Anyhow, the compare-vwsims call above produced the following.
#|
compare: 1.9522956211423762e12 and -1.7675048515695393e-4 are not equal within precision.
compare-results: Results not the same for 
VRAMPSPPL@0/XBIASC/XMERGET@4/XORFOUR@3.
|#

;; :q (push :rf-cl *features*) (lp)
; 8.85 seconds realtime, 8.85 seconds runtime
; (3,140,762,768 bytes allocated).
; [Note: Test succeeded with EQUAL, not just EQUALP.]
; SUMMARY: This read-from-string solution actually uses less memory than the
; read-float solution (the one with no added features), but it's a bit slower
; (8.84 seconds vs. 7.99 above).  I don't know why read-float is using more
; memory than read-from-string, but may it's because read-from-string is custom
; coded in C.

; NOTE: I tried the :rf-cl experiment again, but this time evaluating (setq
; *read-eval* nil) after (ld "driver.lsp") but before the time$ call.  It made
; essentially no difference.

; 8.77 seconds realtime, 8.77 seconds runtime
; (3,140,794,224 bytes allocated).
