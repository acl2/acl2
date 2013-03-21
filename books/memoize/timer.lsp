; Memoize Library
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>
;
; This library is a descendant of the memoization scheme developed by Bob Boyer
; and Warren A. Hunt, Jr. which was incorporated into the HONS version of ACL2,
; sometimes called ACL2(h).

(in-package "MEMOIZE")

; We now develop a simple timing mechanism that uses RDTSC for high-performance
; timing on CCL, or else uses whatever timing utilities are provided by the
; Common Lisp implementation.
;
; The interface here is just:
;
;   (ticks)
;     - similar to get-internal-real-time in Common Lisp, but guaranteed
;       to return an mfixnum
;
;   (ticks-per-second)
;     - similar to internal-time-units-per-second in Common Lisp, but
;       guaranteed to return a float
;
; It would be nice to have a cross-platform, high-performance way to time
; things, and it would be nice if Lisp took care of this for us.  But
; high-performance timing turns out to be a very complicated and subtle matter.
;
; On CCL at least, (get-internal-real-time) is implemented with gettimeofday(),
; which seems basically reasonable but involves a system call and is slow.
; FWIW, gettimeofday() is actually marked as obsolete in Posix.1-2008, with
; clock_gettime() as the recommended replacement.  It also seems like there are
; some efforts to speed this up, e.g., there seems to be some user-space
; equivalent called vgettimeofday(), but I haven't yet found any coherent
; documentation about how to use it.  At any rate, maybe gettimeofday() will be
; faster some day.
;
; In the meantime, clock_gettime() seems to provide a sort of higher-level
; interface to the high-performance counters (e.g., CLOCK_PROCESS_CPUTIME_ID),
; but these would appear to have the same problems as RDTSC.  It would probably
; make sense to switch our code below to use clock_gettime() instead of RDTSC
; if it can be conveniently added to CCL.
;
; But for now we use RDTSC (read timestamp counter).  This is a very fast way
; to get something resembling the current time, but has its own set of
; problems:
;
;  - RDTSC doesn't serialize, so it may read the timestamp before previous
;    instructions have completed.  (This may actually be a feature in that it
;    suggests adding profiling instructions may not slow things down too badly;
;    alternately we could consider using RDTSCP which does serialize, or else
;    the typical trick seems to be to put a CPUID instruction in front of the
;    RDTSC call to force serialization).
;
;  - On some systems, CPU frequency scaling may cause the counter to advance at
;    different rates over time.  This is apparently a particlar problem on the
;    Pentium M.  But on newer processors (Core 2, Phenom, and presumably later)
;    this seems to have been fixed by instead basing the RDTSC on the FSB clock
;    frequency instead of the CPU clock.  So, allegedly on newer systems the
;    RDTSC ticks at a reliable rate even when the clock frequency is scaled
;    back to save power.
;
;  - On a multi-core system, the timestamps on the various cores may not agree.
;    This might cause wildly inaccurate results if the operating system
;    relocates our process from one core to another.  It seems like the whole
;    point of RDTSCP is to let you detect this by also figuring out which CPU
;    you are on, but this seems to require some support from the operating
;    system and it's not clear to me how it's all supposed to work.
;
; On CCL it seems that RDTSC is about 7x faster than (get-internal-real-time).
; CCL actually gives us two ways to use RDTSC:
;
;    (ccl::rdtsc)   -- just returns a fixnum's worth of bits of rdtsc
;    (ccl::rdtsc64) -- returns the full 64 bits (possibly a bignum)
;
; Either of these compiles down to just a few machine instructions instead of
; having to do system calls.  On FV-1, these loops finish in 1.61, 1.57, 11.16,
; and 42.55 seconds, respectively:

;; (progn
;;  (time (loop for i fixnum from 1 to 100000000 do (ccl::rdtsc)))
;;  (time (loop for i fixnum from 1 to 100000000 do (ccl::rdtsc64)))
;;  (time (loop for i fixnum from 1 to 100000000 do (get-internal-real-time)))
;;  (time (loop for i fixnum from 1 to 100000000 do (get-internal-run-time))))

; This works out to about 9 million calls of (get-internal-real-time) per
; second, versus 62 million calls of (ccl::rdtsc).  The better speed of RDTSC
; is pretty appealing since, e.g., the faster we can do timing, the more
; accurately we can handle nested timing.
;
; I wrote a little code to investigate whether these frequency-scaling problems
; have really been resolved.  I first tweaked some loops to provide one
; second's worth of computation.  Here are the loops I came up with for fv-1
; (Xeon e5450) and prime (i5-750).  The timings on fv-1 are very reliable, for
; instance 1.000538, 1.000906, 1.000748, .999290, etc.  The timings on prime
; are much less reliable, often as much as 2 seconds on the first run, but they
; settle down to nearly 1 second each time when it is run in a loop.

;; (defun one-second-on-fv-1 ()
;;   (let ((k 0))
;;     (declare (fixnum k))
;;     (loop for i fixnum from 1 to 9017500 do
;;           (loop for j fixnum from 1 to 153 do
;;                 (incf k)))))
;;
;; (defun one-second-on-prime ()
;;   (let ((k 0))
;;     (declare (fixnum k))
;;     (loop for i fixnum from 1 to 8120000 do
;;           (loop for j fixnum from 1 to 161 do
;;                 (incf k)))))

; I then tried to compare how fast the RDTSC increased while running these
; loops versus sleeping.

;; (let (start end)
;;   (one-second-on-prime)
;;   (setq start (ccl::rdtsc))
;;   (loop for i fixnum from 1 to 100 do (one-second-on-prime))
;;   (setq end (ccl::rdtsc))
;;   (- end start))
;;
;; (let (start end)
;;   (sleep 10)
;;   (setq start (ccl::rdtsc))
;;   (sleep 100)
;;   (setq end (ccl::rdtsc))
;;   (- end start))

; The idea behind this test is that the CPU should be running at high frequency
; when running the first loop, but at low frequency when sleeping.  Even on
; prime (which aggressively throttles), the two forms gave results that were
; within 1.5%.  So this is encouraging -- it seems like indeed frequency
; scaling is unlikely to lead to bad results on these modern processors.
;
; It seems more difficult to try to deal with unreliable timings due to
; changing from one core to another.  If our process is relocated from core A
; to core B, there are two possibilities:
;
;   (1) A's timer is behind B's.  Here, any previous start times we recorded
;       will seem to be farther back in time than they really were, and we may
;       over-estimate how much time something has taken.
;
;   (2) B's timer is behind A's.  Here, any previous start times we recorded
;       will seem either closer in time than they really were, or will seem to
;       be in the future.  We can probably detect these future cases (and do
;       what?  ignore whatever time has elapsed?) but in the other cases we
;       will be silently under-estimating how much time has been taken.
;
; BOZO we should try to investigate how often these relocations occur.  It may
; be that we can detect these cases with something like RDTSCP and at least
; tell the user when the timings we've collected are unreliable.  Alternately,
; we might suggest that the user run "taskset" to set the CPU affinity for
; their ACL2 process if they want more accurate timings.  Hopefully this just
; doesn't happen very often and the timings we collect will be okay.

#+(and Clozure x86_64)
(eval-when
 (:execute :compile-toplevel :load-toplevel)
 (when (fboundp 'ccl::rdtsc)
   (pushnew :memoize-use-rdtsc *features*)))

#-memoize-use-rdtsc
(progn

  (defabbrev ticks ()
    (the mfixnum (logand (get-internal-real-time) most-positive-mfixnum)))

  (defun ticks-per-second ()
    internal-time-units-per-second))

#+memoize-use-rdtsc
(progn

  (defabbrev ticks ()
    (the mfixnum (ccl::rdtsc)))

  (defparameter *ticks-per-second*
    ;; Cached estimate of how many ticks are in a second.  NIL means we haven't
    ;; estimated this yet, otherwise it will be a float.
    ;;
    ;; We estimate this the first time we need it, then record our guess.  We
    ;; do this at runtime, rather than at compile time, because ACL2 is often
    ;; used in networked environments where the same ACL2 image may be running
    ;; on several different machines, each of which have their own tick rates.
    nil)

  (defun estimate-ticks-per-second (sleep-time)
    ;; Simply estimate the number of RDTSC ticks per second by sleeping for a
    ;; little bit and seeing how many RDTSC ticks have elapsed.
    (let* ((start (ccl::rdtsc))
           (end   (progn (sleep sleep-time) (ccl::rdtsc)))
           (ticks (coerce (- end start) 'float)))
      (/ ticks sleep-time)))

; We want to sleep for the shortest time that will give us a reasonably
; accurate guess as to the true number of ticks per second.  As an experiment,
; I estimated the "true" amount of ticks per second on fv-1 by sleeping for 20
; seconds.  Then, I tried using much smaller sleep times, and compared how
; close my guesses were.  Here is the code I used:

;; (defparameter *true-ticks-per-second*
;;   (estimate-ticks-per-second 20))

;; (defun max-error-ticks (times sleep-time)
;;   (if (= times 0)
;;       0
;;     (let* ((est1 (estimate-ticks-per-second sleep-time))
;;            (diff (abs (- est1 *true-ticks-per-second*))))
;;       (max diff (max-error-ticks (1- times) sleep-time)))))

;; (defun max-error-pct (times sleep-time)
;;   (* 100.0 (/ (max-error-ticks times sleep-time) *true-ticks-per-second*)))

;; (max-error-pct 100 .0001) ;; 888.60%
;; (max-error-pct 100 .001)  ;;  98.80%
;; (max-error-pct 100 .01)   ;;   9.89%
;; (max-error-pct 100 .05)   ;;   1.97%
;; (max-error-pct 100 .08)   ;;   1.23%
;; (max-error-pct 100 .1)    ;;   0.98%
;; (max-error-pct 100 .12)   ;;   0.81%
;; (max-error-pct 100 .15)   ;;   0.67%
;; (max-error-pct 100 .2)    ;;   0.49%
;; (max-error-pct 100 .3)    ;;   0.32%
;; (max-error-pct 100 .5)    ;;   0.19%

; In short, it seems like sleeping for .1 seconds gives an estimate that is
; within 1% of the true ticks per second.  It seems like this is probably
; pretty reasonable.

  (defun carefully-estimate-ticks-per-second ()
    ;; Of course, if RDTSC is wacky, maybe this doesn't give us a good number.
    ;; So, try to make sure that we have a least a 1 KHz processor. :)
    (let* ((sleep-time 0.1))
      (loop do
            (setq *ticks-per-second*
                  (estimate-ticks-per-second sleep-time))
            (if (< *ticks-per-second* 1000.0)
                ;; Probably a bogus result, try again, maybe sleeping a bit more.
                (setq sleep-time (* sleep-time 2))
              (loop-finish)))
      *ticks-per-second*))

  (defun ticks-per-second ()
    (or *ticks-per-second*
        (carefully-estimate-ticks-per-second))))
