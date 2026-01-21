;; Original Author: Yahya Sohail <yahya@yahyasohail.com>

;; This script demonstrates a difference in performance and resource usage
;; between the two bigmem models. It runs a very simple benchmark, writing 1s
;; to random addresses. This is not a book; it can not and is not intended to
;; be certified. Use this script by starting acl2 and setting the `ACL2::MEM`,
;; `ACL2::BENCHMARK`, and `ACL2::N-WRITES` state global variables before
;; loading this script with `LD`.
;;
;; The options for `ACL2::MEM` are
;; :SYMMETRIC  - Use the `BIGMEM::MEM` memory (see xdoc topic bigmem::bigmem).
;; :ASYMMETRIC - Use the `BIGMEM-ASYMMETRIC::MEM` memory (see xdoc topic
;;               BIGMEM-ASYMMETRIC::BIGMEM-ASYMMETRIC).
;; :ATTACHED   - Use `BIGMEM-ASYMMETRIC::MEM` attached to `BIGMEM::MEM`. This
;;               should perform the same as :ASYMMETRIC.
;;
;; The options for `ACL2::BENCHMARK` set the region of memory the random
;; addresses written to should be sampled from. The options are:
;; :LOW  - The 1 GB region starting at address 0
;; :HIGH - The 1 GB region starting at address 6 GB
;;
;; `ACL2::N-WRITES` specifies the number of write operations to perform during
;; the benchmark. It can be any natural number.
;;
;; This script uses `time$` to measure the time necessary to include the
;; symmetric memory model book when `ACL2::MEM` is :SYMMETRIC or :ATTACHED to
;; measure the time necessary for the actual benchmark to run. It prints
;; "(BEGIN|END) (INCLUDING BIGMEM|BENCHMARK)" log messages around the time$
;; output to help identify the time$ output.
;;
;; If using CCL, one can check the heap usage after LDing this script using
;; `CCL::HEAP-UTILIZATION`.
;;
;; Including with this script is a `mem-test.sh` bash script to run all
;; combinations of options and record the time$ output and memory usage.

;; =============================================================================
;; Setup
;; =============================================================================
;; We include the books necessary for our test and define some constants to
;; make it easy to use the specified memory model. We also add a global stobj
;; for whichever stobj we choose to use.

(include-book "centaur/bigmems/bigmem/portcullis" :dir :system)
(include-book "centaur/bigmems/bigmem-asymmetric/portcullis" :dir :system)

(if (or (equal :asymmetric (@ acl2::mem))
        (equal :attached (@ acl2::mem)))
  (include-book "centaur/bigmems/bigmem-asymmetric/bigmem-asymmetric" :dir :system)
  nil)

;; Note: combining this into the previous if in a progn results in an error
;; since the reader can't find the bigmem package
(if (equal :attached (@ acl2::mem))
  (attach-stobj bigmem::mem bigmem-asymmetric::mem)
  nil)

(if (or (equal :symmetric (@ acl2::mem))
        (equal :attached (@ acl2::mem)))
  (time$ (include-book "centaur/bigmems/bigmem/bigmem" :dir :system))
  nil)

(make-event
  `(defconst *mem-pkg* ,(if (or (equal :symmetric (@ acl2::mem))
                                (equal :attached (@ acl2::mem)))
                          "BIGMEM"
                          "BIGMEM-ASYMMETRIC")))

(defconst *mem-stobj*
          (intern$ "MEM" *mem-pkg*))
(defconst *write-mem*
          (intern$ "WRITE-MEM" *mem-pkg*))

(b* ((event (get-event '#.*mem-stobj* (w state)))
     (args (cddr event))
     (non-executable (assoc-keyword :non-executable args))
     ((when (and non-executable
                 (cadr non-executable)))
      (value-triple nil)))
    (remove-global-stobj '#.*mem-stobj* state))

(add-global-stobj '#.*mem-stobj* state)

;; =============================================================================
;; Define benchmark
;; =============================================================================
;; We define the benchmark function, which perform n writes of byte 1 at random
;; addresses in the region that is size bytes large starting at address base.

;; State is used for random$
(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defun random-writes (base size n #.*mem-stobj* state)
    (declare (xargs :stobjs (#.*mem-stobj* state)
                    :guard-hints (("Goal" :in-theory (enable natp-random$ mv-nth)
                                          :use (:instance random$-linear (n size))))
                    :guard-debug t
                    :guard (and (unsigned-byte-p 64 base)
                                (unsigned-byte-p 64 size)
                                (posp size)
                                (unsigned-byte-p 64 (1- (+ base size)))
                                (natp n))))
    (declare (type (unsigned-byte 64) base))
    (declare (type (unsigned-byte 64) size))
    (declare (type (integer 0 *) n))
    (b* (((unless (and (mbt (natp n))
                       (<= 1 n)))
          (mv #.*mem-stobj* state))
         ((mv offset state) (random$ size state))
         (#.*mem-stobj* (#.*write-mem* (+ base offset) 1 #.*mem-stobj*)))
        (random-writes base size (1- n) #.*mem-stobj* state))))

;; =============================================================================
;; Run benchmark
;; =============================================================================
;; We run the benchmark and measure the time it takes.

(b* ((n (@ acl2::n-writes))
     ((list base size)
      (case (@ acl2::benchmark)
        (:low (list 0 (* 1 (expt 2 30))))
        (:high (list (* 6 (expt 2 30)) (* 1 (expt 2 30))))))
     (- (cw "BEGIN BENCHMARK~%"))
     ((mv #.*mem-stobj* state) (time$ (random-writes base size n #.*mem-stobj* state)))
     (- (cw "END BENCHMARK~%")))
    (mv #.*mem-stobj* state))
