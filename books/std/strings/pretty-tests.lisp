; An Implementation of Formatted Printing for ACL2
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

#||
(ld ;; for interactive development you'll need this first
 "pretty-tests.acl2")
||#

(in-package "STR")
(include-book "pretty")
(include-book "std/testing/assert" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
;(include-book "tools/plev" :dir :system)
;(include-book "centaur/memoize/old/profile" :dir :system)
(value-triple (acl2::set-max-mem (* 4 (expt 2 30))))

;(make-event (b* (((mv & & state) (acl2::plev-max)))
;              (acl2::value '(value-triple :plev-max))))


(make-event
 (acl2::value
  '(value-triple (cw "~|~%Warning: you seem to be including ~
                      std/strings/pretty-tests.lisp.  You definitely don't ~
                      want to do that!~%")))
 :check-expansion t)


; ----------------------------------------------------------------------------
;
;                     Potential Printer Configurations
;
; ----------------------------------------------------------------------------

(define printconfig-debug ((config printconfig-p))
  (b* (((printconfig cfg) config))
    (list 'printconfig
          :flat-right-margin cfg.flat-right-margin
          :hard-right-margin cfg.hard-right-margin
          :print-base        cfg.print-base
          :print-radix       cfg.print-radix
          :print-lowercase   cfg.print-lowercase
          :home-package      cfg.home-package)))

(defconst *configs0*
  ;; Manually enumerated: all combinations of print-base and radix
  (list (make-printconfig :print-base 10 :print-radix nil)
        (make-printconfig :print-base 10 :print-radix t)
        (make-printconfig :print-base 16 :print-radix nil)
        (make-printconfig :print-base 16 :print-radix t)
        (make-printconfig :print-base 8 :print-radix nil)
        (make-printconfig :print-base 8 :print-radix t)
        (make-printconfig :print-base 2 :print-radix nil)
        (make-printconfig :print-base 2 :print-radix t)))

(defun downcase-configs (configs)
  (if (atom configs)
      nil
    (cons (change-printconfig (car configs) :print-lowercase t)
          (downcase-configs (cdr configs)))))

(defconst *configs1*
  ;; Extend configs with all combinations of downcasing
  (append *configs0* (downcase-configs *configs0*)))

(defun change-home-packages (new-pkg configs)
  (if (atom configs)
      nil
    (cons (change-printconfig (car configs) :home-package new-pkg)
          (change-home-packages new-pkg (cdr configs)))))

(defconst *configs2*
  ;; Extend configs with several base packages
  (append *configs1*
          (change-home-packages (pkg-witness "COMMON-LISP") *configs1*)
          (change-home-packages (pkg-witness "STR") *configs1*)
          (change-home-packages (pkg-witness "AS\\DF!") *configs1*)))

;; (defun change-print-escape (configs)
;;   (if (atom configs)
;;       nil
;;     (cons (change-printconfig (car configs) :print-escape nil)
;;           (change-print-escape (cdr configs)))))

;; (defconst *configs3*
;;   (append *configs2* (change-print-escape *configs2*)))

;; (defun change-print-readably (configs)
;;   (if (atom configs)
;;       nil
;;     (cons (change-printconfig (car configs) :print-readably t)
;;           (change-print-readably (cdr configs)))))

;; (defconst *configs4*
;;   (append *configs3* (change-print-readably *configs3*)))

(defconst *configs* *configs2*)

(define install-config-for-acl2 (config state)
  :mode :program
  (b* (((printconfig config) config)
       (state      (set-print-base config.print-base state))
       (state      (set-print-radix config.print-radix state))
       (state      (set-print-case (if config.print-lowercase
                                       :downcase
                                     :upcase)
                                   state))
       (state      (f-put-global 'acl2::write-for-read t state))
       ;(state      (set-print-readably config.print-readably state))
       ;(state      (set-print-escape config.print-escape state))
       ((mv & & state) (acl2::in-package-fn
                        (symbol-package-name config.home-package)
                        state)))
    state))

(define back-to-normal-config (state)
  :mode :program
  (install-config-for-acl2
   (make-printconfig :home-package (pkg-witness "STR"))
   state))

; ----------------------------------------------------------------------------
;
;                            Testing Objects
;
; ----------------------------------------------------------------------------

(defconst *nats*
  (set::mergesort '(0 1 2 6 7 8 9 10 13 14 15 16 17 63 64 65 99 100 101 1000 12345)))

(defun neg-each (x)
  (if (atom x)
      nil
    (cons (- (car x))
          (neg-each (cdr x)))))

(defconst *negs*
  (neg-each *nats*))

(defun div-by-each (a x)
  (if (atom x)
      nil
    (if (equal (car x) 0)
        (div-by-each a (cdr x))
      (cons (/ a (car x))
            (div-by-each a (cdr x))))))

(defun div-each-by (a x)
  (if (atom x)
      nil
    (if (equal (car x) 0)
        (div-each-by a (cdr x))
      (cons (/ (car x) a)
            (div-each-by a (cdr x))))))

(defconst *rats*
  (set::mergesort
   (append *nats*
           *negs*
           (div-by-each 2 *nats*)
           (div-by-each 5 *nats*)
           (div-by-each 17 *nats*)
           (div-by-each 2 *negs*)
           (div-by-each 3 *negs*)
           (div-by-each 13 *negs*)
           (div-each-by 1 *nats*)
           (div-each-by 3 *nats*)
           (div-each-by 13 *nats*)
           (div-each-by 1 *negs*)
           (div-each-by 3 *negs*)
           (div-each-by 13 *negs*))))

(defun real-plus-each (a x)
  (if (atom x)
      nil
    (cons (complex a (car x))
          (real-plus-each a (cdr x)))))

(defun imag-plus-each (a x)
  (if (atom x)
      nil
    (cons (complex (car x) a)
          (imag-plus-each a (cdr x)))))

(defconst *complexes*
  (set::mergesort
   (append (real-plus-each 0 *rats*)
           (real-plus-each 1 *rats*)
           (real-plus-each -1 *rats*)
           (real-plus-each 17 *rats*)
           (imag-plus-each 0 *rats*)
           (imag-plus-each 1 *rats*)
           (imag-plus-each -1 *rats*)
           (imag-plus-each 17 *rats*))))

(defconst *numbers*
  (set::mergesort
   (append *rats* *complexes*)))

(defun chars (n)
  (if (zp n)
      nil
    (let ((n (- n 1)))
      (cons (code-char n)
            (chars n)))))

(defconst *chars* (chars 256))

(defconst *strings* '("" "a" "b" "c" "foo" "bar" "baz" "hello world" "hello
world" "blah blah"))

(defconst *symbols*
  (set::mergesort
  '(acl2::append acl2::xxxxy acl2::|foo| acl2::|FOO BAR| acl2::|:foo|
    common-lisp::asdf common-lisp::foo common-lisp::|bar| common-lisp::|wingo\|wango!| common-lisp::|:FOO|
    str::abcdefg str::|foo!\|bar| str::|low| str::HIGH str::|:foo|
    |AS\\DF!|::abcd |AS\\DF!|::abcd! |AS\\DF!|::|abcd| |AS\\DF!|::|:FOO|
    :foo :|foo| :|fo\|o| :foo\|bar
    )))

(defconst *atoms*
  (append *strings* *chars* *numbers* *symbols*))

(acl2::defconsts (*real-forms* state)
  ;; Go read some real forms from some books
  (b* (((mv & forms1 state) (acl2::read-file "pretty.lisp" state))
       ((mv & forms2 state) (acl2::read-file "base64.lisp" state))
       ((mv & forms3 state) (acl2::read-file "arithmetic.lisp" state))
       ((mv & forms4 state) (acl2::read-file "case-conversion.lisp" state))
       ((mv & forms5 state) (acl2::read-file "decimal.lisp" state))
       ((mv & forms6 state) (acl2::read-file "hex.lisp" state))
       ((mv & forms7 state) (acl2::read-file "binary.lisp" state)))
    (mv (append forms1 forms2 forms3 forms4 forms5 forms6 forms7)
        state)))

(defconst *objects*
  (append *atoms*
          '((consp x)
            (consp (car x))
            (+ 1 '2 3 (append y z))
            (a . b))
          (list *atoms*)
          (list (reverse *atoms*))
          (pairlis$ *atoms* nil)
          (pairlis$ (reverse *atoms*) *atoms*)
          *real-forms*))


; ----------------------------------------------------------------------------
;
;                        Basic Printing of Atoms
;
; ----------------------------------------------------------------------------

(define princ$-spec ((x atom) state)
  :mode :program
  (b* (((mv channel state) (open-output-channel :string :character state))
       ((unless channel)
        (raise "Failed to create string output channel.")
        (mv nil state))
       (state (princ$ x channel state))
       ((mv erp val state)
        (get-output-stream-string$ channel state))
       ((when erp)
        (raise "Failed to get output stream string.")
        (mv nil state)))
    (mv val state)))

(define test-princ$-atom-on-config (atom config state)
  ;; Assumes config has already been installed into state
  :mode :program
  (b* (((mv spec state) (princ$-spec atom state))
       (impl (rchars-to-string (print-atom atom config nil))))
    (or (equal impl spec)
        (cw "Mismatch ")
        (raise "Mismatch: ~x0.~%"
               (list (cons :object atom)
                     (cons :spec spec)
                     (cons :impl impl)
                     (cons :config (printconfig-debug config)))))
    state))

(define test-princ$-atoms-on-config (atoms config state)
  ;; Assumes config has already been installed into state
  :mode :program
  (if (atom atoms)
      state
    (let ((state (test-princ$-atom-on-config (car atoms) config state)))
      (test-princ$-atoms-on-config (cdr atoms) config state))))

(define test-princ$-atoms-on-configs (atoms configs state)
  :mode :program
  (b* (((when (atom configs))
        (back-to-normal-config state))
       ;; Restore defaults for reliable config printing
       (state (install-config-for-acl2 (make-printconfig) state))
       (- (cw "Testing config ~x0.~%" (printconfig-debug (car configs))))
       (state (install-config-for-acl2 (car configs) state))
       (state (time$ (test-princ$-atoms-on-config atoms (car configs) state))))
    (test-princ$-atoms-on-configs atoms (cdr configs) state)))

(make-event
 (let ((state (time$ (test-princ$-atoms-on-configs *atoms* *configs* state))))
   (acl2::value '(value-triple :success))))


(define prin1$-spec ((x atom) state)
  :mode :program
  (b* (((mv channel state) (open-output-channel :string :character state))
       ((unless channel)
        (raise "Failed to create string output channel.")
        (mv nil state))
       (state (prin1$ x channel state))
       ((mv erp val state)
        (get-output-stream-string$ channel state))
       ((when erp)
        (raise "Failed to get output stream string.")
        (mv nil state)))
    (mv val state)))

(define test-prin1$-atom-on-config (atom config state)
  ;; Assumes config has already been installed into state
  :mode :program
  (b* (((mv spec state) (prin1$-spec atom state))
       (impl (rchars-to-string (print-escaped-atom atom config nil))))
    (or (equal impl spec)
        (raise "Mismatch ~x0."
               (list (cons :object atom)
                     (cons :spec spec)
                     (cons :impl impl)
                     (cons :config (printconfig-debug config)))))
    state))

(define test-prin1$-atoms-on-config (atoms config state)
  ;; Assumes config has already been installed into state
  :mode :program
  (if (atom atoms)
      state
    (let ((state (test-prin1$-atom-on-config (car atoms) config state)))
      (test-prin1$-atoms-on-config (cdr atoms) config state))))

(define test-prin1$-atoms-on-configs (atoms configs state)
  :mode :program
  (b* (((when (atom configs))
        (back-to-normal-config state))
       ;; Restore defaults for reliable config printing
       (state (install-config-for-acl2 (make-printconfig) state))
       (- (cw "Testing config ~x0.~%" (printconfig-debug (car configs))))
       (state (install-config-for-acl2 (car configs) state))
       (state (time$ (test-prin1$-atoms-on-config atoms (car configs) state))))
    (test-prin1$-atoms-on-configs atoms (cdr configs) state)))

(make-event
 (let ((state (time$ (test-prin1$-atoms-on-configs *atoms* *configs* state))))
   (acl2::value '(value-triple :success))))


; ----------------------------------------------------------------------------
;
;                        Object Size Estimation
;
; ----------------------------------------------------------------------------

(define test-obj-size-on-config (obj col max eviscp config state)
  ;; Assumes config has already been installed into state
  :mode :program
  (b* (((printconfig config) config)
       (spec (acl2::flsz1 obj
                          config.print-base
                          config.print-radix
                          col max state
                          eviscp))
       (impl (obj-size obj col max eviscp config))
       (- (or (equal impl spec)
              (raise "Mismatch ~x0."
                     (list (cons :object obj)
                           (cons :spec spec)
                           (cons :impl impl)
                           (cons :col col)
                           (cons :max max)
                           (cons :eviscp eviscp)
                           (cons :config (printconfig-debug config)))))))
    t))

(define test-obj-sizes-on-config (objs col max eviscp config state)
  ;; Assumes config has already been installed into state
  :mode :program
  (if (atom objs)
      t
    (progn$ (test-obj-size-on-config (car objs) col max eviscp config state)
            (test-obj-sizes-on-config (cdr objs) col max eviscp config state))))

(define test-obj-sizes-on-configs (objs col max eviscp configs state)
  :mode :program
  (b* (((when (atom configs))
        (back-to-normal-config state))
       ;; Restore defaults for reliable config printing
       (state (install-config-for-acl2 (make-printconfig) state))
       (- (cw "Testing config ~x0.~%" (printconfig-debug (car configs))))
       (state (install-config-for-acl2 (car configs) state))
       (- (time$ (test-obj-sizes-on-config objs col max eviscp (car configs) state))))
    (test-obj-sizes-on-configs objs col max eviscp (cdr configs) state)))

(comp t)

(make-event
 (let* ((objs *objects*)
        (configs *configs*)
        ;; BOZO reinstate this but we disagree on evisceration-mark stuff
        ;(state (time$ (test-obj-sizes-on-configs objs 0 30 t configs state)))
        ;(state (time$ (test-obj-sizes-on-configs objs 10 15 t configs state)))
        ;(state (time$ (test-obj-sizes-on-configs objs 20 1000 t configs state)))
        (state (time$ (test-obj-sizes-on-configs objs 0 30 nil configs state)))
        (state (time$ (test-obj-sizes-on-configs objs 10 15 nil configs state)))
        (state (time$ (test-obj-sizes-on-configs objs 20 1000 nil configs state))))
   (acl2::value '(value-triple :success))))






; ----------------------------------------------------------------------------
;
;                             PPR
;
; ----------------------------------------------------------------------------

(defmacro trace-ppr1 ()
  `(progn
     (defttag :foo)
     (progn!
      (trace$ (ppr1 :entry (list :my-ppr1
                                 :obj x
                                 :width width
                                 :rpc rpc)
                    :exit (list :my-ppr1
                                :obj acl2::value)))
      (trace$ (ppr1-lst :entry (list :my-ppr1-lst
                                     :obj lst
                                     :width width
                                     :rpc rpc)
                        :exit (list :my-ppr1-lst
                                    :obj acl2::value)))
      (trace$ (acl2::ppr1 :entry (list :acl2-ppr1
                                       :obj acl2::x
                                       :width acl2::width
                                       :rpc acl2::rpc)
                          :exit (list :acl2-ppr1 acl2::value)))
      (trace$ (acl2::ppr1-lst :entry (list :acl2-ppr1-lst
                                           :obj acl2::lst
                                           :width acl2::width
                                           :rpc acl2::rpc)
                          :exit (list :acl2-ppr1-lst acl2::value)))
      )))

(defmacro trace-ppr2 ()
  `(progn
     (defttag :foo)
     (progn!
      (trace$ (acl2::ppr2-column
               :entry (list 'acl2::ppr2-column
                            :lst acl2::lst
                            :loc acl2::loc
                            :col acl2::col)))
      (trace$ (acl2::ppr2
               :entry (list 'acl2::ppr2
                            :obj acl2::x
                            :col acl2::col)))

      (trace$ (acl2::ppr2-flat
               :entry (list 'acl2::ppr2-flat :objs acl2::x)))

      (trace$ (print-column
               :entry (list 'print-column
                            :obj x
                            :loc loc
                            :col col)
               :exit (list 'print-column
                           :acc (rchars-to-string acl2::value))))
      (trace$ (print-instruction
               :entry (list 'print-instruction
                            :obj x
                            :col col)
               :exit (list 'print-instruction
                           :acc (rchars-to-string acl2::value))))

      (trace$ (print-flat-objs
               :entry (list 'print-flat-objs :objs x)
               :exit (list 'print-flat-objs
                           :acc (rchars-to-string acl2::value)))))))


(define ppr-spec (obj col eviscp state)
  :mode :program
  (b* (((mv channel state) (open-output-channel :string :character state))
       ((unless channel)
        (raise "Failed to create string output channel.")
        (mv nil state))
       (state (acl2::ppr obj col channel state eviscp))
       ((mv erp val state)
        (get-output-stream-string$ channel state))
       ((when erp)
        (raise "Failed to get output stream string.")
        (mv nil state)))
    (mv val state)))

(define test-ppr-obj-on-config (obj col config eviscp state)
  ;; Assumes config has already been installed into state
  :mode :program
  (b* (;(- (cw "Checking object ~x0.~%" obj))
       ((mv spec state) (ppr-spec obj col eviscp state))
       (impl (str::rchars-to-string
              (ppr obj col config eviscp nil)))
       (- (or (equal impl spec)
              (raise "Mismatch ~x0."
                     (list (cons :object obj)
                           (cons :spec spec)
                           (cons :impl impl)
                           (cons :col col)
                           (cons :eviscp eviscp)
                           (cons :config (printconfig-debug config)))))))
    state))

(define test-ppr-objs-on-config (objs col config eviscp state)
  ;; Assumes config has already been installed into state
  :mode :program
  (if (atom objs)
      state
    (let ((state (test-ppr-obj-on-config (car objs) col config eviscp state)))
      (test-ppr-objs-on-config (cdr objs) col config eviscp state))))

(define test-ppr-objs-on-configs (objs col configs eviscp state)
  :mode :program
  (b* (((when (atom configs))
        (back-to-normal-config state))
       ;; Restore defaults for reliable config printing
       (state (install-config-for-acl2 (make-printconfig) state))
       (- (cw "Testing config ~x0.~%" (printconfig-debug (car configs))))
       (state (install-config-for-acl2 (car configs) state))
       (state (time$ (test-ppr-objs-on-config objs col (car configs) eviscp state))))
    (test-ppr-objs-on-configs objs col (cdr configs) eviscp state)))

(defmacro do-ppr-test (objs col configs eviscp)
  `(make-event
    (let ((state (test-ppr-objs-on-configs ,objs ,col ,configs ,eviscp state)))
      (acl2::value '(value-triple :success)))))

(defconst *myconfigs*
  ;; a nice config for debugging mismatches
  (list (change-printconfig (car *configs*)
                            :home-package (pkg-witness "STR"))))

(comp t)

(do-ppr-test *atoms* 0 *configs* nil)

(do-ppr-test (pairlis$ *atoms* nil) 0 *configs* nil)

;; Test printing simple 2-element tuples
(do-ppr-test (pairlis$ *atoms* (pairlis$ *atoms* nil)) 0 *configs* nil)

;; Test printing simple improper lists
(do-ppr-test (pairlis$ *atoms* *atoms*) 0 *configs* nil)

(do-ppr-test '((f :key1 val1)
               (f :key1 val1 :key2 val2)
               (f :key1 val1 extra)
               (f some-extra-argument :key1 val1)
               (f some-extra-argument :key1 val1 :key2 val2)
               (f some-extra-argument :key1 val1 extra))
             0 *configs* nil)

(do-ppr-test '((f some-extra-long-argument :key1 val1 extra))
             0 *myconfigs* nil)

(do-ppr-test (list '(this is-a-long-s-expression with-long-arguments))
                         0 (list (change-printconfig (car *configs*)
                                                     :home-package (pkg-witness "STR")))
                         nil)

(do-ppr-test *objects* 0 *configs* nil)

(do-ppr-test (list '(|AS\\DF!|::LOCAL
                     (|AS\\DF!|::DEFTHM
                      |AS\\DF!|::UNSIGNED-BYTE-P-5-WHEN-PRINT-BASE-P
                      (|AS\\DF!|::IMPLIES (|AS\\DF!|::PRINT-BASE-P |AS\\DF!|::X)
                       (|AS\\DF!|::UNSIGNED-BYTE-P 5 |AS\\DF!|::X)))))
             0 *myconfigs* nil)

(do-ppr-test (list '(DEFINE
                      (|AS\\DF!|::MBE :LOGIC (IF (|AS\\DF!|::PRINT-BASE-P |AS\\DF!|::X)
                                                 |AS\\DF!|::X 10)
                       :EXEC x)))
             0 *myconfigs* nil)

(do-ppr-test (list '(|AS\\DF!|::DEFINE
                     |AS\\DF!|::PRINT-BASE-FIX
                     ((|AS\\DF!|::X |AS\\DF!|::PRINT-BASE-P))
                     :RETURNS
                     (|AS\\DF!|::X-FIX |AS\\DF!|::PRINT-BASE-P)
                     :INLINE |AS\\DF!|::T
                     (|AS\\DF!|::MBE :LOGIC (|AS\\DF!|::IF (|AS\\DF!|::PRINT-BASE-P |AS\\DF!|::X)
                                             |AS\\DF!|::X 10)
                      :EXEC |AS\\DF!|::X)
                     |AS\\DF!|::///
                     (|AS\\DF!|::DEFTHM
                      |AS\\DF!|::PRINT-BASE-FIX-WHEN-PRINT-BASE-P
                      (|AS\\DF!|::IMPLIES (|AS\\DF!|::PRINT-BASE-P |AS\\DF!|::X)
                       (|AS\\DF!|::EQUAL (|AS\\DF!|::PRINT-BASE-FIX |AS\\DF!|::X)
                        |AS\\DF!|::X)))))
             0 *myconfigs* nil)

(do-ppr-test
 (list '(DEFINE
          (DEFTHM
             (("Goal" :IN-THEORY (E/D (STR::B64-CHAR-FROM-VALUE UNSIGNED-BYTE-P)
                                      (STR::EQUAL-OF-CHAR-CODE-AND-CONSTANT)))))))
 0 (list (car *configs*)) nil)


#||

; ----------------------------------------------------------------------------
;
;                       Rudimentary performance tests
;
; ----------------------------------------------------------------------------

:q

;; Various timing results.  (CCL Linux-X86-64 AMD FX-8350)

(time (loop for i fixnum from 1 to 10000000 do (acl2::flsz-integer i 10 0)))   ;; 1.486 seconds
(time (loop for i fixnum from 1 to 10000000 do (str::int-size i 10)))          ;; 0.762 seconds

(time (loop for i fixnum from 1 to 10000000 do (acl2::flsz-integer i 2 0)))    ;; 4.742 seconds
(time (loop for i fixnum from 1 to 10000000 do (str::int-size i 2)))           ;; 0.115 seconds

(time (loop for i fixnum from 1 to 10000000 do (acl2::flsz-integer i 8 0)))    ;; 1.669 seconds
(time (loop for i fixnum from 1 to 10000000 do (str::int-size i 8)))           ;; 0.464 seconds

(time (loop for i fixnum from 1 to 10000000 do (acl2::flsz-integer i 16 0)))   ;; 1.244 seconds
(time (loop for i fixnum from 1 to 10000000 do (str::int-size i 16)))          ;; 0.365 seconds

;; This may be a more interesting test, because we really care a lot about small numbers.
(let ((x 1091))
  ;; 6.960 seconds
  (time (loop for i fixnum from 1 to 100000000 do (acl2::flsz-integer x 10 0)))
  ;; 3.528 seconds
  (time (loop for i fixnum from 1 to 100000000 do (str::int-size x 10))))


;; Extremely rudimentary performance comparison.  Looks like we're generally
;; slightly faster than ACL2 here.

(let ((state acl2::*the-live-state*)
      (config (str::make-printconfig :home-package (pkg-witness "STR"))))
  (loop for x in (list 0 300 -848 "foo" #\a #\Newline (expt 2 32)
                       (/ 22 7) (/ (expt 2 32) (1- (expt 2 39)))
                       #c( 100 200)
                       'acl2::append 'acl2::rewrite 'str::trim 'str::asdfasdf)
        do
        (format t "Testing ~a:~%" x)
        (time (loop for i fixnum from 1 to 10000000 do
                    (acl2::flsz-atom x 10 nil 0 state)))
        (time (loop for i fixnum from 1 to 10000000 do
                    (str::atom-size x config)))
        (unless (equal (acl2::flsz-atom x 10 nil 0 state)
                       (str::atom-size x config))
          (error "Mismatch"))))


;; Some tests of atoms: this appears to compare pretty favorably to the ACL2
;; equivalent.  Occasionally it's a bit faster.
(let ((state  acl2::*the-live-state*)
      (config (str::make-printconfig :home-package (pkg-witness "STR")))
      (max    100)
      (eviscp t)
      (termp  t)  ;; apparently relevant only for infix printing
      )
  (loop for x in (list 0 300 -848 "foo" #\a #\Newline (expt 2 32)
                       (/ 22 7) (/ (expt 2 32) (1- (expt 2 39)))
                       #c( 100 200)
                       'acl2::append 'acl2::rewrite 'str::trim 'str::asdfasdf)
        do
        (format t "Testing ~a:~%" x)
        (time (loop for i fixnum from 1 to 10000000 do
                    (acl2::flsz x termp 0 max state eviscp)))
        (time (loop for i fixnum from 1 to 10000000 do
                    (str::obj-size x 0 max eviscp config)))
        (unless (equal (acl2::flsz x termp 0 max state eviscp)
                       (str::obj-size x 0 max eviscp config))
          (error "Mismatch"))))

;; Altogether this seems like a good improvement:
(let ((state  acl2::*the-live-state*)
      (config (str::make-printconfig :home-package (pkg-witness "STR")))
      (max    100)
      (eviscp t)
      (termp  t)  ;; apparently relevant only for infix printing
      )
  (loop for x in '((local (defthm len-when-consp
                            (implies (consp x)
                                     (< 0 (len x)))
                            :rule-classes ((:linear) (:rewrite))))
                   (defthm append-when-not-consp
                     (implies (not (consp x))
                              (equal (append x y)
                                     y))))
        do
        (format t "Testing ~a:~%" x)
        (time (loop for i fixnum from 1 to 100000 do
                    (acl2::flsz x termp 0 max state eviscp)))
        (time (loop for i fixnum from 1 to 100000 do
                    (str::obj-size x 0 max eviscp config)))
        (unless (equal (acl2::flsz x termp 0 max state eviscp)
                       (str::obj-size x 0 max eviscp config))
          (error "Mismatch"))))

(lp)

; let's try to write a more interesting test benchmarking acl2::ppr against
; str::ppr.  we'll try to avoid measuring any channel creation overhead by
; printing lots of objects.

(define acl2-loop-core (objs channel state)
  :mode :program
  (b* (((when (atom objs))
        state)
       (state (acl2::ppr (car objs) 0 channel state nil)))
    (acl2-loop-core (cdr objs) channel state)))

(define acl2-loop-wrapper (n objs channel state)
  :mode :program
  (b* (((when (zp n))
        state)
       (state (acl2-loop-core objs channel state)))
    (acl2-loop-wrapper (- n 1) objs channel state)))

(define acl2-string-test (n objs state)
  :mode :program
  (b* (((mv channel state) (open-output-channel :string :character state))
       ((unless channel)
        (raise "Failed to create string output channel.")
        (mv nil state))
       (state (acl2-loop-wrapper n objs channel state))
       ((mv erp val state)
        (get-output-stream-string$ channel state))
       ((when erp)
        (raise "Failed to get output stream string.")
        (mv nil state)))
    (mv val state)))

(define my-loop-core (objs config acc)
  :mode :program
  (b* (((when (atom objs))
        acc)
       (acc (ppr (car objs) 0 config nil acc)))
    (my-loop-core (cdr objs) config acc)))

(define my-loop-wrapper (n objs config acc)
  :mode :program
  (b* (((when (zp n))
        acc)
       (acc (my-loop-core objs config acc)))
    (my-loop-wrapper (- n 1) objs config acc)))

(define my-string-test (n objs)
  :mode :program
  (let ((acc (my-loop-wrapper n objs *default-printconfig* nil)))
    (str::rchars-to-string acc)))

(acl2-string-test 5 '("hello") state)
(my-string-test 5 '("hello"))


(b* ((n 100)
     (- (gc$))
     ((mv acl2-result state)
      (time$ (acl2-string-test n *real-forms* state)))
     (- (gc$))
     (my-result
      (time$ (my-string-test n *real-forms*))))
  (mv (equal acl2-result my-result)
      state))

; Performance looks really good:
;
;  ACL2 -- 9.71 seconds, 277 MB allocated
;  STR  -- 1.74 seconds, 485 MB allocated
;
; (/ 9.71 1.74) -- looks about 5.5x faster on these forms!

(include-book ;; load up faster version of rchars to string
 "fast-cat")

(b* ((n 100)
     (- (gc$))
     ((mv acl2-result state)
      (time$ (acl2-string-test n *real-forms* state)))
     (- (gc$))
     (my-result
      (time$ (my-string-test n *real-forms*))))
  (mv (equal acl2-result my-result)
      state))

;  ACL2 -- 9.71 seconds, 277 MB allocated
;  STR  -- 1.73 seconds, 414 MB allocated
;
; So that cuts the memory usage by a bit but doesn't do anything for speed.
; Well, good enough.

||#
