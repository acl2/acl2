; Copyright (C) 2019 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)

(program)



;; This book includes two utilities, run-events-record-failures and
;; run-events-stop-on-failure, Both take a list of events as input.

;; Run-events-record-failures tries running each event in the list.  For each
;; event that fails, the event form is pushed onto the state global variable
;; acl2::failed-events.  Any events that succeed are recorded.

;; Run-events-stop-on-failure tries running each event in the list until one
;; fails.  The first failing event is saved in the state global variable
;; acl2::failed-event and the previous events that succeeded are recorded.


;; Run an event; if unsuccessful, record its failure:
(defmacro run-and-record-failure (event)
  `(make-event
    '(:or (with-output :stack :pop ,event)
      (make-event
       (b* ((state (f-put-global 'failed-events
                                 (cons ',event (@ failed-events))
                                 state)))
         (value '(value-triple :failed)))))))

;; Do all events even if they fail:
(defun run-and-record-failure-list (events)
  (if (atom events)
      nil
    (cons `(run-and-record-failure ,(car events))
          (run-and-record-failure-list (cdr events)))))

(defmacro run-events-record-failures (events &key
                                          (with-output '(:off :all)))
  (b* ((events (run-and-record-failure-list events)))
    `(with-output
       ,@with-output :stack :push
       (progn
         (make-event
          (b* ((state (f-put-global 'failed-events nil state)))
            (value '(value-triple :invisible))))
         . ,events))))



;; Test correctness of run-events-record-failures
(encapsulate nil
  (logic)
  (local
   (progn
     (make-event
      (if (and (equal (fgetprop 'foo 'formals :none (w state)) :none)
               (equal (fgetprop 'bar 'formals :none (w state)) :none)
               (not (formula 'not-foo nil (w state)))
               (not (formula 'foo-identity nil (w state))))
          (value '(value-triple :ok))
        (er soft 'run-events-record-failures-test
            "Foo, bar, not-foo, and foo-identity should not be defined beforehand!")))

     (with-output
       :off (prove event warning observation error) :gag-mode nil
       (run-events-record-failures
        ((defun foo (x) x)
         (defthm not-foo (not (foo (foo x))))
         (defun bar (x) y)
         (defthm foo-identity (equal (foo (foo x)) (foo x))))
        :with-output (:off :all :on (error))))

     (make-event
      (if (and (equal (@ failed-events)
                      '((defun bar (x) y)
                        (defthm not-foo (not (foo (foo x))))))
               (equal (fgetprop 'bar 'formals :none (w state)) :none)
               (not (formula 'not-foo nil (w state)))
               (equal (fgetprop 'foo 'formals :none (w state)) '(x))
               (formula 'foo-identity nil (w state)))
          '(value-triple :ok)
        (er soft 'run-events-record-failures-test
            "Unexpected result from run-events-record-failures"))))))

;; Test scalability of run-events-record-failures with keep-going=t
(encapsulate nil
  (logic)
  (local
   (progn
     (defun generate-lots-of-identity-fns (n)
       (declare (xargs :mode :program))
       (if (zp n)
           nil
         (cons `(defun ,(intern-in-package-of-symbol
                         (concatenate 'string "FOO"
                                      (coerce (explode-atom n 10) 'string))
                         'foo)
                  (x) x)
               (generate-lots-of-identity-fns (1- n)))))

     (make-event
      `(with-output
         :off (prove event warning observation summary error) :gag-mode nil
         (run-events-record-failures
          ,(generate-lots-of-identity-fns 100)
          :with-output (:off :all :on (error)))))

     (make-event
      (if (and (equal (@ failed-events) nil)
               ;; (equal (@ my-events) nil)
               (equal (formals 'foo100 (w state)) '(x))
               (equal (formals 'foo10 (w state)) '(x)))
          '(value-triple :ok)
        (er soft 'run-events-record-failures-test
            "Unexpected result from run-events-record-failures"))))))
   




   




;; It seems nice in a way to not generate the whole mess of events at once, but
;; rather pull them off of the state global one by one as they are run.  But it
;; turns out this is much slower (when not dominated by the cost of actually
;; running the events).

;; (defun run-events-record-failures-from-global-var-aux-fn (global-var)
;;   `(make-event
;;     (b* ((events (@ ,global-var))
;;          ((when (atom events)) (value '(value-triple :invisible)))
;;          (state (f-put-global ',global-var (cdr events) state))
;;          (event (car events))
;;          (global-var ',global-var))
;;       ,'(value `(progn
;;                   (run-and-record-failure ,event)
;;                   (run-events-record-failures-from-global-var-aux ,global-var))))))

;; (defmacro run-events-record-failures-from-global-var-aux (global-var)
;;   (run-events-record-failures-from-global-var-aux-fn global-var))

;; (defmacro run-events-record-failures-from-global-var (global-var &key (with-output '(:off :all)))
;;   `(with-output ,@with-output :stack :push
;;      (progn
;;        ,'(make-event
;;           (b* ((state (f-put-global 'failed-events nil state)))
;;             (value '(value-triple :invisible))))
;;        (run-events-record-failures-from-global-var-aux ,global-var))))




;; Run event1 and record its failure if it fails; if it succeeds, continue with event2
(defmacro run-and-continue-if-successful (event1 event2)
  `(progn
     (make-event
      (b* ((event ',event1))
        ,'`(:or (with-output :stack :pop ,event)
            (make-event
             (b* ((state (f-put-global 'failed-event ',event state)))
               (value '(value-triple :failed)))))))
     (make-event
      (if (@ failed-event)
          '(value-triple :invisible)
        ',event2))))

(defun run-events-stop-on-failure-fn (events)
  (if (atom events)
      '(value-triple :invisible)
    `(run-and-continue-if-successful
      ,(car events)
      ,(run-events-stop-on-failure-fn (cdr events)))))

(defmacro run-events-stop-on-failure (events &key (with-output '(:off :all)))
  `(with-output ,@with-output :stack :push
     (progn
     ,'(make-event
        (b* ((state (f-put-global 'failed-event nil state)))
          (value '(value-triple :invisible))))
     ,(run-events-stop-on-failure-fn events))))
                                     


;; Test corectness of run-events-stop-on-failure
(encapsulate nil
  (logic)
  (local
   (progn

     (make-event
      (if (and (equal (fgetprop 'foo 'formals :none (w state)) :none)
               (equal (fgetprop 'bar 'formals :none (w state)) :none)
               (not (formula 'not-foo nil (w state)))
               (not (formula 'foo-identity nil (w state))))
          (value '(value-triple :ok))
        (er soft 'run-events-stop-on-failure
            "Foo, bar, not-foo, and foo-identity should not be defined beforehand!")))

     (with-output
       :off (prove event warning observation error) :gag-mode nil
       (run-events-stop-on-failure
        ((defun foo (x) x)
         (defthm not-foo (not (foo (foo x))))
         (defun bar (x) y)
         (defthm foo-identity (equal (foo (foo x)) (foo x))))
        :with-output (:off :all :on (error))))

     (make-event
      (if (and (equal (@ failed-event)
                      '(defthm not-foo (not (foo (foo x)))))
               (equal (formals 'foo (w state)) '(x))
               (not (formula 'foo-identity nil (w state))))
          '(value-triple :ok)
        (er soft 'run-events-stop-on-failure
            "Unexpected result"))))))


;; Test scaling of run-events-stop-on-failure
(encapsulate nil
  (logic)
  (local
   (progn
     (defun generate-lots-of-identity-fns (n)
       (declare (xargs :mode :program))
       (if (zp n)
           nil
         (cons `(defun ,(intern-in-package-of-symbol
                         (concatenate 'string "FOO"
                                      (coerce (explode-atom n 10) 'string))
                         'foo)
                  (x) x)
               (generate-lots-of-identity-fns (1- n)))))

     (make-event
      (b* ((state (f-put-global 'my-events
                                ;; Reduced this to 100 in hopes that it would
                                ;; prevent an SBCL stack overflow of some sort.
                                ;; To test this for real, raise it to 10000.
                                ;; Takes 10-20 sec or so on CCL
                                (generate-lots-of-identity-fns 100)
                                state)))
        (value '(value-triple :invisible))))

     (with-output
       :off (prove event warning observation summary error) :gag-mode nil
       (make-event
        `(run-events-stop-on-failure
          ,(@ my-events)
          :with-output (:off :all :on (error)))))

     (make-event
      (if (and (equal (@ failed-event) nil)
               ;; (equal (@ my-events) nil)
               (equal (formals 'foo100 (w state)) '(x))
               (equal (formals 'foo10 (w state)) '(x)))
          '(value-triple :ok)
        (er soft 'run-events-stop-on-failure-test
            "Unexpected result"))))))

