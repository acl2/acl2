; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "../defrule")
(include-book "std/strings/coerce" :dir :system)
(include-book "std/testing/assert" :dir :system)
(set-state-ok t)
(logic)

(defsection stupid-test-that-defrule-actually-makes-theorems

  (defun is-theorem-p (name state)
    (fgetprop name 'acl2::theorem nil (w state)))

  (assert! (is-theorem-p 'car-cons state))
  (assert! (not (is-theorem-p 'you-should-never-make-a-theorem-with-this-name state)))

  (assert! (not (is-theorem-p 'revappend-when-atom state)))
  (local (defrule revappend-when-atom
           (implies (atom x)
                    (equal (revappend x y)
                           y))))
  (assert! (is-theorem-p 'revappend-when-atom state)))


;; Some tests of rule/defrule with-output handling.  This isn't a proper
;; book because there are some failing events.

(defttag :sys-call)

#!ACL2
(defmacro with-standard-co-and-proofs-co-to-file! (filename form)
  ;; Open-output-channel is broken and doesn't pay attention to writes-ok and
  ;; you can't make it OK no matter what you do.  So, copy and paste
  ;; with-standard-co-and-proofs-co-to-file to get it to use
  ;; open-output-channel!.
  `(mv-let
    (wof-chan state)
    (open-output-channel! ,filename :character state)
    (cond
     ((null wof-chan)
      (er soft 'with-standard-co-and-proofs-co-to-file
          "Unable to open file ~x0 for output."
          ,filename))
     (t
      (pprogn
       (princ$ "-*- Mode: auto-revert -*-" wof-chan state)
       (newline wof-chan state)
       (mv-let (erp val state)
               (state-global-let*
                ((standard-co wof-chan set-standard-co-state)
                 (proofs-co wof-chan set-proofs-co-state))
                (check-vars-not-free
                 (wof-chan)
                 ,form))
               (pprogn (close-output-channel wof-chan state)
                       (cond (erp (silent-error state))
                             (t (value val))))))))))

#!ACL2
(defmacro wof! (filename form) ; Acronym: With Output File
  `(with-standard-co-and-proofs-co-to-file! ,filename ,form))

(defmacro compare-output (event1 event2)
  `(progn
     ;; Run event1 and capture its output
     (make-event (b* ( ;;((mv & & state) (assign writes-ok t))
                      ((mv ?er ?val ?state) (acl2::wof! "defrule.event1.out" ,event1)))
                   (value '(value-triple :invisible))))
     ;; Run event2 and capture its output
     (make-event (b* ( ;;((mv & & state) (assign writes-ok t))
                      ((mv ?er ?val ?state) (acl2::wof! "defrule.event2.out" ,event2)))
                   (value '(value-triple :invisible))))
     ;; Do a diff on their output
     (make-event
      (b* (((mv ?er val state)
            (sys-call+ "sdiff" (list "--width" "170" "defrule.event1.out" "defrule.event2.out") state))
           (state (princ$ (str::implode (make-list 170 :initial-element #\-)) (standard-co state) state))
           (state (newline (standard-co state) state))
           (state (princ$ val (standard-co state) state))
           (state (princ$ (str::implode (make-list 170 :initial-element #\-)) (standard-co state) state))
           (state (newline (standard-co state) state)))
        (value '(value-triple :invisible))))))

(compare-output
 ;; Successful thm versus equivalent "rule" with a top-level enable
 ;; Goal: reasonably identical output.
 ;; Status: GOOD -- only differences are TEMPORARY-RULE versus THM and "Proof succeeded" versus nothing
 (thm (equal (len (append x y)) (+ (len x) (len y)))
      :hints(("Goal" :in-theory (enable append))))
 (rule (equal (len (append x y)) (+ (len x) (len y)))
       :enable append))

(compare-output
 ;; Successful thm versus equivalent "rule" with :hints style enable
 ;; Goal: reasonably identical output.
 ;; Status: GOOD -- only differences are TEMPORARY-RULE versus THM and "Proof succeeded" versus nothing
 (thm (equal (len (append x y)) (+ (len x) (len y)))
      :hints(("Goal" :in-theory (enable append))))
 (rule (equal (len (append x y)) (+ (len x) (len y)))
       :hints(("Goal" :in-theory (enable append)))))

(compare-output
 ;; Failing thm versus equivalent "rule" with top-level :enable hint
 ;; Goal: reasonably equivalent output
 ;; Status: GOOD -- only differences are TEMPORARY-RULE versus THM
 (thm (equal (len (append x y)) (cons (len x) (len y)))
      :hints(("Goal" :in-theory (enable append))))
 (rule (equal (len (append x y)) (cons (len x) (len y)))
       :enable append))

(compare-output
 ;; Failing thm versus equivalent "rule" with :hints style enable
 ;; Goal: reasonably equivalent output
 ;; Status: GOOD -- only differences are TEMPORARY-RULE versus THM
 (thm (equal (len (append x y)) (cons (len x) (len y)))
      :hints(("Goal" :in-theory (enable append))))
 (rule (equal (len (append x y)) (cons (len x) (len y)))
       :hints(("Goal" :in-theory (enable append)))))


(compare-output
 ;; Successful thm versus equivalent "rule" with an extra :prep-books
 ;; Can't really compare to an explicit include-book. (embeddable blah...)
 ;; Goal: not too much extraneous output
 ;; Status: ACCEPTABLE -- we get two include-book summaries instead of just one,
 ;;   one for Form: (include-book ...)
 ;;   one for Form: (progn (include-book ...))
 ;; It'd be nicer not to get the second one, but that's not too horrible.
 (thm (equal (len (append x y)) (+ (len x) (len y)))
      :hints(("Goal" :in-theory (enable append))))
 (rule (equal (len (append x y)) (+ (len x) (len y)))
       :hints(("Goal" :in-theory (enable append)))
       :prep-books ((include-book "arithmetic/top" :dir :system))))

(compare-output
 ;; Including an invalid book versus a "rule" that tries to include an invalid book
 ;; Goal: clear error message without excessive extraneous output
 ;; Status: LOUSY
 ;;   -- we do at least get a clear failure, which is the most important thing
 ;;   -- but the error is printed twice, once for the include-book, once for the progn
 (include-book ;; Newline to fool dependency scanner
  "does-not-exist" :dir :system)
 (rule (equal (len (append x y)) (+ (len x) (len y)))
       :hints(("Goal" :in-theory (enable append)))
       :prep-books ((include-book ;; Newline to fool dependency scanner
                     "does-not-exist" :dir :system))))

(compare-output
 ;; A failing defthm versus a "rule" that has a failing defthm in its prep-lemmas
 ;; Goal: clear error message without extraneous output
 ;; Status: LOUSY
 ;;   -- we do at least get a clear failure, which is the most important thing
 ;;   -- before l0's failure: 8-line message about "to verify that the
 ;;      encapsulated event extends the current theory, we will evaluate it"
 ;;      and telling us what the encapsulated event is.  this is nonsense that
 ;;      the user doesn't care about
 ;;   -- l0 failure itself is just fine
 ;;   -- extra 16 line error message to tell us that the encapsulate has failed
 (defthm l0 (equal (cons x y) (+ x y)))
 (rule (equal (len (append x y)) (+ (len x) (len y)))
       :prep-lemmas ((local (defthm l0 (equal (cons x y) (+ x y)))))))


(encapsulate
  ()
  ;; A thm that violates a theory invariant, versus a rule that does the
  ;; same via a top-level enable
  ;; Goal: clear error message
  ;; Status: GOOD -- clear error message with no extraneous output
  ;;                 actually better than the thm, because it doesn't
  ;;                 produce a useless summary.
  ;;   (previously this produced no output at all!)
  (local (defthm len-of-cdr
           (implies (consp x)
                    (equal (len (cdr x)) (+ -1 (len x))))))
  (local (in-theory (disable len)))
  (local (theory-invariant (incompatible (:definition len) (:rewrite len-of-cdr))))
  (compare-output
   (thm (equal (len (append x y)) (+ (len x) (len y)))
        :hints(("Goal" :in-theory (enable len))))
   (rule (equal (len (append x y)) (+ (len x) (len y)))
         :enable len)))

(encapsulate
  ()
  ;; A thm that violates a theory invariant, versus a rule that does the
  ;; same via a hint enable
  ;; Goal: clear error message without extraneous output
  ;; Status: GOOD -- virtually identical
  (local (defthm len-of-cdr
           (implies (consp x)
                    (equal (len (cdr x)) (+ -1 (len x))))))
  (local (in-theory (disable len)))
  (local (theory-invariant (incompatible (:definition len) (:rewrite len-of-cdr))))
  (compare-output
   (thm (equal (len (append x y)) (+ (len x) (len y)))
        :hints(("Goal" :in-theory (enable len))))
   (rule (equal (len (append x y)) (+ (len x) (len y)))
         :hints(("Goal" :in-theory (enable len))))))

(compare-output
 ;; Successful defthm versus an equivalent defrule with top-level enable
 ;; Goal: reasonably identical output
 ;; Status: GOOD -- identical except perhaps for time taken
 (defthm my-rule
   (equal (len (append x y)) (+ (len x) (len y)))
   :hints(("Goal" :in-theory (enable append))))
 (defrule my-rule
   (equal (len (append x y)) (+ (len x) (len y)))
   :enable append))

(compare-output
 ;; Successful defthm versus equivalent defrule with :hints style enable
 ;; Goal: reasonably identical output
 ;; Status: GOOD -- identical except perhaps for time taken
 (defthm my-rule
   (equal (len (append x y)) (+ (len x) (len y)))
   :hints(("Goal" :in-theory (enable append))))
 (defrule my-rule
   (equal (len (append x y)) (+ (len x) (len y)))
   :hints(("Goal" :in-theory (enable append)))))

(compare-output
 ;; Failed include book versus defrule with failed include book in its prep-books
 ;; Goal: reasonably identical output without extra junk
 ;; Status: LOUSY -- we at least get a good failure, but we print an extra
 ;; 15-line error message due to the progn.
 (include-book ;; Newline to fool dependency scanner
  "does-not-exist" :dir :system)
 (defrule my-rule
   (equal (len (append x y)) (+ (len x) (len y)))
   :hints(("Goal" :in-theory (enable append)))
   :prep-books ((include-book ;; Newline to fool dependency scanner
                 "does-not-exist" :dir :system))))

(compare-output
 ;; Failing proof versus a defrule that has a failing lemma
 ;; Goal: reasonably identical output
 ;; Status: LOUSY
 ;;   -- extra "to verify the encapsulated event" junk
 ;;   -- extra failure messages l0 fails.
 (defthm l0 (equal (cons x y) (+ x y)))
 (defrule my-rule
   (equal (len (append x y)) (+ (len x) (len y)))
   :prep-lemmas ((local (defthm l0 (equal (cons x y) (+ x y)))))))

(encapsulate
  ()
  ;; Failing proof due to theory invariant violation in :prep-lemmas
  ;; Goal: clear error
  ;; Status: GOOD -- clear error message, actually better than a plain
  ;;         in-theory because it doesn't produce a useless summary
  ;;   (previously this produced no output at all!)
  (local (defthm len-of-cdr
           (implies (consp x)
                    (equal (len (cdr x)) (+ -1 (len x))))))
  (local (in-theory (disable len)))
  (local (theory-invariant (incompatible (:definition len) (:rewrite len-of-cdr))))
  (compare-output
   (in-theory (enable len))
   (defrule blah (equal (len (append x y)) (+ (len x) (len y))) :enable len)))
