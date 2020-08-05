; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
; sexpr-loop-debug.lisp
;   Original author: Jared Davis <jared@centtech.com>
;   Code for debugging apparent combinational loops for sexpr-fixpoint.

(in-package "ACL2")
(include-book "sexpr-fixpoint")
(include-book "centaur/esim/vltoe/emodwire" :dir :system)
(include-book "centaur/vl2014/util/cw-unformatted" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))


; This file is a plug-in debugging mechanism for loops in the sexpr-fixpoint
; algorithm.  We exploit sneaky-save and sneaky-load to make it possible to
; debug loops without complicating the logical story of sexpr-fixpoint.
;
; Roughly, when SEXPR-DFS optimizes the list of s-expressions and tries to
; topologically sort them, it saves the loops it has found in
;
;    :SEXPR-LOOP-DEBUG-LOOPS
;
; But practically speaking these loops are hard to read because they are just
; lists of numbers.  That is, SEXPR-DFS works on "translated" sexprs, where the
; variables have been replaced by numbers so that we can use faster variable
; gathering routines.  So the loops are in terms of numbers that have nothing
; to do with the input variables.
;
; To make sense of these loops, we also save the INV-VARMAP (an alist mapping
; the numbers back to the original signal names) in
;
;    :SEXPR-LOOP-DEBUG-INV-VARMAP
;
; This varmap lets us translate the loops we have found back in terms of the
; original sexpr vars.

(defun translate-loops (loops inv-varmap)
  ;; Use the INV-VARMAP to turn the loops from lists of numbers into lists
  ;; of proper sexpr variables.
  (declare (xargs :guard t))
  (if (atom loops)
      nil
    (cons (fal-extract-vals (car loops) inv-varmap)
          (translate-loops (cdr loops) inv-varmap))))

(defun find-first-relevant-loop (sig-num loops)
  ;; Just find the first loop that mentions this signal.
  ;;  - SIG-NUM is a number (i.e., not a proper sexpr var)
  ;;  - LOOPS are the untranslated loops
  (declare (xargs :guard t))
  (cond ((atom loops)
         nil)
        ((gentle-member-equal sig-num (car loops))
         (car loops))
        (t
         (find-first-relevant-loop sig-num (cdr loops)))))

(defun find-all-relevant-loops (sig-num loops)
  ;; Find all the loops that mention this signal.
  ;;  - SIG-NUM is a number (i.e., not a proper sexpr var)
  ;;  - LOOPS are the untranslated loops
  (declare (xargs :guard t))
  (cond ((atom loops)
         nil)
        ((gentle-member-equal sig-num (car loops))
         (cons (car loops) (find-all-relevant-loops sig-num (cdr loops))))
        (t
         (find-all-relevant-loops sig-num (cdr loops)))))

(defsection len-sort

  ;; Sort lists so that the shortest ones come first.

  (local (include-book "arithmetic-3/top" :dir :system))

  (defun shorter-p (x y)
    (declare (xargs :guard t))
    (mbe :logic (< (len x) (len y))
         :exec
         (cond ((atom x)
                (consp y))
               ((atom y)
                nil)
               (t
                (shorter-p (cdr x) (cdr y))))))

  (defthm shorter-p-transitive
    (implies (and (shorter-p x y)
                  (shorter-p y z))
             (shorter-p x z)))

  (defsort :compare< shorter-p
           :prefix len))



; Figuring out the Verilog signals that give rise to a loop.
;
; The following code basically assumes that the sexpr vars we're trying to
; reach a fixpoint for are VL emodwires.  This is probably a reasonable
; assumption if we're using ESIM to simulate modules produced by VL.
;
; What are we trying to do here?  Well, if ESIM is getting bogged down in
; apparent combinational loops, probably you need to install a custom function
; into ESIM-SIMPLIFY-UPDATE-FNS that will shannon-expand the clocks signals
; that are controlling certain latches so that the loop will go away.  The
; biggest problem is figuring out why there seems to be a loop and what we need
; to expand to break it.
;
; The loops that we're going to find in the course of our topological sort are
; all going to be in terms of ESIM wires, but they can have just gobs of signals
; because typically you have a loop like:
;
;    main inputs         +---- feedback
;             |          |   |
;          \---------------/ |
;           \     mux     /  |
;            \-----------/   |
;                  |         |
;              +-------+     |
;    clk --+---| LATCH |     |
;          |   +-------+     |
;          |       |         |
;          |    Do Stuff     |
;          |       |         |
;          |   +-------+     |
;          +--o| LATCH |     |
;              +-------+     |
;                  |         |
;                Result ------
;                  |
;
; And if the busses involved are wide then you can end up with basically all of
; the bits of each wire involved taking part in the loop.  This is too much
; stuff to look at.
;
; So what I want to do is basically collapse the loops down and just talk about
; Verilog wires instead of bits.  Beyond that, I want to make the output to be
; easy to plug into the module browser's wireview tool so you can just go and
; visualize the loop without having to do anything but copy and paste it into
; wireview.

#!STR
(defsection strjoin

  ;; BOZO move to string library

  (defun strjoin-aux (separator x acc)
    (declare (xargs :guard (and (stringp separator)
                                (string-listp x))))
    (cond ((atom x)
           acc)
          ((atom (cdr x))
           (str::revappend-chars (car x) acc))
          (t
           (let* ((acc (str::revappend-chars (car x) acc))
                  (acc (str::revappend-chars separator acc)))
             (strjoin-aux separator (cdr x) acc)))))

  (defthm character-listp-of-strjoin-aux
    (implies (character-listp acc)
             (character-listp (strjoin-aux separator x acc)))
    :hints(("Goal" :in-theory (enable strjoin-aux))))

  (defun strjoin (separator x)
    (declare (xargs :guard (and (stringp separator)
                                (string-listp x))))
    (reverse (coerce (strjoin-aux separator x nil) 'string))))

(defund verilog-loop-from-translated-loop (x)
  (declare (xargs :guard t))
  (if (vl2014::vl-emodwirelist-p x)
      (set::mergesort (vl2014::vl-emodwirelist->basenames x))
    (cw "Oops, loop contains mal-formed signals, not trying to convert
         it into Verilog.  ~x0.~%" x)))

(defthm string-listp-of-verilog-loop-from-translated-loop
  (string-listp (verilog-loop-from-translated-loop x))
  :hints(("Goal" :in-theory (enable verilog-loop-from-translated-loop))))

(defun verilog-loops-from-translated-loops-aux (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (verilog-loop-from-translated-loop (car x))
          (verilog-loops-from-translated-loops-aux (cdr x)))))

(defthm string-list-listp-of-verilog-loops-from-translated-loops-aux
  (vl2014::string-list-listp (verilog-loops-from-translated-loops-aux x))
  :hints(("Goal" :in-theory (enable verilog-loops-from-translated-loops-aux))))

(defun verilog-loops-from-translated-loops (x)
  (declare (xargs :guard t))
  (set::mergesort (remove-equal nil (verilog-loops-from-translated-loops-aux x))))

(defthm string-list-listp-of-verilog-loops-from-translated-loops
  (vl2014::string-list-listp (verilog-loops-from-translated-loops x))
  :hints(("Goal" :in-theory (enable verilog-loops-from-translated-loops))))

(defund comma-strings-from-verilog-loops (x)
  (declare (xargs :guard (vl2014::string-list-listp x)))
  (if (atom x)
      nil
    (cons (str::strjoin "," (car x))
          (comma-strings-from-verilog-loops (cdr x)))))

(defthm string-listp-of-comma-strings-from-verilog-loops
  (implies (vl2014::string-list-listp x)
           (string-listp (comma-strings-from-verilog-loops x)))
  :hints(("Goal" :in-theory (enable comma-strings-from-verilog-loops))))

(defun verilog-summarize-translated-loops-aux (n comma-strs)
  (declare (xargs :guard (and (natp n)
                              (string-listp comma-strs))))
  (if (atom comma-strs)
      nil
    (progn$
     (cw "Loop ~x0: " n)
     (vl2014::cw-unformatted (car comma-strs)) ;; so it all prints on one line
     (cw "~%")
     (verilog-summarize-translated-loops-aux (+ 1 n) (cdr comma-strs)))))

(defthm
   vl2014::string-list-listp-of-len-sort
   (iff (vl2014::string-list-listp (len-sort x))
        (vl2014::string-list-listp x))
   :hints
   (("goal" :in-theory (disable vl2014::string-list-listp-when-subsetp-equal)
            :use ((:instance vl2014::string-list-listp-when-subsetp-equal
                             (y (len-sort x)))
                  (:instance vl2014::string-list-listp-when-subsetp-equal
                             (x (len-sort x))
                             (y x))))))

(defund verilog-summarize-translated-loops (x)
  (declare (xargs :guard t))
  (b* ((loops (verilog-loops-from-translated-loops x))
       (loops (len-sort loops))
       ((unless (vl2014::string-list-listp loops))
        (er hard? 'verilog-summarize-translated-loops
            "Jared thinks this is impossible."))
       (strs  (comma-strings-from-verilog-loops loops)))
    (cw "Verilog-level Summary of Possible Loops:~%~%")
    (verilog-summarize-translated-loops-aux 1 strs)
    (cw "~%~%")))



(defconst *max-sneaky-debug-loops* 5)


(defun jared-sneaky-loop-debug-mutator (stored-vals ignored)
  (declare (ignorable ignored)
           (xargs :guard t))
  ; See sneaky-mutate.  This is a mutator.  We expect that stored-vals should
  ; be a list of the form (loops inv-varmap).
  (b* (((unless (tuplep 2 stored-vals))
        (er hard? 'sneaky-loop-debug-mutator
            "Expected stored-vals to have the form (loops inv-varmap), found ~x0."
            stored-vals))
       ((list loops inv-varmap) stored-vals)
       ((unless loops)
        ;; Common case: there are no loops in this module, so don't do anything.
        nil)
       (loops (ec-call (len-sort loops)))
       ;; The answer we return from the sneaky-mutator is an alist that says
       ;; how to update the sneaky store.  We'll go ahead and change the stored
       ;; loops to their sorted equivalent, so that when we report particular
       ;; loops we'll say the shortest example.
       (ret (list (cons :sexpr-loop-debug-loops loops)))
       (loops (if (< *max-sneaky-debug-loops* (len loops))
                  (prog2$
                   (cw "; jared-loop-debug: printing ~x0 of ~x1 \"raw\" ~
                        loops.  To increase the number of loops printed, ~
                        redefine ~s2."
                       *max-sneaky-debug-loops* (len loops)
                       '*max-sneaky-debug-loops*)
                   (take *max-sneaky-debug-loops* loops))
                loops))
       ;; Loops are numeric, so change them to variables.
       (loops (with-fast-alist inv-varmap (translate-loops loops inv-varmap)))
       (- (cw "; loop-debug: ~x0~%~%" loops)))
    ;; The answer is an ALIST that says how to update the sneaky store.
    ;; Returning NIL as a sneaky mutator means, "don't change the sneaky store."
    ret))

(defun jared-sneaky-loop-debugger ()
  (declare (xargs :guard t))
  (sneaky-mutate 'jared-sneaky-loop-debug-mutator
                 ;; List of keys to get from the sneaky store
                 (list :sexpr-loop-debug-loops
                       :sexpr-loop-debug-inv-varmap)
                 ;; User argument (none)
                 nil))

(defattach sneaky-loop-debugger jared-sneaky-loop-debugger)






(defun jared-sneaky-loop-say-how-bad-mutator (stored-vals user-arg)
  (declare (xargs :guard t))
  (b* (((unless (tuplep 2 stored-vals))
        (er hard? 'sneaky-loop-say-how-bad-mutator
            "Expected stored-vals to have the form (loops inv-varmap), found ~x0."
            stored-vals))
       ((unless (consp user-arg))
        (er hard? 'sneaky-loop-say-how-bad-mutator
            "Expected user-arg to have the form (sig-number . ndeps), found ~x0."
            user-arg))
       ((list loops inv-varmap) stored-vals)
       ((cons sig-number ndeps) user-arg)
       (sig-name (cdr (hons-get sig-number inv-varmap)))
       (- (cw "~x0 is a dependency of ~x1 previous signals.~%" sig-name ndeps))

       (loops (find-all-relevant-loops sig-number loops))
       ((unless loops)
        (cw "No loop info available for ~x0.~%" sig-name))

       (loops (with-fast-alist inv-varmap
                (translate-loops loops inv-varmap)))
       (- (verilog-summarize-translated-loops loops)))
    nil))


(defun jared-sneaky-loop-say-how-bad (sig-number ndeps)
  (declare (xargs :guard t))
  (sneaky-mutate 'jared-sneaky-loop-say-how-bad-mutator
                 (list :sexpr-loop-debug-loops
                       :sexpr-loop-debug-inv-varmap)
                 ;; User argument
                 (cons sig-number ndeps)))

(defattach sneaky-loop-say-how-bad jared-sneaky-loop-say-how-bad)
