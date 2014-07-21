; The SEQ Macro Language, Examples
; Copyright (C) 2008-2010 Centaur Technology
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

(in-package "ACL2")
(include-book "seq")
(set-verify-guards-eagerness 2)

; We will demonstrate how SEQ may be used to develop "parsers" that recognize
; certain kinds of lists.  We begin with some straightforward utility
; functions.

(defun match-int (lst)
  (cond ((not (consp lst))
         (mv "Error: expecting int but found end of list." nil lst))
        ((not (integerp (car lst)))
         (mv "Error: integer expected." nil lst))
        (t
         (mv nil (car lst) (cdr lst)))))

(defun match-string (lst)
  (cond ((not (consp lst))
         (mv "Error: expecting string but found end of list." nil lst))
        ((not (stringp (car lst)))
         (mv "Error: string expected." nil lst))
        (t
         (mv nil (car lst) (cdr lst)))))

(defun match-three-ints (lst)
  (seq lst
       (a := (match-int lst))
       (b := (match-int lst))
       (c := (match-int lst))
       (return (list (cons 'a a)
                     (cons 'b b)
                     (cons 'c c)))))

(match-three-ints '(1 2 3))   ;; Works, val is (a . 1) (b . 2) (c . 3)
(match-three-ints '(1 "2" 3)) ;; Fails, 2 is not an integer.



; This requires that the list beings with an integer, and furthermore if a
; string follows the integer, then there must be three strings after the
; integer.  Notice how we can refer to the variables b, c, and d even if the
; "when" branch is not followed -- implicitly, all the variables in a SEQ
; program are bound to nil to begin with.

(defun match-int-then-maybe-three-strings (lst)
  (seq lst
       (a := (match-int lst))
       (when (and (consp lst)
                  (stringp (car lst)))
         (b := (match-string lst))
         (c := (match-string lst))
         (d := (match-string lst)))
       (return (list (list :a a)
                     (list :b b)
                     (list :c c)
                     (list :d d)))))

; Fail, not even an int:
(match-int-then-maybe-three-strings nil)

; Fail, not even an int.
(match-int-then-maybe-three-strings '("1"))

; Works, one int is okay.
(match-int-then-maybe-three-strings '(1))

; Works, one int is okay, leaves 2 in lst.
(match-int-then-maybe-three-strings '(1 2))

; Fail, if a string is there, we need three strings.
(match-int-then-maybe-three-strings '(1 "foo"))

; Works, an int and 3 strings.
(match-int-then-maybe-three-strings '(1 "foo" "bar" "baz"))

; Works, an int and 3 strings; leaves 2 3 4 in the lst
(match-int-then-maybe-three-strings '(1 "foo" "bar" "baz" 2 3 4))



; SEQ does not have any looping construct, but you can recursively call the
; current function as an action.  So this matches a non-empty list of
; integers.

(defun match-int-list (lst)
  (seq lst
       (first := (match-int lst))
       (when (consp lst)
         (rest := (match-int-list lst)))
       (return (cons first rest))))

(match-int-list nil)                 ;; fail, need at least one int
(match-int-list '(1 2 3 4))          ;; works
(match-int-list '(1 2 3 4 "five"))   ;; fail, not all integers



; Here's another way to match a non-empty list of integers, which also uses
; an "early return" in the unless block.

(defun match-int-list2 (lst)
  (seq lst
       (first := (match-int lst))
       (unless (consp lst)
         (return (list first)))
       (rest := (match-int-list2 lst))
       (return (cons first rest))))

(match-int-list2 nil)               ;; fail, need at least one int
(match-int-list2 '(1 2 3 4))        ;; works
(match-int-list2 '(1 2 3 4 "five")) ;; fail, not all integers



; And here's a variant that permits an empty list.  Early returns are nice
; for avoiding nested whens, etc.

(defun match-ints (lst)
  (seq lst
       (when (atom lst)
         (return nil))
       (first := (match-int lst))
       (rest := (match-ints lst))
       (return (cons first rest))))

(match-ints nil)                ;; works
(match-ints '(1 2 3))           ;; works
(match-ints '(1 2 3 "four"))    ;; fail, not all integers



; And here's a tail-recursive variant that accumulates the integers into acc
; in reverse, then reverses them at the end.

(defun tr-match-ints (lst acc)
  (declare (xargs :guard (true-listp acc)))
  (seq lst
       (when (atom lst)
         (return (reverse acc)))
       (a := (match-int lst))
       (return-raw (tr-match-ints lst (cons a acc)))))

(tr-match-ints nil nil)                ;; works
(tr-match-ints '(1 2 3) nil)           ;; works
(tr-match-ints '(1 2 3 "four") nil)    ;; fail, not all integers

#||
; stack overflows on my Lisp
; segfaults on gcl, watch out.
(comp 'match-ints)
(mv-let (erp val lst)
        (match-ints (make-list 10000000 :initial-element 0))
        (declare (ignore val lst))
        erp)
||#

; does not stack overflow on my Lisp
(comp 'tr-match-ints)
(mv-let (erp val lst)
        (tr-match-ints (make-list 10000000 :initial-element 0) nil)
        (declare (ignore val lst))
        erp)


; And here's a function that reads as many ints as it can.
(defun match-front-ints (lst)
  (seq lst
       (unless (and (consp lst)
                    (integerp (car lst)))
         (return nil))
       (a := (match-int lst))
       (b := (match-front-ints lst))
       (return (cons a b))))

(match-front-ints nil)                ;; fine, no ints
(match-front-ints '("foo" 1 2 3))     ;; fine, but no front ints
(match-front-ints '(1 2 3 "foo" 4 5)) ;; fine, but only matches 1 2 3



; Now let's try backtracking.  We'll write a function that either reads "int
; int string", or "string string int", or fails.

(defun match-iis-or-ssi (lst)
  (seq-backtrack lst
                 ;; Option 1: Read int, int, string.
                 ((i1 := (match-int lst))
                  (i2 := (match-int lst))
                  (str := (match-string lst))
                  (return (list :OPTION-1 i1 i2 str)))
                 ;; Option 2: Read string, string, int.
                 ((s1 := (match-string lst))
                  (s2 := (match-string lst))
                  (int := (match-int lst))
                  (return (list :OPTION-2 s1 s2 int)))))

(match-iis-or-ssi '(1 1 "foo" 2 3 4))  ;; works, option 1
(match-iis-or-ssi '("foo" "bar" 1 9))  ;; works, option 2
(match-iis-or-ssi '(1 "foo" 2 2 4))    ;; fails
