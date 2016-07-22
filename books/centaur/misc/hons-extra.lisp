; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

(defxdoc with-fast-alists
  :parents (fast-alists)
  :short "Concisely call @(see with-fast-alist) on multiple alists."
  :long "<p>Example:</p>
@({
   (with-fast-alists (a b c) form)
})

<p>is just shorthand for:</p>

@({
   (with-fast-alist a
    (with-fast-alist b
     (with-fast-alist c
      form)))
})

@(def with-fast-alists)
@(def with-fast-alists-fn)")

(defun with-fast-alists-fn (alists form)
  (if (atom alists)
      form
    `(with-fast-alist ,(car alists)
                      ,(with-fast-alists-fn (cdr alists) form))))

(defmacro with-fast-alists (alists form)
  (with-fast-alists-fn alists form))

(def-b*-binder with-fast
  :short "@(see b*) binder to make some alists fast for the remainder of the
          @('b*') form."
  :decls ((declare (xargs :guard (not forms))
                   (ignorable forms)))
  :body
  `(with-fast-alists ,args ,rest-expr))



#||

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b '((1 . a) (2 . b) (3 . d)))
     (- (cw "Before with-fast-alists:~%"))
     (- (fast-alist-summary)))

    (with-fast-alists
     (a b)
     (b* ((- (cw "After with-fast-alists:~%"))
          (- (fast-alist-summary))
          (x (hons-get 2 a))
          (a ())
          (y (hons-get 3 b)))
       (list (cdr x) (cdr y) a))))

(fast-alist-summary)

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b '((1 . a) (2 . b) (3 . d)))
     (- (cw "Before with-fast:~%"))
     (- (fast-alist-summary))
     ((with-fast a b))      ;; a and b become fast until the end of the b*.
     (- (cw "After with-fast:~%"))
     (- (fast-alist-summary))
     (x (hons-get 2 a))
     (a ())
     (y (hons-get 3 b)))
  (list (cdr x) (cdr y) a))

(fast-alist-summary)

||#

(defun alist-of-alistsp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst)
         (null lst))
        ((and (consp (car lst))
              (alistp (cdar lst)))
         (alist-of-alistsp (cdr lst)))
        (t nil)))

(defun make-fast-alist-of-alists (lst)

; Perhaps a tail recursive definition would be better, but this is simpler (so
; long as we don't overflow the stack).

  (declare (xargs :guard (alist-of-alistsp lst)
                  :mode :logic))
  (cond
   ((atom lst)
    lst)
   (t
    (let* ((current-entry (car lst)))
      (cond ((atom current-entry)
             (prog2$ (er hard 'make-fast-alist-of-alists
                         "Guard of alist-of-alistp not met.  ~x0 was an atom ~
                          when it needed to be an [inner] alist."
                         current-entry)
                     lst))
            (t (let* ((current-entry-key (car current-entry))
                      (current-entry-val (cdr current-entry))
                      (new-current-entry-val (make-fast-alist current-entry-val)))
                 (hons-acons current-entry-key
                             new-current-entry-val
                             (make-fast-alist-of-alists (cdr lst))))))))))

(defthm make-fast-alist-of-alists-identity
  (equal (make-fast-alist-of-alists lst) lst))

(in-theory (disable make-fast-alist-of-alists))


(defxdoc with-stolen-alists
  :parents (fast-alists)
  :short "Concisely call @(see with-stolen-alist) on multiple alists."
  :long "<p>Example:</p>
@({
    (with-stolen-alists (a b c) form)
})

<p>is just shorthand for:</p>

@({
    (with-stolen-alist a
      (with-stolen-alist b
        (with-stolen-alist c
          form)))
})

@(def with-stolen-alists)
@(def with-stolen-alists-fn)")

(defun with-stolen-alists-fn (alists form)
  (if (atom alists)
      form
    `(with-stolen-alist ,(car alists)
                      ,(with-stolen-alists-fn (cdr alists) form))))

(defmacro with-stolen-alists (alists form)
  (with-stolen-alists-fn alists form))

(def-b*-binder with-stolen
  :short "@(see b*) binder for invoking @(see with-stolen-alists) for the
          remainder of a @(see b*) form."
  :decls ((declare (xargs :guard (not forms))
                   (ignorable forms)))
  :body
  `(with-stolen-alists ,args ,rest-expr))

#||

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b '((1 . a) (2 . b) (3 . d)))
     (- (cw "Before with-stolen-alists:~%"))
     (- (fast-alist-summary))
     (res (with-stolen-alists
            (a b)
            (b* ((- (cw "Inside with-stolen-alists:~%"))
                 (- (fast-alist-summary))
                 (x (hons-get 2 a))
                 (a ())
                 (y (hons-get 3 b)))
              (list (cdr x) (cdr y) a)))))
  (cw "After with-stolen-alists:~%")
  (fast-alist-summary)
  res)

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b (make-fast-alist '((1 . a) (2 . b) (3 . d))))
     (- (cw "Before with-stolen-alists:~%"))
     (- (fast-alist-summary))
     (res (with-stolen-alists
            (a b)
            (b* ((- (cw "Inside with-stolen-alists:~%"))
                 (- (fast-alist-summary))
                 (x (hons-get 2 a))
                 (a ())
                 (b (hons-acons 5 'f b))
                 (y (hons-get 5 b)))
              (fast-alist-free b)
              (list (cdr x) (cdr y) a))))
     (b (hons-acons 4 'e b)))
  (cw "After with-stolen-alists:~%")
  (fast-alist-summary)
  (fast-alist-free b)
  res)

||#


(defxdoc fast-alists-free-on-exit
  :parents (fast-alists)
  :short "Concisely call @(tsee fast-alist-free-on-exit) for several alists."
  :long "<p>For example:</p>

@({
    (fast-alists-free-on-exit (a b c) form)
})

<p>is just shorthand for:</p>

@({
    (fast-alist-free-on-exit a
     (fast-alist-free-on-exit b
      (fast-alist-free-on-exit c
       form)))
})

@(def fast-alists-free-on-exit)
@(def fast-alists-free-on-exit-fn)")

(defun fast-alists-free-on-exit-fn (alists form)
  (if (atom alists)
      form
    `(fast-alist-free-on-exit ,(car alists)
                              ,(fast-alists-free-on-exit-fn (cdr alists) form))))

(defmacro fast-alists-free-on-exit (alists form)
  (fast-alists-free-on-exit-fn alists form))

(def-b*-binder free-on-exit
  :short "@(see b*) binder for freeing fast alists when the @(see b*) exits."
  :decls ((declare (xargs :guard (not forms))
                   (ignorable forms)))
  :body
  `(fast-alists-free-on-exit ,args ,rest-expr))


#|

(fast-alist-summary)

(let ((a (hons-acons 'a 1 'a-alist)))
  (fast-alist-free-on-exit a            ;; a is still fast until the end of the
    (hons-get 'a a)))                   ;; fast-alist-free-on-exit form

(fast-alist-summary)

(let ((a (hons-acons 'a 1 'a-alist))    ;; a and b are still fast until the
      (b (hons-acons 'b 2 'b-alist)))   ;; exit of the fast-alists-free-on-exit
  (fast-alists-free-on-exit             ;; form.
   (a b)
   (+ (cdr (hons-get 'a a))
      (cdr (hons-get 'b b)))))

(fast-alist-summary)



(b* ((- (fast-alist-summary))

     (a (hons-acons 'a 1 'a-alist))
     (b (hons-acons 'b 2 'b-alist))
     (- (cw "After creating a and b.~%"))
     (- (fast-alist-summary))

     ((free-on-exit a b))           ;; a and b are still fast until the end of

     (c (hons-acons 'c 3 'c-alist))
     (- (cw "After creating c.~%"))
     (- (fast-alist-summary))
     (- (fast-alist-free c)))

  (+ (cdr (hons-get 'a a))
     (cdr (hons-get 'b b))))

(fast-alist-summary) ;; all alists freed

|#
