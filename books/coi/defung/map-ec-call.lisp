; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

(in-package "DEFUNG")

;; ==================================================================
;;
;; map-ec-call-term
;;
;; maps ec-call over a (presumably fully-translated) pseudo-termp
;; modulo restrictions on which functions may be wrapped.
;;
;; ==================================================================

(defun ec-call-restriction (x omit)
  (declare (type (satisfies symbol-listp) omit))
  (or (member x omit)
      (eq x 'acl2::mv)
      (member x *ec-call-bad-ops*)))

(defund ec-call-term (fn args omit)
  (declare (type symbol fn)
	   (type (satisfies symbol-listp) omit)
	   (xargs :guard (not (equal fn 'quote)))
	   (type (satisfies pseudo-term-listp) args))
  (if (not (ec-call-restriction fn omit))
      (list `ec-call (list* fn args))
    (list* fn args)))

(defthm pseudo-termp-ec-call-term
  (implies
   (and
    (symbolp fn)
    (not (equal fn 'quote))
    (pseudo-term-listp args))
   (pseudo-termp (ec-call-term fn args omit)))
  :hints (("Goal" :in-theory (enable ec-call-term))))

(defmacro map-ec-call-term (term omit)
  `(map-ec-call-key t ,term ,omit))

(defmacro map-ec-call-args (args omit)
  `(map-ec-call-key nil ,args ,omit))

(defun map-ec-call-key (key term omit)
  (declare (type (satisfies symbol-listp) omit)
	   (xargs :measure (acl2-count term)
		  :verify-guards nil
		  :guard (if key (pseudo-termp term) (pseudo-term-listp term))))
  (let ((term term)
	(args term))
    (if key
	(cond
	 ((atom term) term)
	 ((eq (car term) 'quote) term)
         ((and (eq (car term) 'acl2::mv-let)
               (consp (cdr term))
               (consp (cddr term))
               (consp (cdddr term)))
          (let ((formals (cadr term))
                (arg     (map-ec-call-term (caddr term) omit))
                (body    (map-ec-call-term (cadddr term) omit)))
            `(acl2::mv-let ,formals ,arg ,body)))
	 ((symbolp (car term))
	  (ec-call-term (car term) (map-ec-call-args (cdr term) omit) omit))
	 (t
	  (let ((fn (car term)))
	    (cons `(lambda ,(cadr fn) ,(map-ec-call-term (caddr fn) omit))
		  (map-ec-call-args (cdr term) omit)))))
      (if (consp term)
	  (cons (map-ec-call-term (car args) omit)
		(map-ec-call-args (cdr args) omit))
	nil))))

(defun map-ec-call-property (key term omit)
  (if key
      (implies
       (pseudo-termp term)
       (pseudo-termp (map-ec-call-term term omit)))
    (and
     (equal (len (map-ec-call-args term omit))
	    (len term))
     (implies
      (pseudo-term-listp term)
      (pseudo-term-listp (map-ec-call-args term omit))))))

(defthm map-ec-call-property-proof
  (map-ec-call-property key term omit)
  :rule-classes nil
  :hints (("Goal" :induct (map-ec-call-key key term omit))))

(defthm pseudo-termp-map-ec-call-term
  (implies
   (pseudo-termp term)
   (pseudo-termp (map-ec-call-term term omit)))
  :hints (("Goal" :use (:instance map-ec-call-property-proof
				  (key t)))))

(defthm pseudo-term-listp-map-ec-call-args
  (implies
   (pseudo-term-listp term)
   (pseudo-term-listp (map-ec-call-args term omit)))
  :hints (("Goal" :use (:instance map-ec-call-property-proof
				  (key nil)))))

(verify-guards map-ec-call-key)

(mutual-recursion

 (defun strip-bad-ec-calls-args (list)
   (declare (type (satisfies pseudo-term-listp) list))
   (if (endp list) nil
     (cons (strip-bad-ec-calls (car list))
	   (strip-bad-ec-calls-args (cdr list)))))

 (defun strip-bad-ec-calls (term)
   (declare (type (satisfies pseudo-termp) term))
   (cond
    ((atom term) term)
    ((eq (car term) 'quote) term)
    ((and (equal (car term) 'ec-call)
	  (consp (cdr term))
	  (symbolp (cadr term)))
     (cadr term))
    (t
     (let ((args (strip-bad-ec-calls-args (cdr term))))
       (cond
	((consp (car term))
	 `((lambda ,(cadr (car term)) ,(strip-bad-ec-calls (caddr (car term)))) ,@args))
	(t (cons (car term) args)))))))

 )
