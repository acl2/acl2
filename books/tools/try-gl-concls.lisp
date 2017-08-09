; Copyright (C) 2017 Centaur Technology
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
; Original author: Shilpi Goel <shilpi@centtech.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(include-book "misc/eval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

;; ----------------------------------------------------------------------

(set-state-ok t)
(set-irrelevant-formals-ok t)
(program)

(defun try-gl-concl-1 (name hyps concl kwd-alist state)

  (b* ((form `(gl::gl-thm ,name
                          :hyp ,hyps
                          :concl ,concl
                          ,@kwd-alist))
       (- (cw "~%Trying this form: ~p0~%" form))
       ;; Try the new event.
       ((mv trans-eval-erp stobjs-out/replaced-val state)
        (trans-eval form 'try-gl-concl-1 state t))
       (stobjs-out (car stobjs-out/replaced-val))
       (replaced-val (cdr stobjs-out/replaced-val))
       (err (or trans-eval-erp
                (not (equal stobjs-out '(nil nil state)))
                (car replaced-val))))
    (mv err state)))

(defun try-gl-concls-aux (name hyps concls kwd-alist ok-concls state)
  (if (endp concls)
      (value ok-concls)
    (b* ((this-concl (car concls))
         (rest-concl (cdr concls))
         ((mv err state)
          (try-gl-concl-1 name hyps this-concl kwd-alist state))
         ((when (not err))
          ;; gl-thm succeeded, save concl in ok-concls and recur.
          (try-gl-concls-aux
           name hyps rest-concl kwd-alist (cons this-concl ok-concls) state)))
      ;; gl-thm failed, just recur.
      (try-gl-concls-aux
       name hyps rest-concl kwd-alist ok-concls state))))

(defun try-gl-concls-fn (name args state)
  (b* (((mv args-alist rest)
        (std::extract-keywords
         'try-gl-concls '(:hyp :concls :g-rest) args nil))
       ((when rest)
        (er soft 'try-gl-concls
            "Non-keyword arg(s) to try-gl-concls: ~x0~%"
            rest))
       (hyp          (std::getarg :hyp      t args-alist))
       (concls       (std::getarg :concls nil args-alist))
       (g-rest-alist (std::getarg :g-rest nil args-alist))
       ((mv erp ok-concls state)
        (try-gl-concls-aux name hyp concls g-rest-alist nil state))
       (- (cw "~%Hyp:~%~p0~%" hyp))
       (- (if ok-concls
              (cw "~%Successful conclusion(s):~%")
            (cw "~%No conclusion was successful!~%"))))
    (mv erp ok-concls state)))

(defmacro try-gl-concls (name &rest args)
  `(try-gl-concls-fn (quote ,name) (quote ,args) state))

(logic)

#||

(try-gl-concls test
               :hyp (and (unsigned-byte-p 1 a) (unsigned-byte-p 1 b))
               :concls ((not (equal (+ a b) 0))
                        (not (equal (+ a b) 1))
                        (not (equal (+ a b) 2)))
               :g-rest (:g-bindings
                        (gl::auto-bindings (:mix (:nat a 8) (:nat b 8)))))

(try-gl-concls test
               :hyp (and (unsigned-byte-p 1 a) (unsigned-byte-p 1 b))
               :concls ((not (equal (+ a b) 0))
                        (not (equal (+ a b) 1))
                        (not (equal (+ a b) 2))
                        (not (equal (+ a b) 3)))
               :g-rest (:g-bindings
                        (gl::auto-bindings (:mix (:nat a 8) (:nat b 8)))))

||#

;; ======================================================================