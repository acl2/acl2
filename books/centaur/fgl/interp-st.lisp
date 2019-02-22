; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "pathcond")
(include-book "bvar-db")
(include-book "constraint-db")
(include-book "glcp-config")

(fty::defalist nat-nat-alist :key-type natp :val-type natp :true-listp t)

(defstobj interp-profiler
  (prof-enabledp :type (satisfies booleanp))
  (prof-indextable)
  (prof-totalcount :type (integer 0 *) :initially 0)
  (prof-nextindex :type (integer 0 *) :initially 0)
  (prof-array :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (prof-stack :type (satisfies nat-nat-alist-p)))

(make-event
 `(defconst *interp-st-fields*
    '((logicman :type logicman)
      (bvar-db :type bvar-db)
      (pathcond :type pathcond)
      (constraint :type pathcond)
      (constraint-db :type (satisfies constraint-db-p))
      (prof :type interp-profiler)
      (debug-stack :type t)
      (backchain-limit :type (or (integer 0 *) null))
      (bvar-mode :type t)
      (reclimit :type (integer 0 *) :initially 0)
      (config :type (satisfies glcp-config-p) :initially ,(make-glcp-config)))))


(local (defun interp-st-fields-to-templates (fields)
         (declare (xargs :mode :program))
         (if (atom fields)
             nil
           (cons (acl2::make-tmplsubst :atoms `((<field> . ,(caar fields))
                                                (:<field> . ,(intern$ (symbol-name (caar fields)) "KEYWORD"))
                                                (<fieldcase> . ,(if (atom (cdr fields))
                                                                    t
                                                                  (intern$ (symbol-name (caar fields)) "KEYWORD")))
                                                (<type> . ,(third (car fields)))
                                                (<rest> . ,(cdddr (car fields))))
                                       :strs `(("<FIELD>" . ,(symbol-name (caar fields))))
                                       :pkg-sym 'fgl::foo)
                 (interp-st-fields-to-templates (cdr fields))))))

(make-event
 `(defconst *interp-st-field-templates*
    ',(interp-st-fields-to-templates *interp-st-fields*)))
  

(make-event
 (acl2::template-subst
  '(defstobj interp-st
     (:@proj fields (interp-st-><field> :type <type> . <rest>)))
  :subsubsts `((fields . ,*interp-st-field-templates*))))


(make-event
 (acl2::template-subst
  '(std::defenum interp-st-field-p ((:@proj fields :<field>)))
  :subsubsts `((fields . ,*interp-st-field-templates*))))

(make-event
 (acl2::template-subst
  '(define interp-st-get ((key interp-st-field-p) &optional (interp-st 'interp-st))
     ;; bozo define doesn't correctly support :non-executable t with macro args
     (declare (xargs :non-executable t))
     :no-function t
     :prepwork ((local (in-theory (enable interp-st-field-fix))))
     (prog2$ (acl2::throw-nonexec-error 'interp-st-get-fn (list key interp-st))
             (case key
               (:@proj fields (<fieldcase> (interp-st-><field> interp-st))))))
  :subsubsts `((fields . ,*interp-st-field-templates*))))

(make-event
 (acl2::template-subst
  '(defsection interp-st-field-basics
     (local (in-theory (enable interp-st-get
                               interp-st-field-fix)))
     (:@append fields
      (def-updater-independence-thm interp-st-><field>-updater-independence
        (implies (equal (interp-st-get :<field> new)
                        (interp-st-get :<field> old))
                 (equal (interp-st-><field> new)
                        (interp-st-><field> old))))

      (defthm update-interp-st-><field>-preserves-others
        (implies (not (equal (interp-st-field-fix i) :<field>))
                 (equal (interp-st-get i (update-interp-st-><field> x interp-st))
                        (interp-st-get i interp-st))))

      (defthm update-interp-st-><field>-self-preserves-interp-st
        (implies (interp-stp interp-st)
                 (equal (update-interp-st-><field>
                         (interp-st-><field> interp-st)
                         interp-st)
                        interp-st))
        :hints(("Goal" :in-theory (enable interp-stp
                                          aignet::redundant-update-nth))))

      (defthm interp-st-><field>-of-update-interp-st-><field>
        (equal (interp-st-><field> (update-interp-st-><field> x interp-st))
               x)))

     (:@proj fields
      (in-theory (disable interp-st-><field>
                          update-interp-st-><field>)))

     (local (in-theory (disable interp-st-get
                                interp-st-field-fix)))

     ;; test:
     (local 
      (defthm interp-st-test-updater-independence
        (b* ((interp-st1 (update-interp-st->bvar-mode bvar-mode interp-st))
             (interp-st2 (update-interp-st->logicman logicman interp-st)))
          (and (equal (interp-st->constraint interp-st2) (interp-st->constraint interp-st))
               (equal (interp-st->constraint interp-st1) (interp-st->constraint interp-st)))))))
  
  :subsubsts `((fields . ,*interp-st-field-templates*))))


