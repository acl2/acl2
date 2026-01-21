;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FTY")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/support" :dir :system)

(program)

(defun multicase-case-decomp (case)
  (case-match case
    ((match ':when cond val)
     (mv match cond val))
    ((match ':when cond val)
     (mv match cond val))
    ((match val)
     (mv match t val))
    (& (prog2$ (er hard? 'multicase "Illformed case: ~x0" case)
               (mv nil nil nil)))))

(defun multicase-wildcard-p (x)
  (or (eq x ':otherwise)
      (and (symbolp x)
           (or (equal (symbol-name x) "&")
               (equal (symbol-name x) "-")))))

(defun multicase-empty-cases-assemble (cases)
  (b* (((when (atom cases))
        nil)
       ((mv match cond val) (multicase-case-decomp (car cases)))
       ((when (and match
                   (not (multicase-wildcard-p match))))
        (er hard? 'multicase "Extra match fields"))
       ((when (eq cond t)) val))
    `(if ,cond ,val
       ,(multicase-empty-cases-assemble (cdr cases)))))


(defun multicase-matches-decomp (match)
  (if (multicase-wildcard-p match)
      (mv :otherwise :otherwise)
    (mv (if (multicase-wildcard-p (car match))
            :otherwise
          (car match))
        (cdr match))))



(defun cases-collect-leading-keys (cases)
  (b* (((when (atom cases)) nil)
       (rest (cases-collect-leading-keys (cdr cases)))
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first &) (multicase-matches-decomp match))
       ((when (member-equal first rest))
        rest))
    (cons first rest)))

(defun case-change-match (match case)
  (cons match (cdr case)))


(defun filter-wildcard-cases (cases)
  (b* (((when (atom cases)) nil)
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first rest) (multicase-matches-decomp match))
       ((when (multicase-wildcard-p first))
        (cons (case-change-match rest (car cases))
              (filter-wildcard-cases (cdr cases)))))
    (filter-wildcard-cases (cdr cases))))

(defun filter-key-cases (key cases)
  (b* (((when (atom cases)) nil)
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first rest) (multicase-matches-decomp match))
       ((when (or (multicase-wildcard-p first)
                  (equal first key)))
        (cons (case-change-match rest (car cases))
              (filter-key-cases key (cdr cases)))))
    (filter-key-cases key (cdr cases))))


(defun list-has-consp-cases (cases)
  (b* (((when (atom cases)) nil)
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first &) (multicase-matches-decomp match))
       ((when (atom first))
        (list-has-consp-cases (cdr cases))))
    t))

(defun list-has-endp-cases (cases)
  (b* (((when (atom cases)) nil)
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first &) (multicase-matches-decomp match))
       ((when (eq first nil))
        t))
    (list-has-endp-cases (cdr cases))))

(defun list-process-consp-cases (cases)
  (b* (((when (atom cases)) nil)
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first rest) (multicase-matches-decomp match))
       ((when (multicase-wildcard-p first))
        (cons (case-change-match (list* first first rest) (car cases))
              (list-process-consp-cases (cdr cases))))
       ((when (atom first))
        (list-process-consp-cases (cdr cases)))
       ;; first is a cons. We change e.g.
       ;; ((:foo :bar) rest)
       ;; to (:foo (:bar) rest)
       ;; because we're going to do separate cases on the car and cdr.
       ((cons first-first rest-first) first))
    (cons (case-change-match (list* first-first rest-first rest) (car cases))
          (list-process-consp-cases (cdr cases)))))

(defun list-process-wildcard-cases (cases)
  (b* (((when (atom cases)) nil)
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first rest) (multicase-matches-decomp match))
       ((when (multicase-wildcard-p first))
        (cons (case-change-match rest (car cases))
              (list-process-wildcard-cases (cdr cases)))))
    (list-process-wildcard-cases (cdr cases))))

(defun list-process-endp-cases (cases)
  (b* (((when (atom cases)) nil)
       ((mv match & &) (multicase-case-decomp (car cases)))
       ((mv first rest) (multicase-matches-decomp match))
       ((unless (or (multicase-wildcard-p first)
                    (eq first nil)))
        (list-process-endp-cases (cdr cases))))
    (cons (case-change-match rest (car cases))
          (list-process-endp-cases (cdr cases)))))

(mutual-recursion
 (defun multicase-fn (pairs cases)
   ;; Pairs is something like ((foo-case x) (bar-case y) ((list baz-case z0 z1 z2) z))
   ;; Cases is something like (((:foo-kind1 :bar-kind2) (f x.a y.b))
   ;;                          ((&          :bar-kind1) (g x y.c))
   ;;                          ((:foo-kind1 :bar-kind3)
   ;;                           :when (p x.b)
   ;;                           (h x.a y.d))
   ;;                          (&           (j x y))           
   (b* (((when (atom pairs))
         ;; Cases should all have empty match fields and only possibly WHEN fields --
         ;; assemble these into an IF.
         (multicase-empty-cases-assemble cases))
        ((list casemacro var) (car pairs))
        ((mv listp casemacro vars) (case-match casemacro
                                (('list mac . vars) (mv t mac vars))
                                (& (if (atom casemacro)
                                       (mv nil casemacro nil)
                                     (prog2$ (er hard? 'multicase-fn "bad casemacro")
                                             (mv nil nil nil))))))
        ((when listp)
         (b* ((has-cons (list-has-consp-cases cases))
              (has-end  (list-has-endp-cases cases))
              (end-cases (list-process-endp-cases cases))
              (check-consp (or has-cons has-end)))
           (if check-consp
                 `(if (consp ,var)
                      ,(if has-cons
                           (b* ((cons-cases (list-process-consp-cases cases)))
                             `(let* ((,(car vars) (car ,var))
                                     (multicase-tmp (cdr ,var)))
                                (declare (ignorable multicase-tmp ,(car vars)))
                                ,(multicase-fn (list* `(,casemacro ,(car vars))
                                                      `((list ,casemacro . ,(cdr vars)) multicase-tmp)
                                                      (cdr pairs))
                                               cons-cases)))
                         (b* ((wild-cases (list-process-wildcard-cases cases)))
                           (multicase-fn (cdr pairs) wild-cases)))
                    ,(multicase-fn (cdr pairs) end-cases))
             (multicase-fn (cdr pairs) end-cases))))
        (match-keys (cases-collect-leading-keys cases))
        (has-wildcard (member-eq :otherwise match-keys))
        (non-wildcard-keys (remove-eq :otherwise match-keys)))
     `(,casemacro ,var
        . ,(multicase-collect-subcases non-wildcard-keys has-wildcard (cdr pairs) cases))))

 (defun multicase-collect-subcases (keys
                                    has-wildcard
                                    pairs
                                    cases)
   (if (atom keys)
       (and has-wildcard
            `(:otherwise* ,(multicase-fn pairs (filter-wildcard-cases cases))))
     (b* ((key (car keys)))
       `(,key ,(multicase-fn pairs (filter-key-cases key cases))
              . ,(multicase-collect-subcases (cdr keys) has-wildcard pairs cases))))))
         
       



       


(defmacro multicase (pairs &rest cases)
  (multicase-fn pairs cases))




(defun enum-casemacro-cases (kwd-alist)
  (b* (((when (atom kwd-alist))
        nil)
       ((when (or (eq (caar kwd-alist) :otherwise)
                  (eq (caar kwd-alist) :otherwise*)))
        `((otherwise ,(cdar kwd-alist)))))
    (cons `(,(if (atom (cdr kwd-alist))
                 'otherwise
               (caar kwd-alist))
            ,(cdar kwd-alist))
          (enum-casemacro-cases (cdr kwd-alist)))))
        

(defun enumcase-case-fn (var-or-expr rest-args macro-name fix enum-members)
  (b* (((when (and (eql (len rest-args) 1)
                   (or (atom (car rest-args))
                       (eq (caar rest-args) 'quote))))
        (cond ((and (atom (car rest-args))
                    (member-eq (car rest-args) enum-members))
               ;; special case: (foo-case expr :kind) becomes (eq expr :kind)
               `(eq ,var-or-expr ,(car rest-args)))
              ((and (consp (car rest-args))
                    (eq (caar rest-args) :quote)
                    (true-listp (cadr rest-args))
                    (subsetp (cadr rest-args) enum-members))
               ;; special case: (foo-case expr '(:kind1 :kind2))
               ;; becomes (member-eq expr '(:kind1 :kind2))
               `(member-eq ,var-or-expr ,(car rest-args)))
              (t (er hard? macro-name "Bad argument: ~x0~%Must be one of ~x1 or a quoted subset."
                     (car rest-args) enum-members))))

       ((when (consp var-or-expr))
        (er hard? macro-name "Expected a variable, rather than: ~x0" var-or-expr))

       (allowed-keywordlist-keys (append enum-members '(:otherwise :otherwise*)))
       (allowed-parenthesized-keys (append enum-members '(acl2::otherwise :otherwise :otherwise* acl2::&)))
       ((mv kwd-alist rest)
        (std::extract-keywords macro-name
                          allowed-keywordlist-keys
                          rest-args nil))

       ((when (and rest kwd-alist))
        (er hard? macro-name "Inconsistent syntax: ~x0" rest-args))

       ((unless (or kwd-alist
                    (and (alistp rest)
                         (true-list-listp rest)
                         ;; weaken this?
                         (subsetp (strip-cars rest) allowed-parenthesized-keys))))
        (er hard? macro-name "Malformed cases: ~x0~%" rest))
       
       (kwd-alist (reverse kwd-alist))

       (keys (if kwd-alist
                 (strip-cars kwd-alist)
               (sublis '((acl2::otherwise . :otherwise)
                         (acl2::&         . :otherwise))
                       (strip-cars rest))))

       (vals (if kwd-alist
                 (strip-cdrs kwd-alist)
               (pairlis$ (make-list (len rest) :initial-element 'progn$)
                         (strip-cdrs rest))))

       ((unless (and (<= (len (member :otherwise keys)) 1)
                     (<= (len (member :otherwise* keys)) 1)))
        (er hard? macro-name "Otherwise case must be last"))

       (completep (subsetp-eq enum-members keys))
       (redundant-otherwise (and completep (member-eq :otherwise keys)))
       ((when redundant-otherwise)
        (er hard? macro-name "Redundant otherwise case"))
       (incompletep (and (not completep)
                         (not (member-eq :otherwise keys))
                         (not (member-eq :otherwise* keys))))
       ((when incompletep)
        (er hard? 'macro-name "Incomplete cases and no :otherwise/:otherwise*"))
       
       (redundant-otherwise* (and completep
                                  (member-eq :otherwise* keys)))
       (case-kwd-alist (or kwd-alist (pairlis$ keys vals)))
       (case-kwd-alist (if redundant-otherwise*
                           (remove-assoc-eq :otherwise* case-kwd-alist)
                         case-kwd-alist))

       (body `(case (,fix ,var-or-expr)
                . ,(enum-casemacro-cases case-kwd-alist))))
    body))
       

(defun def-enumcase-fn (name enum wrld)
  (b* ((tab (table-alist 'std::defenum-table wrld))
       (look (cdr (assoc-eq enum tab)))
       (members (cdr (assoc-eq :members look)))
       (fix (cdr (assoc-eq :fix look))))
    `(defmacro ,name (var &rest rest-args)
       (enumcase-case-fn var rest-args ',name ',fix ',members))))
       

(defmacro def-enumcase (name enum)
  `(make-event
    (def-enumcase-fn ',name ',enum (w state))))



(defun case*-keyvals-to-cases (keyvals)
  (if (atom keyvals)
      nil
    (cons (cond ((eq (car keyvals) :otherwise*) `(t ,(cadr keyvals)))
                ((booleanp (car keyvals)) `((,(car keyvals)) ,(cadr keyvals)))
                (t `(,(car keyvals) ,(cadr keyvals))))
          (case*-keyvals-to-cases (cddr keyvals)))))

(defun case*-fn (var keyvals)
  `(case ,var
     . ,(case*-keyvals-to-cases keyvals)))

(defmacro case* (var &rest keyvals)
  (case*-fn var keyvals))

(defun case*-equal-keyvals-to-cond (var keyvals)
  (if (atom keyvals)
      nil
    (cons (if (eq (car keyvals) :otherwise*)
              `(t ,(cadr keyvals))
            `((equal ,var ,(car keyvals))
              ,(cadr keyvals)))
          (case*-equal-keyvals-to-cond var (cddr keyvals)))))

(defun case*-equal-fn (var keyvals)
 `(cond . ,(case*-equal-keyvals-to-cond var keyvals)))

(defmacro case*-equal (var &rest keyvals)
  (case*-equal-fn var keyvals))

