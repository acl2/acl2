; XDOC Documentation System for ACL2
; Copyright (C) 2009-2014 Centaur Technology
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
; Modified November 2014 by Matt Kaufmann

; defdoc -> defxdoc converter
;
; Original author: Jared Davis <jared@centtech.com>
;
; Modified November 2014 by Matt Kaufmann, to convert book documentation
; instead of ACL2 system documentation

(in-package "ACL2") ;; So the acl2 topic comes from the acl2 package.
(set-state-ok t)
(program)

#!XDOC
(progn
  (defun remove-alist-key (key x)
    (cond ((atom x)
           nil)
          ((atom (car x))
           (remove-alist-key key (cdr x)))
          ((equal (caar x) key)
           (remove-alist-key key (cdr x)))
          (t
           (cons (car x) (remove-alist-key key (cdr x))))))

  (defun change-self-parent-to-acl2 (topic)
    (let ((name    (cdr (assoc :name topic)))
          (parents (cdr (assoc :parents topic))))
      (if (member name parents)
          (acons :parents
                 (cons 'acl2::acl2 (remove-equal name parents))
                 (remove-alist-key :parents topic))
        topic)))

  (defun change-self-parents-to-acl2 (topics)
    (if (atom topics)
        nil
      (cons (change-self-parent-to-acl2 (car topics))
            (change-self-parents-to-acl2 (cdr topics)))))

  (defun add-from-acl2 (topics)
    (if (atom topics)
        nil
      (cons (acons :from "ACL2 Sources" (car topics))
            (add-from-acl2 (cdr topics)))))

  (defun all-topic-names (topics)
    (if (atom topics)
        nil
      (cons (cdr (assoc :name (car topics)))
            (all-topic-names (cdr topics)))))

  (defun remove-topics-by-name (topics names)
    (cond ((atom topics)
           nil)
          ((member (cdr (assoc :name (car topics))) names)
           (remove-topics-by-name (cdr topics) names))
          (t
           (cons (car topics) (remove-topics-by-name (cdr topics) names)))))

  )

(include-book "xdoc/base" :dir :system)
(include-book "std/util/bstar" :dir :system)

(include-book "system/origin" :dir :system)

(defun defdoc-include-book-path (name wrld)

; Tool from Matt Kaufmann for figuring out where a DEFDOC event comes from.
;
; We return nil if there is no defdoc for name.  Otherwise, we return the
; include-book path (with closest book first, hence opposite from the order
; typically displayed by :pe) for the most recent defdoc of name, else t if
; that path is nil.

  (declare (xargs :mode :program))
  (cond ((endp wrld)
         nil)
        (t (or (let ((x (car wrld)))
                 (case-match x
                   (('EVENT-LANDMARK 'GLOBAL-VALUE . event-tuple)
                    (let ((form (access-event-tuple-form event-tuple)))
                      (case-match form
                        (('DEFDOC !name . &)
                         ;; Matt's version didn't reverse these, but mine
                         ;; does for compatibility with the origin book.
                         (or (reverse (global-val 'include-book-path wrld))
                             t)))))))
               (defdoc-include-book-path name (cdr wrld))))))

#!XDOC
(defun extend-topic-with-origin (topic state)
  ;; Returns (MV TOPIC STATE)
  (b* ((name (cdr (assoc :name topic)))
       (from (cdr (assoc :from topic)))

       ((when from)
        (er hard? 'extend-topic-with-origin
            "Topic ~x0 already has :from." name)
        (mv topic state))

       ((unless (symbolp name))
        (er hard? 'extend-topic-with-origin
            "Topic with non-symbolic name ~x0" name)
        (mv topic state))

       ((mv er val state)
        (acl2::origin-fn name state))
       ((mv er val)
        (b* (((unless er)
              (mv er val))
             ;; This can occur at least in cases such as DEFDOC, which do not
             ;; introduce logical names.
             ;(- (cw "~x0: unknown: ~@1~%" name er))
             (new-val (acl2::defdoc-include-book-path name (w state)))
             ((when new-val)
              ;(cw "~x0: tried harder and found ~x1.~%" name new-val)
              (mv nil new-val)))
          ;(cw "~x0: tried harder and still failed." name)
          (mv er val)))

       ((when er)
        (mv (acons :from "Unknown" topic)
            state))

       ((when (eq val :built-in))
        ;;(cw "~x0: built-in~%" name)
        (mv (acons :from "ACL2 Sources" topic)
            state))

       ((when (natp val))
        ;;(cw "~x0: current session.~%" name)
        (mv (acons :from "Current Interactive Session" topic)
            state))

       ((when (and (consp val)
                   (string-listp val)))
        (b* ((bookname (car (last val)))
             (bookname (normalize-bookname bookname state)))
          ;; (cw "~x0: ~x1~%" name bookname)
          (mv (acons :from bookname topic)
              state))))

    (er hard? 'extend-topic-with-origin
        "origin-fn returned unexpected value ~x0." val)
    (mv topic state)))

#!XDOC
(defun extend-topics-with-origins (topics state)
  (b* (((when (atom topics))
        (mv nil state))
       ((mv first state)
        (extend-topic-with-origin (car topics) state))
       ((mv rest state)
        (extend-topics-with-origins (cdr topics) state)))
    (mv (cons first rest) state)))

; The following was in the original version of this book, and might or might
; not still be useful.

#||
;; Test code:

(len (xdoc::get-xdoc-table (w state)))  ;; 1546
(make-event
 `(defconst *prev-names*
    ',(xdoc::all-topic-names (xdoc::get-xdoc-table (w state)))))
(include-book
 "ihs/logops-lemmas" :dir :system)
(len (xdoc::get-xdoc-table (w state)))  ;; 1546
(time$ (xdoc::import-acl2doc))  ;; .2 seconds, converting all that ihs doc
(len (xdoc::get-xdoc-table (w state)))  ;; 1841
(set-difference-equal
 (xdoc::all-topic-names (xdoc::get-xdoc-table (w state)))
 *prev-names*)
(time$ (xdoc::import-acl2doc))  ;; almost no time
(len (xdoc::get-xdoc-table (w state))) ;; 1841


(defun all-topic-froms (topics)
  (if (atom topics)
      nil
    (cons (cdr (assoc :from (car topics)))
          (all-topic-froms (cdr topics)))))

(let ((topics (xdoc::get-xdoc-table (w state))))
  (pairlis$ (xdoc::all-topic-names topics)
            (all-topic-froms topics)))

;; ACL2::UNSIGNED-BYTE-P-LEMMAS: unknown: Not logical name:
;; ACL2::UNSIGNED-BYTE-P-LEMMAS.
;; ACL2::SIGNED-BYTE-P-LEMMAS: unknown: Not logical name:
;; ACL2::SIGNED-BYTE-P-LEMMAS.
;; ACL2::IHS: unknown: Not logical name: ACL2::IHS.
;; ACL2::DATA-STRUCTURES: unknown: Not logical name: ACL2::DATA-STRUCTURES.
;; ACL2::B*-BINDERS: unknown: Not logical name: ACL2::B*-BINDERS.

(acl2::defdoc-include-book-path 'acl2::ihs (w state))



||#
