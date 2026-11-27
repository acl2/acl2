; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../network")
(set-induction-depth-limit 1)

; Inbox Utility ---------------------------------------------------------------

; Check if the inbox contains a message structured as {pid, _},
; a patern commonly used in Erlang programs.
(define inbox-contains ((inbox erl-vlst-p) (pid pid-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) nil)
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid))) t))
      (inbox-contains (cdr inbox) pid))
  ///
    (defcong erl-vlst-equiv equal (inbox-contains inbox pid) 1)
    (defcong pid-equiv equal (inbox-contains inbox pid) 2)
    
    (defrule inbox-contains-of-append-1
      (implies
        (and (erl-vlst-p a) (erl-vlst-p b) (inbox-contains a pid))
        (inbox-contains (append a b) pid)))
    (defrule inbox-contains-of-append-2
      (implies
        (and (erl-vlst-p a) (erl-vlst-p b) (inbox-contains b pid))
        (inbox-contains (append a b) pid)))
    
    (defrule not-inbox-contains-of-car
      (implies
        (and
          (pid-p pid) (consp inbox)
          (not (inbox-contains inbox pid))
          (equal (erl-val-kind (car inbox)) :tuple)
          (equal (len (erl-val-tuple->lst (car inbox))) 2))
        (not (equal (car (erl-val-tuple->lst (car inbox))) pid))))

    (defrule not-inbox-contains-of-cdr
      (implies
        (and (not (inbox-contains inbox pid)) (erl-vlst-p inbox))
        (not (inbox-contains (cdr inbox) pid)))
      :enable erl-vlst-p)

    (defrule inbox-contains-of-append-message
      (implies
        (and
          (erl-vlst-p l) (pid-p pid) (erl-val-p m)
          (equal (erl-val-kind m) :tuple)
          (equal (len (erl-val-tuple->lst m)) 2)
          (equal (car (erl-val-tuple->lst m)) pid))
        (inbox-contains (append l (list m)) pid))))

; Retrive the messages in the inbox that are not structured as structured as {pid, _}.
(define inbox-without ((inbox erl-vlst-p) (pid pid-p))
  :returns (r erl-vlst-p)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) nil)
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid)))
        (cdr inbox)))
      (cons m (inbox-without (cdr inbox) pid)))
  ///
    (defcong erl-vlst-equiv equal (inbox-without inbox pid) 1)
    (defcong pid-equiv equal (inbox-without inbox pid) 2))

; Other PIDs are not affected by inbox-without.
(defrule inbox-without-of-neq-pid
  (implies
    (and (erl-vlst-p inbox) (pid-p pid) (pid-p x)
         (not (equal pid x))
         (inbox-contains inbox pid))
    (inbox-contains (inbox-without inbox x) pid))
  :enable (inbox-contains inbox-without))

; Retrive the value of a message structured as {pid, value}.
; If none exists, return (:none).
(define inbox->value ((inbox erl-vlst-p) (pid pid-p))
  :returns (v erl-val-p)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) (make-erl-val-none))
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid)))
        (cadr (erl-val-tuple->lst m))))
      (inbox->value (cdr inbox) pid))
  ///
    (defcong erl-vlst-equiv equal (inbox->value inbox pid) 1)
    (defcong pid-equiv equal (inbox->value inbox pid) 2))