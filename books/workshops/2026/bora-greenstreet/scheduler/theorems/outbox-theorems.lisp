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

; Some  functions and rules about outboxes.
; TODO: Some of these should be better organized and renamed.

(defrule proc->outbox-of-proc
  (equal (proc->outbox (proc ps s inbox-new inbox-tried klst))
         (erl-state->outbox s))
  :enable proc->outbox)

(defrule head-of-outbox
  (implies
    (and (not (omap::emptyp m)) (outbox-p m))
    (and
      (pid-p (mv-nth 0 (omap::head m)))
      (erl-vlst-p (mv-nth 1 (omap::head m)))))
  :enable outbox-p)

(defrule head-of-outbox-consp
  (implies
    (and
      (not (omap::emptyp m)) (outbox-p m)
      (mv-nth 1 (omap::head m)))
    (consp (mv-nth 1 (omap::head m))))
  :enable (outbox-p erl-vlst-p)
  :disable head-of-outbox
  :use (:instance head-of-outbox))

(defrule lookup-of-outbox-consp
  (implies
    (and (outbox-p m) (omap::assoc k m) (omap::lookup k m))
    (consp (omap::lookup k m)))
  :prep-lemmas
   ((defrule consp-when-erl-vlst-p-and-non-nil
      (implies (and (erl-vlst-p x) x) (consp x))
    :enable erl-vlst-p)))

(defrule bind-of-lookup-of-update-of-outbox
  (implies
    (and (network-p net) (omap::assoc pid net))
    (equal
      (erl-state->bind
        (proc->s
          (omap::lookup q
            (omap::update pid
              (change-proc (omap::lookup pid net)
                :s (update-erl-state->outbox
                     (proc->s (omap::lookup pid net)) ob))
              net))))
      (erl-state->bind (proc->s (omap::lookup q net)))))
  :enable omap::lookup-of-update)

(defrule bind-of-lookup-of-update-when-bind-equal
  (implies
    (and (network-p net) (omap::assoc q net)
         (equal (erl-state->bind (proc->s qproc))
                (erl-state->bind (proc->s (omap::lookup q net)))))
    (equal (erl-state->bind (proc->s (omap::lookup x (omap::update q qproc net))))
           (erl-state->bind (proc->s (omap::lookup x net)))))
  :enable omap::lookup-of-update)

; check if an outbox is empty
(define outbox-emptyp ((outbox outbox-p))
  :returns (r booleanp)
  :measure (acl2-count (outbox-fix outbox))
  :hints (("Goal" :in-theory (enable outbox-p outbox-fix)))
  (b* ((outbox (outbox-fix outbox))
       ((if (omap::emptyp outbox)) t))
      (and (not (omap::head-val outbox))
           (outbox-emptyp (omap::tail outbox))))
  ///
    (defcong outbox-equiv equal (outbox-emptyp outbox) 1)
    
    (defrule lookup-when-outbox-emptyp
      (implies
        (and (outbox-p outbox) (outbox-emptyp outbox))
        (not (omap::lookup k outbox)))
      :enable omap::lookup)
    
    (defrule outbox-emptyp-of-drain
      (implies
        (and (outbox-p outbox)
             (omap::assoc parent outbox)
             (omap::emptyp (omap::tail outbox)))
        (outbox-emptyp (omap::update parent nil outbox)))
      :use ((:instance omap::assoc-of-tail-when-not-head
              (key parent) (map outbox)))))