; Arithmetic-4 Library
; Copyright (C) 2008 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; dynamic-e-d.lisp
;;;
;;; This book contains a custom keyword hint which allows enabling and
;;; disabling of rules in a dynamic environment.  That is, the
;;; enabling and disabling is done relative to the active theory at
;;; the goal for which the hint applies, rather than the active theory
;;; at the time the proof request was submitted.  Thus, one can do,
;;; for example:
;;;
;;; :hints (("Goal"  :dynamic-e/d (((:rewrite foo))()))
;;;         ("Goal'" :dynamic-e/d (((:rewrite bar))()))
;;;
;;; and have both foo and bar enabled at Goal'.  The effects of the
;;; :dynamic-e/d hints are cumulative.
;;;
;;; The argument to :dynamic-e/d should be a pair of lists:
;;; (<runes to enable> <runes to disable>).  Either list may be empty.
;;; Otherwise it should be a list of runes.  (The summary of rules
;;; used at the end of a proof effort is a list of runes.)
;;;
;;; Improvements to the error handling, or generalizing the operations
;;; so that the two lists can look like those for
;;; :in-theory (e/d <enable list> <disable list>)
;;; is most welcome.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We grab the theory active at the time the hint is encountered.
;;; The theory returned is a list of all the enabled runes.

(defun get-current-dynamic-theory (pspv world)
  (declare (xargs :mode :program))
  ;; We grab the enabled structure from the pspv, and check for the
  ;; index-of-last-enabling.  This index is the number of the rune at
  ;; the time of the last in-theory event, and the enabled structure
  ;; is current as of this index.  The function enabled-runep
  ;; considers a rune to be enabled if it is in the enabled structure,
  ;; or if it's index is greater than the index-of-last-enabling.  See
  ;; enabled-runep.
  (let* ((ens (access rewrite-constant
		      (access prove-spec-var pspv 
			      :rewrite-constant)
		      :current-enabled-structure))
	 (ens-index (access enabled-structure
			    ens
			    :index-of-last-enabling)))
    (if (equal ens-index
	       (+ -1 (get-next-nume world)))
	;; Since the index-of-last-enabling is, in fact, that of the
	;; last rune admited, the ens is up to date.  So we use it to
	;; get our list of currently active runes.
	;;
	;;; In particular, this will be true if there has been an
	;;; :in-theory hint seen earlier in the proof attempt.
	(strip-cdrs (cdr (access enabled-structure 
				 ens
				 :theory-array)))
      ;; The ens is not up to date.  We therefore use the theory
      ;; active at the start of the proof.
      (current-theory-fn :here world))))

(defun dynamic-e/d (e/d keyword-alist pspv world state)
  (declare (xargs :mode :program))
  (let ((enable (car e/d))
	(disable (cadr e/d)))
    ;; We should check that the values supplied to enable and disable
    ;; are lists of runes as expected.
    (let* ((old-theory (get-current-dynamic-theory pspv world))
	   ;; should I use set-union-equal?  Append seems sufficient.
	   (new-theory (set-difference-equal (append enable
						     old-theory)
					     disable)))
      (if (member-equal :in-theory keyword-alist)
	  ;; Improve the error message, or decide what we should do in
	  ;; this case.
	  (er soft 'dynamic-e/d "It is not yet clear to me how dynamic-e/d ~
                                 should interact with user supplied :in-theory ~
                                 hints.  We therefore give up.")
	(let ((new-keyword-alist (splice-keyword-alist :dynamic-e/d
						       `(:in-theory ',new-theory)
						       keyword-alist)))
	  (mv nil new-keyword-alist state))))))

(add-custom-keyword-hint :dynamic-e/d
			 (dynamic-e/d val keyword-alist pspv world state))
