#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "PATH")

;; bzo bzo bzo this whole file is terrible, figure out which of these belong
;; in here and which of these belong in graphs.  (We don't have a clean
;; separation of the libraries yet.)

(defconst *exports*
  '(
    keys
    vals
    range
    dup

    dia
    implies@
    enlist

    dominates
    strictly-dominates
    dominated-by-some
    strictly-dominated-by-some
    dominates-some
    diverge
    diverges-from-all
    all-diverge-from-all
    all-diverge
    all-dominated-by-some

    psorted
    psort

    wfpath

    gp
    sp
    cp
    mp

    gp-list
    clrp-list

    wf-graph
    use
    def
    defun*
    defmodel
    defmodeld
    defgraph
    defproof

    ))
