
(in-package "SVL")

(include-book "svl")

(include-book "tools/flag" :dir :system)


(local
 (defthm queue-mem-p-of-cons
   (implies (and (queue-mem-p queue-mem)
                 (OCC-NAME-P OCC-NAME))
            (QUEUE-MEM-P (CONS (LIST OCC-NAME) QUEUE-MEM)))))

(local
 (defthm queue-mem-of-last
   (QUEUE-MEM-P
    (*
     4
     (LEN (SVL-MODULE->OCCS (CDR (HONS-ASSOC-EQUAL MODULE-NAME
                                                   SVL-MODULES))))))))

(local
 (defthm QUEUE-P-lemma
   (implies (and (CONSP QUEUE)
                 (QUEUE-P queue))
            (QUEUE-P (CDR QUEUE)))))

(local
 (defthm QUEUE-P-lemma-2
   (implies (and (CONSP QUEUE)
                 (QUEUE-P queue))
            (OCC-NAME-P (CAR QUEUE)))))

(local
 (defthm cons-assign-cdr-occ-is-occ
   (implies (and (EQUAL (OCC-KIND OCC) :ASSIGN)
                 (OCC-P OCC))
            (equal (CONS :ASSIGN (CDR OCC))
                   occ))
   :hints (("Goal"
            :in-theory (e/d (occ-p
                             occ-kind) ())))))

(local
 (defthm cons-module-cdr-occ-is-occ
   (implies (and (EQUAL (OCC-KIND OCC) :module)
                 (OCC-P OCC))
            (equal (CONS :module (CDR OCC))
                   occ))
   :hints (("Goal"
            :in-theory (e/d (occ-p
                             occ-kind) ())))))


(defthm-svl-run-cycle
  (defthm return-val-of--svl-run-cycle
    (implies (and (stringp module-name)
                  (sv::4veclist-p inputs)
                  (svl-env-p delayed-env)
                  (svl-module-alist-p svl-modules))
             (and (sv::4veclist-p
                   (mv-nth 0 (svl-run-cycle module-name inputs delayed-env
                                            svl-modules)))
                  (svl-env-p
                   (mv-nth 1 (svl-run-cycle module-name inputs delayed-env
                                            svl-modules)))))
    :flag svl-run-cycle)

  (defthm return-val-of-svl-run-occ
    (implies (and (occ-p occ)
                  (occ-name-p occ-name)
                  (queue-p new-queue)
                  (queue-mem-p queue-mem)
                  (svl-env-p delayed-env)
                  (svl-env-alist-p next-delayed-env.modules)
                  (sv::svex-env-p env-wires)
                  (occ-name-alist-p listeners)
                  (svl-module-alist-p svl-modules))
             (b* (((mv res-env-wires new-new-queue
                       queue-mem new-next-delayed-env.modules)
                   (svl-run-occ occ-name occ new-queue
                                queue-mem
                                delayed-env
                                next-delayed-env.modules
                                env-wires
                                listeners
                                svl-modules)))
               (and (sv::svex-env-p res-env-wires)
                    (queue-p new-new-queue)
                    (queue-mem-p queue-mem)
                    (svl-env-alist-p new-next-delayed-env.modules))))
    :flag svl-run-occ)

  (defthm return-val-of-svl-run-this-queue
    (implies (and (queue-p queue)
                  (queue-mem-p queue-mem)
                  (svl-env-p delayed-env)
                  (svl-env-alist-p next-delayed-env.modules)
                  (sv::svex-env-p env-wires)
                  (occ-alist-p occs)
                  (occ-name-alist-p listeners)
                  (svl-module-alist-p svl-modules)
                  )
             (b* (((mv res-env-wires new-new-queue
                       queue-mem new-next-delayed-env.modules)
                   (svl-run-this-queue queue
                                       queue-mem
                                       delayed-env
                                       next-delayed-env.modules
                                       env-wires
                                       occs
                                       listeners
                                       svl-modules
                                       limit)))
               (and (sv::svex-env-p res-env-wires)
                    (queue-p new-new-queue)
                    (queue-mem-p queue-mem)
                    (svl-env-alist-p new-next-delayed-env.modules))))
    :flag svl-run-this-queue)

  (defthm return-val-of-svl-run-queue
    (implies (and (queue-p queue)
                  (queue-mem-p queue-mem)
                  (svl-env-p delayed-env)
                  (svl-env-alist-p next-delayed-env.modules)
                  (sv::svex-env-p env-wires)
                  (occ-alist-p occs)
                  (occ-name-alist-p listeners)
                  (svl-module-alist-p svl-modules)
                  )
             (b* (((mv new-env-wires
                       new-next-delayed-env.modules)
                   (svl-run-queue queue
                                  queue-mem
                                  delayed-env
                                  next-delayed-env.modules
                                  env-wires
                                  occs
                                  listeners
                                  svl-modules
                                  limit)))
               (and (sv::svex-env-p new-env-wires)
                    (svl-env-alist-p new-next-delayed-env.modules))))
    :flag svl-run-queue)
  :hints (("Goal"
           :in-theory (e/d (SVL-RUN-QUEUE
                            svl-run-this-queue
                            svl-run-cycle
                            svl-run-occ)
                           (QUEUE-MEM-P
                            well-ranked-module
                            queue-p)))))


#|(defthm occ-name-p-means-svar-p
  (implies (occ-name-p x)
           (sv::svar-p x))
  :hints (("Goal"
           :in-theory (e/d (occ-name-p
                            sv::svar-p) ()))))||#

(defthm SVEX-ENV-P-of-HONS-GETS-FAST-ALIST
  (implies (and (sv::svarlist-p names)
                (sv::svex-env-p env))
           (sv::svex-env-p (hons-gets-fast-alist names env)))
  :hints (("Goal"
           :expand (HONS-GETS-FAST-ALIST (CDR NAMES) NIL)
           :induct (hons-gets-fast-alist names env)
           :do-not-induct t
           :in-theory (e/d (hons-gets-fast-alist
                            SV::SVAR-P
                            occ-name-p
                            svex-env-p
                            occ-name-list-p)
                           ()))))

(verify-guards svl-run-cycle
  :hints (("Goal"
           :in-theory (e/d () (WELL-RANKED-MODULE
                               QUEUE-P
                               QUEUE-MEM-P)))))
