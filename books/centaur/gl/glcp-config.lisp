

(in-package "GL")

(include-book "shape-spec-defs")

(cutil::defaggregate glcp-config
  ((abort-unknown booleanp :default t)
   (abort-ctrex booleanp :default t)
   (exec-ctrex booleanp :default t)
   (abort-vacuous booleanp :default t)
   (nexamples natp :rule-classes :type-prescription :default 3)
   (hyp-clk natp :rule-classes :type-prescription :default 1000000)
   (concl-clk natp :rule-classes :type-prescription :default 1000000)
   (clause-proc-name symbolp :rule-classes :type-prescription)
   (overrides) ;;  acl2::interp-defs-alistp but might be too expensive to check
     ;;  the guards in clause processors
   (param-bfr :default t)
   top-level-term
   (shape-spec-alist shape-spec-bindingsp)
   run-before
   run-after
   case-split-override
   (split-conses booleanp :default nil)
   (split-fncalls booleanp :default nil)
   (lift-ifsp booleanp :default nil)
   )
  :tag :glcp-config)


(defund-inline glcp-config-update-param (p config)
  (declare (xargs :guard (glcp-config-p config)))
  (change-glcp-config config :param-bfr p))

(defthm param-bfr-of-glcp-config-update-param
  (equal (glcp-config->param-bfr (glcp-config-update-param p config))
         p)
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))

(defthm glcp-config->overrides-of-glcp-config-update-param
  (equal (glcp-config->overrides (glcp-config-update-param p config))
         (glcp-config->overrides config))
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))

(defthm glcp-config->top-level-term-of-glcp-config-update-param
  (equal (glcp-config->top-level-term (glcp-config-update-param p config))
         (glcp-config->top-level-term config))
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))



(defund-inline glcp-config-update-term (term config)
  (declare (xargs :guard (glcp-config-p config)))
  (change-glcp-config config :top-level-term term))

(defthm param-bfr-of-glcp-config-update-term
  (equal (glcp-config->param-bfr (glcp-config-update-term term config))
         (glcp-config->param-bfr config))
  :hints(("Goal" :in-theory (enable glcp-config-update-term))))

(defthm glcp-config->overrides-of-glcp-config-update-term
  (equal (glcp-config->overrides (glcp-config-update-term term config))
         (glcp-config->overrides config))
  :hints(("Goal" :in-theory (enable glcp-config-update-term))))

(defthm glcp-config->top-level-term-of-glcp-config-update-term
  (equal (glcp-config->top-level-term (glcp-config-update-term term config))
         term)
  :hints(("Goal" :in-theory (enable glcp-config-update-term))))


