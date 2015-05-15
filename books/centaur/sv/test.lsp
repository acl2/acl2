

(include-book "centaur/tutorial/intro" :dir :system)
(include-book "vl-svex")


#!vl
(defmodules *boothmul-translation*
  ;; Translate the Verilog
  (vl::make-vl-loadconfig
   :start-files (list "/share/apps/fv/sswords/work/cn/e/acl2/books/centaur/tutorial/boothmul.v")))
   :edition :verilog-2005))

(defconsts
  (*res-assigns* *modalist* *good* *bad* moddb aliases)
  (vl->svex-assigns (vl::vl-translation->orig vl::*boothmul-translation*)
                    "boothmul"
                    vl::*vl-default-simpconfig*
                    moddb aliases))
