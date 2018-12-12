(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/satlink/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "centaur/aignet/portcullis" :dir :system)
(include-book "centaur/ipasir/portcullis" :dir :system)

(defpkg "EXSIM"
  (append '(ipasir::ipasir ipasir::ipasirp
            ipasir::ipasir$a->status ipasir::ipasir$a->new-clause
            ipasir::ipasir-val ipasir::ipasir-solve ipasir::ipasir-add-clauses
            ipasir::ipasir-init ipasir::ipasir-release ipasir::ipasir-reinit
            ipasir::ipasir-cancel-new-clause ipasir::ipasir-input
            ipasir::ipasir-get-status
            ipasir::ipasir-empty-new-clause
            aignet::litarr
            aignet::get-lit
            aignet::id->slot
            aignet::snode->type
            aignet::snode->fanin
            aignet::snode->regp
            aignet::aignet-case
            aignet::default-gatesimp
            aignet::node-listp
            aignet::aignet-copy-dfs-setup
            aignet::co-id->fanin
            aignet::sat-next-var$
            aignet::sat-lits-empty
            aignet::lits-max-id-val
            aignet::aignet-lit-list->ipasir+off
            aignet::aignet-lit-list->cnf
            aignet::sat-lits-wfp
            aignet::aignet-id-has-sat-var
            aignet::lit-id aignet::lit-neg
            aignet::aignetp
            aignet::aignet-id->sat-lit
            aignet::sat-lits
            aignet::mk-lit
            aignet::innum->id
            aignet::num-ins
            aignet::outnum->fanin
            aignet::num-outs
;;            aignet::num-nodes
            aignet::num-fanins
            aignet::non-bool-atom-listp
            aignet::aignet-lit-listp
            aignet::comb-transformlist-p
            aignet::gatesimp-p
            aignet::strash
            aignet::strashtab-init
            aignet::mark
            aignet::consecutive-vars-to-varmap
            aignet::aignet2
            aignet::aignet-add-ins
            aignet::aignet-add-outs
            aignet::aiglist-to-aignet-top
            aignet::apply-comb-transforms!
            aignet::set-lit
            aignet::lits-length
            aignet::resize-lits
            aignet::resize-u32
            aignet::aignet-count-refs
            aignet::aignet-refcounts
            aignet::aignet-copy-dfs-rec
            aignet::aignet-idp
            aignet::aignet-litp
            aignet::aignet-copies-in-bounds
            aignet::u32-length
            aignet::aignet-lit-listp
            vl->sv-design
            vcd-parent-map-p
            vcd-parent-map
            vcd-child-map-p
            vcd-child-map
            vcd-var-map-p
            vcd-var-map
            vcd-var-elem-p
            vcd-var-elem->v-size
            vcd-var-elem->v-type
            vcd-var-elem->v-vec
            vcd-var-elem->v-id
            vcd-var-elem
            rev! append!
            seed-random$
            rand randp update-seed genrandom
            non-exec
            b*
            bitp
            lnfix
            lbfix
            bfix
            b-not
            b-and
            b-ior
            b-xor
            b-eqv
            b-ite
            bool->bit
            bit->bool
            defxdoc
            defsection
            defstobj-clone
            list-fix
            list-equiv
            set-equiv
            nat-equiv
            bit-equiv
            bits-equiv
            rev
            duplicity
            alist-keys
            alist-vals
            hons-remove-duplicates
            set-reasoning
            enable*
            disable*
            e/d*
            nxt-tbl-elem nxt-tbl-p nxt-tbl-elem-p
            nxt-tbl-keys nxt-tbl-vals
            nxt-tbl-elem->wire nxt-tbl-elem->port nxt-tbl-elem->supp
            nxt-tbl-elem->step nxt-tbl-elem->reset nxt-tbl-elem->subs
            vcd$ read-vcd-file-to-vcd$ vcd$-val-chg-lst snap
            bitarr get-bit set-bit bits-length resize-bits bits-equiv
            natarr get-nat set-nat nats-length resize-nats nats-equiv
            tshell-call tshell-start tshell-stop tshell-ensure
            satlink boolean-reasoning gl tshell)
          (remove1 'true-list-fix ; removed by Matt K. 12/2018, when added to *acl2-exports*
                   (union-eq *acl2-exports*
                             *common-lisp-symbols-from-main-lisp-package*
                             *aignet-exports*
                             *aignet-imports*
                             satlink::*satlink-exports*
                             std::*std-exports*
                             *bitops-exports*
                             *stobjs-exports*
                             (remove-eq 'clause acl2::*standard-acl2-imports*)))))
