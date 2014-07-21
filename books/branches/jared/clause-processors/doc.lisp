(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc clause-processor-tools
  :parents (clause-processor proof-automation)
  :short "Noteworthy clause-processors"
  :long "<p>Some noteworthy clause-processors include:</p>

  <ul>
    <li>tools/defevaluator-fast<br />
       <p>Basically like defevaluator but faster when you have a lot of
          functions in your evaluator.</p></li>

    <li>clause-processor/join-thms<br />
      <p>The DEF-JOIN-THMS macro adds theorems about conjoin, disjoin, etc
         for your evaluator</p></li>

    <li>clause-processors/unify-subst<br />
      <p>The DEF-UNIFY macro proves a unify/substitution algorithm correct
         for your evaluator</p></li>

    <li>clause-processors/meta-extract-user<br />
      <p>The DEF-META-EXTRACT macro sets up support for using the meta-extract
         stuff to assume facts from the world are correct</p>
  </ul>")
