; ACL2 versions of (some of) the Top 100 Theorems List
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;; Include here any books that contain theorems cited below:
(include-book "arithmetic/binomial" :dir :system)
(include-book "nonstd/nsa/sqrt-2" :dir :system)
(include-book "projects/groups/abelian" :dir :system)
(include-book "projects/groups/quotients" :dir :system)
(include-book "projects/groups/sylow" :dir :system)
(include-book "projects/numbers/ballot" :dir :system)
(include-book "projects/numbers/birthday" :dir :system)
(include-book "projects/numbers/derangements" :dir :system)
(include-book "projects/numbers/divisors" :dir :system)
(include-book "projects/numbers/div3" :dir :system)
(include-book "projects/numbers/eisenstein" :dir :system)
(include-book "projects/numbers/euclid" :dir :system)
(include-book "projects/numbers/euler" :dir :system)
(include-book "projects/numbers/girard" :dir :system)
(include-book "projects/numbers/harmonic" :dir :system)
(include-book "projects/numbers/konigsberg" :dir :system)
(include-book "projects/numbers/partitions" :dir :system)
(include-book "projects/numbers/subseq" :dir :system)
(include-book "projects/numbers/subsets" :dir :system)
(include-book "projects/numbers/sum4squares" :dir :system)
(include-book "projects/numbers/triangular" :dir :system)
(include-book "projects/numbers/triples" :dir :system)
(include-book "projects/numbers/z2q" :dir :system)
(include-book "projects/schroeder-bernstein/schroeder-bernstein" :dir :system)
(include-book "projects/linear/reduction" :dir :system)
(include-book "workshops/2006/cowles-gamboa-euclid/Euclid/prime-fac" :dir :system)
(include-book "projects/set-theory/cantor" :dir :system)
(include-book "projects/set-theory/schroeder-bernstein" :dir :system)
;; (include-book "workshops/2018/kwan-greenstreet/cauchy-schwarz" :dir :system) ; needs ACL2r
;; (include-book "workshops/2020/kwan-peng-greenstreet/abstract-cs" :dir :system) ; needs ACL2r

;; TODO: How to support theorems only provable in acl2(r)?

(defxdoc 100-theorems
    :short "ACL2 versions of (some of) the Top 100 Theorems List"
    :parents (math)
    :long
    (concatenate
     'string
     "<p>This page collects those theorems from the <a href=\"https://www.cs.ru.nl/~freek/100/\">Formalizing 100 Theorems</a> page that have been proved in ACL2.</p>"

     "<p>Note that ACL2 has largely focused on proving theorems that are rather different from these (e.g., the correctness of large and complex hardware designs).</p>"

     ;; General format of each entry in this list:
     ;; - heading
     ;; - theorem statement, captured using @def
     ;; - link to code (github)
     ;; - link to xdoc, if any
     ;; - notes, if any

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; TODO: These id=... arguments don't seem to create internal links:
     "<h3 id=\"1\">1. The Irrationality of the Square Root of 2</h3>"

     "@(def irrational-sqrt-2)"

     "<p>By Ruben Gamboa, in <a href=\"https://github.com/acl2/acl2/blob/master/books/nonstd/nsa/sqrt-2.lisp\">books/nonstd/nsa/sqrt-2.lisp</a>.</p>"

     ;; "<p>Doc:</p>"

     ;; "<p>Notes:</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"2\">2. Fundamental Theorem of Algebra</h3>"

     "<p>Theorems @('fundamental-theorem-of-algebra') and @('fundamental-theorem-of-algebra-sk').</p>"

     "<p>By Ruben Gamboa and John Cowles, in <a href=\"https://github.com/acl2/acl2/blob/master/books/workshops/2018/gamboa-cowles/complex-polynomials.lisp\">books/workshops/2018/gamboa-cowles/complex-polynomials.lisp</a>.</p>"

     "<p>Note: These theorems require <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"3\">3. The Denumerability of the Rational Numbers</h3>"

     "@(def dm::q2z-bi-z2q)"
     "@(def dm::z2q-q2z-bi)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/z2q.lisp\">books/projects/numbers/z2q.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"4\">4. Pythagorean Theorem</h3>"
     ;; "<h3 id=\"5\">5. Prime Number Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"6\">6. Godel's Incompleteness Theorem</h3>"

     "<p>By Natarajan Shankar, using Nqthm, a predecessor to ACL2.</p>"

     "<p>See <a href=\"https://www.cs.utexas.edu/users/boyer/ftp/nqthm/nqthm-1992/examples/shankar/goedel.events\">this file</a>.  See also <a href=\"https://philpapers.org/rec/SHAMMA-3\">this book</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"7\">7. Law of Quadratic Reciprocity</h3>"

     "@(def dm::quadratic-reciprocity)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/eisenstein.lisp\">books/projects/numbers/eisenstein.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"8\">8. The Impossibility of Trisecting the Angle and Doubling the Cube</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"9\">9. The Area of a Circle</h3>"

     "<p>Theorem @('circle-area').</p>"

     "<p>By Jagadish Bapanapally, in <a href=\"https://github.com/acl2/acl2/blob/master/books/nonstd/circles/area-of-a-circle/area-of-a-circle-2.lisp\">books/nonstd/circles/area-of-a-circle/area-of-a-circle-2.lisp</a>.</p>"

     "<p>Note: This theorem requires <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"10\">10. Euler's Generalization of Fermat's Little Theorem</h3>"

     "@(def dm::euler-totient)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/groups/abelian.lisp\">books/projects/groups/abelian.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"11\">11. The Infinitude of Primes</h3>"

     "@(def dm::infinitude-of-primes)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/euclid.lisp\">books/projects/numbers/euclid.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"12\">12. The Independence of the Parallel Postulate</h3>"
     ;; "<h3 id=\"13\">13. Polyhedron Formula</h3>"
     ;; "<h3 id=\"14\">14. Euler's Summation of 1 + (1/2)^2 + (1/3)^2 + ....</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"15\">15. Fundamental Theorem of Integral Calculus</h3>"

     "<p>Theorem @('fundamental-theorem-of-calculus').</p>"

     "<p>By Matt Kaufmann, in <a href=\"https://github.com/acl2/acl2/blob/master/books/nonstd/workshops/1999/calculus/book/fundamental-theorem-of-calculus.lisp#L136\">books/nonstd/workshops/1999/calculus/book/fundamental-theorem-of-calculus.lisp</a>.</p>"

     "<p>Note: This theorem requires <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"16\">16. Insolvability of General Higher Degree Equations</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"17\">17. De Moivre's Theorem</h3>"

     "<p>Theorem @('de-moivre-1').</p>"

     "<p>By Ruben Gamboa, in <a href=\"https://github.com/acl2/acl2/blob/master/books/workshops/2018/gamboa-cowles/de-moivre.lisp\">books/workshops/2018/gamboa-cowles/de-moivre.lisp</a>.</p>"

     "<p>Note: This theorem requires <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"18\">18. Liouville's Theorem and the Construction of Transcendental Numbers</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"19\">19. Four Squares Theorem</h3>"

     "@(def dm::nat-sum-of-4-squares)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/sum4squares.lisp\">books/projects/numbers/sum4squares.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"20\">20. All Primes (1 mod 4) Equal the Sum of Two Squares</h3>"

     "@(def dm::prime-sum-squares)"
     "@(def dm::prime-sum-squares-converse)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/girard.lisp\">books/projects/numbers/girard.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"21\">21. <u>Green's Theorem</u></h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"22\">22. The Non-Denumerability of the Continuum</h3>"

     "<p>Theorem @('reals-are-not-countable').</p>"

     "<p>By Ruben Gamboa and John Cowles, in <a href=\"https://github.com/acl2/acl2/blob/master/books/nonstd/transcendentals/reals-are-uncountable-1.lisp\">books/nonstd/transcendentals/reals-are-uncountable-1.lisp</a>.</p>"

     "<p>Note: This theorem requires <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"23\">23. Formula for Pythagorean Triples</h3>"

     "@(def dm::pyth-trip-sufficiency)"
     "@(def dm::pyth-trip-necessity)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/triples.lisp\">books/projects/numbers/triples.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"24\">24. <u>The Undecidability of the Continuum Hypothesis</u></h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"25\">25. Schroeder-Bernstein Theorem</h3>"

     "@(def sbt::injectivity-of-sb)"
     "@(def sbt::surjectivity-of-sb)"

     "<p>By Grant Jurgensen, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/schroeder-bernstein/schroeder-bernstein.lisp\">books/projects/schroeder-bernstein/schroeder-bernstein.lisp</a>.</p>"

     "@(def zf::schroeder-bernstein)"

     "<p>An alternate formulation in pure set theory by Matt Kaufmann, derived
     from Grant Jurgensen's proof and statement, in <a
     href=\"https://github.com/acl2/acl2/blob/master/books/projects/set-theory/schroeder-bernstein.lisp#L28\">books/projects/set-theory/schroeder-bernstein.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"26\">26. Leibniz's Series for Pi</h3>"
     ;; "<h3 id=\"27\">27. Sum of the Angles of a Triangle</h3>"
     ;; "<h3 id=\"28\">28. Pascal's Hexagon Theorem</h3>"
     ;; "<h3 id=\"29\">29. Feuerbach's Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"30\">30. The Ballot Problem</h3>"

     "@(def dm::ballot-theorem)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/ballot.lisp\">books/projects/numbers/ballot.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"31\">31. Ramsey's Theorem</h3>"

     "<p>By Matt Kaufmann, using PC-Nqthm, a predecessor to ACL2.</p>"

     "<p>Note: Only the exponent-2 Ramsey Theorem for two partitions.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"32\">32. <u>The Four Color Problem</u></h3>"
     ;; "<h3 id=\"33\">33. <i><u>Fermat's Last Theorem</u></i></li></h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"34\">34. Divergence of the Harmonic Series</h3>"

     "@(def harmonic-series-diverges)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/harmonic.lisp\">books/projects/numbers/harmonic.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"35\">35. Taylor's Theorem</h3>"

     "<p>By Ruben Gamboa and Brittany Middleton.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"36\">36. Brouwer Fixed Point Theorem</h3>"
     ;; "<h3 id=\"37\">37. The Solution of a Cubic</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"38\">38. Arithmetic Mean/Geometric Mean</h3>"

     "<p>By Matt Kaufmann, using Nqthm, a predecessor to ACL2.</p>"

     "<p>See: <a href=\"https://link.springer.com/article/10.1007/BF00244463\">this paper</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"39\">39. Solutions to Pell's Equation</h3>"
     ;; "<h3 id=\"40\">40. Minkowski's Fundamental Theorem</h3>"
     ;; "<h3 id=\"41\">41. Puiseux's Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"42\">42. Sum of the Reciprocals of the Triangular Numbers</h3>"

     "@(def tri-recip-sum-limit)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/triangular.lisp\">books/projects/numbers/triangular.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"43\">43. <u>The Isoperimetric Theorem</u></h3>"

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"44\">44. The Binomial Theorem</h3>"

     "@(def binomial-theorem)"

     "<p>By Ruben Gamboa, in <a href=\"https://github.com/acl2/acl2/blob/master/books/arithmetic/binomial.lisp\">books/arithmetic/binomial.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"45\">45. The Partition Theorem</h3>"

     "@(def dm::dlistp-odd-parts)"
     "@(def dm::odd-partp-odd-parts)"
     "@(def dm::odd-parts-perm-equal)"
     "@(def dm::perm-odd-parts)"
     "@(def dm::dlistp-dis-parts)"
     "@(def dm::dis-partp-dis-parts)"
     "@(def dm::dis-parts-perm-equal)"
     "@(def dm::dis-partp-dis-parts)"
     "@(def dm::perm-dis-parts)"
     "@(def dm::len-dis-parts)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/partitions.lisp\">books/projects/numbers/partitions.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"46\">46. The Solution of the General Quartic Equation</h3>"
     ;; "<h3 id=\"47\">47. The Central Limit Theorem</h3>"
     ;; "<h3 id=\"48\">48. <u>Dirichlet's Theorem</u></h3>"
     ;; "<h3 id=\"49\">49. The Cayley-Hamilton Theorem</h3>"
     ;; "<h3 id=\"50\">50. The Number of Platonic Solids</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"51\">51. Wilson's Theorem</h3>"

     "@(def dm::wilson)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/euler.lisp\">books/projects/numbers/euler.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"52\">52. The Number of Subsets of a Set</h3>"

     "@(def dm::len-subsets)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/subsets.lisp\">books/projects/numbers/subsets.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"53\">53. Pi is Transcendental</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"54\">54. Konigsberg Bridges Problem</h3>"

     "@(def dm::konigsberg)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/konigsberg.lisp\">books/projects/numbers/konigsberg.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"55\">55. Product of Segments of Chords</h3>"
     ;; "<h3 id=\"56\">56. The Hermite-Lindemann Transcendence Theorem</h3>"
     ;; "<h3 id=\"57\">57. Heron's Formula</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"58\">58. Formula for the Number of Combinations</h3>"

     "@(def dm::len-subsets-of-order)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/subsets.lisp\">books/projects/numbers/subsets.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


     ;; "<h3 id=\"59\">59. The Laws of Large Numbers</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


     ;; "<h3 id=\"60\">60. Bezout's Theorem</h3>"

     ;; TODO: John Cowles proved this?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"61\">61. Theorem of Ceva</h3>"
     ;; "<h3 id=\"62\">62. Fair Games Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"63\">63. Cantor's Theorem</h3>"

     "@(def zf::cantor)"

     "<p>By Matt Kaufmann, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/set-theory/cantor.lisp#L79\">books/projects/set-theory/cantor.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"64\">64. L'Hopital's Rule</h3>"
     ;; "<h3 id=\"65\">65. Isosceles Triangle Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"66\">66. Sum of a Geometric Series</h3>"

     "<p>Theorem @('sumlist-geometric').</p>"

     "<p>By Ruben Gamboa, in <a href=\"https://github.com/acl2/acl2/blob/master/books/nonstd/nsa/exp.lisp\">books/nonstd/nsa/exp.lisp</a>.</p>"

     "<p>Note: This theorem requires <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"67\">67. e is Transcendental</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"68\">68. Sum of an arithmetic series</h3>"

     ;; TODO: Ruben Gamboa proved this?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"69\">69. Greatest Common Divisor Algorithm</h3>"

     "@(def dm::gcd-divides)"
     "@(def dm::divides-gcd)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/euclid.lisp\">books/projects/numbers/euclid.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"70\">70. The Perfect Number Theorem</h3>"

     "@(def dm::perfectp-sufficiency)"
     "@(def dm::perfectp-necessity)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/divisors.lisp\">books/projects/numbers/divisors.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"71\">71. Order of a Subgroup</h3>"

     "@(def dm::lagrange)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/groups/quotients.lisp\">books/projects/groups/quotients.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"72\">72. Sylow's Theorem</h3>"

     "@(def dm::sylow-1)"
     "@(def dm::sylow-2)"
     "@(def dm::sylow-3)"
     "@(def dm::sylow-4)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/groups/sylow.lisp\">books/projects/groups/sylow.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"73\">73. Ascending or Descending Sequences</h3>"

     "@(def dm::asc-desc-subseqp)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/subseq.lisp\">books/projects/numbers/subseq.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"74\">74. The Principle of Mathematical Induction</h3>"

     "@({
(encapsulate (((p *) => *))
  (local (defun p (n) n))
  (defthm p-0
    (p 0))
  (defthm p-recurrence
    (implies (and (natp n) (p n))
             (p (1+ n)))))

(defun n-induction (n)
  (if (posp n)
      (list (n-induction (1- n)))
    (list n)))

(defthm mathematical-induction
  (implies (natp n) (p n))
  :hints ((\"Goal\" :induct (n-induction n))
          (\"Subgoal *1/1\" :use ((:instance p-recurrence (n (1- n)))))))
      })"

     "<p>By David Russinoff.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"75\">75. The Mean Value Theorem</h3>"

     "<p>Theorems @('mvt-theorem') and @('mvt-theorem-sk').</p>"

     "<p>By Ruben Gamboa, in <a href=\"https://github.com/acl2/acl2/blob/master/books/nonstd/nsa/derivatives.lisp\">books/nonstd/nsa/derivatives.lisp</a>.</p>"

     "<p>Note: These theorems require <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"76\">76. Fourier Series</h3>"
     ;; "<h3 id=\"77\">77. Sum of kth powers</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"78\">78. The Cauchy-Schwarz Inequality</h3>"

     "<p>Theorems @('cauchy-schwarz-1'), @('cauchy-schwarz-2'), @('cauchy-schwarz-3'), and @('cauchy-schwarz-4').</p>"

     "<p>By Carl Kwan and Mark R. Greenstreet, in <a href=\"https://github.com/acl2/acl2/blob/master/books/workshops/2018/kwan-greenstreet/cauchy-schwarz.lisp\">books/workshops/2018/kwan-greenstreet/cauchy-schwarz.lisp</a>.</p>"

     "<p>Note: These theorems require <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

     "<p>Theorems @('cs1'), @('cs2'), @('cs1-equality-implies-linear-dependence'), @('cs2-equality-implies-linear-dependence'), @('linear-dependence-implies-cs1-equality'), and @('linear-dependence-implies-cs2-equality').</p>"

     "<p>By Carl Kwan, Yan Peng, and Mark R. Greenstreet, in <a href=\"https://github.com/acl2/acl2/blob/master/books/workshops/2020/kwan-peng-greenstreet/abstract-cs.lisp\">books/workshops/2020/kwan-peng-greenstreet/abstract-cs.lisp</a>.</p>"

     "<p>Note: These theorems require <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"79\">79. The Intermediate Value Theorem</h3>"

     "<p>Theorems @('intermediate-value-theorem')and @('intermediate-value-theorem-sk').</p>"

     "<p>By Ruben Gamboa, in <a href=\"https://github.com/acl2/acl2/blob/master/books/nonstd/nsa/continuity.lisp\">books/nonstd/nsa/continuity.lisp</a>.</p>"

     "<p>Note: These theorems require <see topic=\"@(url real)\">ACL2(r)</see>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"80\">80. The Fundamental Theorem of Arithmetic</h3>"

     "<h4>First solution:</h4>"

     "@(def pos::product-lst-prime-factors)"
     "@(def pos::prime-factorization-uniqueness)"

     "<p>By Ruben Gamboa and John Cowles, in <a href=\"https://github.com/acl2/acl2/blob/master/books/workshops/2006/cowles-gamboa-euclid/Euclid/prime-fac.lisp\">books/workshops/2006/cowles-gamboa-euclid/Euclid/prime-fac.lisp</a>.</p>"

     "<h4>Second solution:</h4>"

     "@(def dm::prime-fact-existence)"
     "@(def dm::prime-fact-uniqueness)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/euclid.lisp\">books/projects/numbers/euclid.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"81\">81. Divergence of the Prime Reciprocal Series</h3>"

     ;; TODO: Uncomment once available:
     ;; "@(def thm-series-Recip-prime-divergess-traditional)"
     ;; "@(def i-large-sumRecip-prime-upto-n-i-large-integer)"

     "<p>Theorems @('thm-series-Recip-prime-divergess-traditional') and @('i-large-sumRecip-prime-upto-n-i-large-integer').</p>"

     ;; TODO: Fixup when code is available.
     "<p>By Ruben Gamboa.</p>"
     ;;     "<p>By Ruben Gamboa, in <a href=\"https://github.com/acl2/acl2/blob/master/books/workshops/2013/cowles-gamboa/sum-recip-prime.lisp\">books/workshops/2013/cowles-gamboa/sum-recip-prime.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"82\">82. Dissection of Cubes (J.E. Littlewood's "elegant" proof)</h3>"
     ;; "<h3 id=\"83\">83. The Friendship Theorem</h3>"
     ;; "<h3 id=\"84\">84. Morley's Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"85\">85. Divisibility by 3 Rule</h3>"

     "@(def dm::divides-3-sum-list-digits)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/div3.lisp\">books/projects/numbers/div3.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"86\">86. Lebesgue Measure and Integration</h3>"
     ;; "<h3 id=\"87\">87. Desargues's Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"88\">88. Derangements Formula</h3>"

     "@(def dm::derangements-formula)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/derangements.lisp\">books/projects/numbers/derangements.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


     ;; "<h3 id=\"89\">89. The Factor and Remainder Theorems</h3>"
     ;; "<h3 id=\"90\">90. Stirling's Formula</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"91\">91. The Triangle Inequality</h3>"

     ;; TODO: Ruben Gamboa proved this?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"92\">92. Pick's Theorem</h3>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"93\">93. The Birthday Problem</h3>"

     "@(def dm::probability-of-repetition-value)"
     "@(def dm::probability-of-repetition-22)"
     "@(def dm::probability-of-repetition-23)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/birthday.lisp\">books/projects/numbers/birthday.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"94\">94. The Law of Cosines</h3>"
     ;; "<h3 id=\"95\">95. Ptolemy's Theorem</h3>"

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"96\">96. Principle of Inclusion/Exclusion</h3>"

     "@(def dm::inclusion-exclusion-principle)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/numbers/sylvester.lisp\">books/projects/numbers/sylvester.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     "<h3 id=\"97\">97. Cramer's Rule</h3>"

     "@(def dm::cramer)"

     "<p>By David Russinoff, in <a href=\"https://github.com/acl2/acl2/blob/master/books/projects/linear/reduction.lisp\">projects/linear/reduction.lisp</a>.</p>"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; "<h3 id=\"98\">98. Bertrand's Postulate</h3>"
     ;; "<h3 id=\"99\">99. Buffon Needle Problem</h3>"
     ;; "<h3 id=\"100\">100. Descartes Rule of Signs</h3>"
     ))
