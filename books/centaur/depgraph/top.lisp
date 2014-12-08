; Basic Dependency Graphs
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "DEPGRAPH")
(include-book "toposort")
(include-book "transdeps")
(include-book "invert")
(include-book "mergesort-alist-values")

(defxdoc depgraph
  :parents (acl2::alists)
  :short "A small library for working with dependency graphs."

  :long "<p>This is just a small collection of basic graph algorithms for
working with dependency graphs.</p>


<h3>Graph Representation</h3>

<p>We represent dependency graphs as simple @(see acl2::alists) that bind nodes
to the lists of nodes they (directly) depend on.  For instance, a graph
like</p>

@({
      A ----->  B ---> C
                |      |
                |      |
                v      |
                D  <---+
})

<p>Could be represented as:</p>

@({
      ((A . (B))        ; A only depends on B
       (B . (C D))      ; B depends on C and D
       (C . (D))        ; C only depends on D
       (D . NIL))       ; D depends on nothing
})

<p>Our algorithms treat @('graph') as an alist, i.e., any \"shadowed\"
entries are ignored.</p>

<p>There are no restrictions on the kinds of nodes that a graph can contain.
However, our algorithms are generally based on @(see acl2::fast-alists), so for
good performance:</p>

<ul>

<li>It is helpful for the nodes to be @(see acl2::normed) objects.  (This isn't
strictly necessary; the nodes will be normed as needed.)</li>

<li>It is helpful for @('graph') to be a fast alist.  (This isn't strictly
necessary; the graph will be made fast if needed.)</li>

</ul>")

