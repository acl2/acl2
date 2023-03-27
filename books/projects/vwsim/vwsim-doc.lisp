; Copyright (C) 2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; NOTE!: This xdoc is currently a work-in-progress. Please refer to
; the file README for instructions on how to use the simulator.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "xdoc/save" :dir :system)
(include-book "xdoc/save-rendered" :dir :system)

(include-book "constants")

(include-book "kestrel/std/util/deftutorial" :dir :system)

; :DOC Examples may be found here:
; books/system/doc/acl2-doc.lisp

(defxdoc vwsim
  :parents (projects hardware-verification)
  :short "A circuit simulator for rapid, single-flux, quantum
  circuits."
  :long
  "

  <h3> Introduction </h3> <p> VWSIM is an interactive circuit
  simulator for rapid, single-flux, quantum (RSFQ) circuits. The
  simulator is designed to model and simulate primitive-circuit
  devices such as capacitors, inductors, Josephson Junctions,
  transformers, and delay lines, and it could be extended to simulate
  other circuit families, such as CMOS.  Circuit models can be
  provided in the native VWSIM netlist format or as SPICE-compatible
  netlists, which are flattened and transformed into symbolic
  equations that can be manipulated and simulated.  Written in the
  ACL2 logic, VWSIM provides logical guarantees about each of the
  circuit models it simulates.  The ACL2-based definition of the VWSIM
  simulator offers a path for specifying and verifying RSFQ circuit
  models. Note, our matrix solving and evaluation routines use Common
  Lisp floating-point numbers, and work is ongoing to extend such
  models into the ACL2 logic.</p>

  <h3> Table of Contents </h3>

  <ul>
  <li> @(see vwsim) </li>
    <ul>
    <li> @(see vwsim-users-guide) </li>
      <ul>
      <li> @(see vwsim-build-and-setup) </li>
      <li> @(see vwsim-input) </li>
        <ul>
        <li>@(see vwsim-spice)</li>
        <li>@(see vwsim-hdl)</li>
          <ul>
          <li>@(see vwsim-constants)</li>
          <li>@(see vwsim-term)</li>
          </ul>
        <li>@(see vwsim-names)</li>
        <li>@(see vwsim-input-source-waveforms)</li>
        </ul>
      <li> @(see vwsim-output) </li>
        <ul>
        <li>@(see vwsim-output-request-format)</li>
        </ul>
      <li> @(see vwsim-commands) </li>
        <ul>
          <li>@(see vwsim-command)</li>
          <li>@(see vw-output-command)</li>
          <li>@(see vw-output-all-command)</li>
          <li>@(see vw-plot-command)</li>
          <li>@(see vw-assoc-command)</li>
        </ul>
      </ul>
    <li> @(see vwsim-tutorial) </li>
      <ul>
      <li> @(see vwsim-tutorial-1) </li>
      <li> @(see vwsim-tutorial-2) </li>
      <li> @(see vwsim-tutorial-3) </li>
      </ul>
    </ul>
  </ul>

    <h3> Motivation </h3>

  <p> The development of our simulator began for several reasons: to
  improve our understanding of the mathematics of JJ-based circuits,
  to better understand what existing simulators were doing, to have a
  simulator that could carry out collections of simulations, to
  provide a way to alter an on-going simulation, to provide an
  interactive means to control our simulation process, to provide a
  programmed method for inspecting results, and to eventually provide
  a formal semantics for JJ-based circuits. </p>

  <p> We have defined the VWSIM circuit simulator with simulation
  models for resistors, capacitors, inductors, transmission lines,
  mutual inductance, Josephson Junctions (JJs), and VWSIM includes
  voltage, current, and phase sources.  VWSIM can simulate an entire
  circuit model either in the voltage or phase domain.  With our use
  of ACL2 to implement the VWSIM electrical-circuit simulator, VWSIM
  enjoys mathematical properties not available in other simulation
  systems: termination, logical consistency, and a formal semantics
  for reasoning about circuit models.  The VWSIM system was authored
  originally by Warren A. Hunt, Jr. and Vivek Ramanathan; J Moore
  provided the VWSIM Gaussian-elimination solver, and Matt Kaufmann
  wrote the SPICE parser and provided tremendous assistance with
  subtle ACL2 issues.</p>

  <p>VWSIM is written using ACL2 formal logic; thus the entire
  simulator implementation can be thought of as a mathematical
  function that animates circuit models.  Given suitable input
  stimulus, VWSIM can produce voltage, current, and phase records.
  Developing tools using ACL2 provides a number of benefits.  Each
  ACL2 function, when defined, must be proven to terminate and proven
  to access reachable data only; thus, all ACL2 programs are known to
  terminate, without memory-reference errors.</p>

   <p> When our effort began, we identified properties we hoped our
   RSFQ circuit modeling and analysis would provide.  We realized that
   available simulators for RSFQ circuits were void of some properties
   we desired.  These shortcoming did not impede our use of
   public-available simulators, but no simulator combined all of the
   properties we felt were important for investigating RSFQ circuit
   models thoroughly and accurately.  Note, the JoSIM simulator
   provides us with inspiration, and we strive to make our system as
   good as JoSIM in areas where JoSIM shines while providing
   capabilities not available in any available circuit simulator.  We
   note that our simulator is not as fast as JoSIM.  Some of our goals
   for VWSIM include:</p>

   <ol>
   <li><b>ACCURATE</b>: We wrote VWSIM with clarity and simplicity in mind.</li>
   <li><b>RELIABLE</b>: VWSIM is proven to terminate without memory-access errors.</li>
   <li><b>FLEXIBLE</b>: VWSIM offers a general-purpose stimulus language.</li>
   <li><b>INTEGRAL</b>: VWSIM supports voltage and phase-based simulation.</li>
   <li><b>TIMING</b>: Fixed and variable time-step simulations are available.</li>
   <li><b>ACCESSIBLE</b>: All code is freely available; runs on multiple systems.</li>
   <li><b>INTEROPERABLE</b>: Use of VWSIM can be scripted with ACL2 or other tools.</li>
   <li><b>CAN BE PAUSED</b>: Any simulation may be paused, saved, and later re-started.</li>
   <li><b>EXTENSIBLE</b>: VWSIM can be extended with additional components and stimulus.</li>
   <li><b>ANNOTATION</b>: VWSIM models can be annotated with physical parameters.</li>
   <li><b>PROMPT</b>: VWSIM can be used interactively; signal traces are memory resident.</li>
   <li><b>FORMAL</b>: The VWSIM is written in a mathematical modeling language.</li>
   <li><b>INTROSPECTIVE</b>: VWSIM source code has been analyzed with the ACL2 system.</li>
   <li><b>ANALYSIS</b>: VWSIM code and circuit models can be analyzed symbolically by ACL2.</li>
   </ol>

   <h3> How VWSIM Works </h3>

   VWSIM accepts a hierarchical circuit description as a list of
   circuit modules, which it then flattens into a list of primitive
   devices with no module (subcircuit) references. The flattened
   netlist is checked for consistency, making sure that there are no
   undefined references or unrecognized components. With a valid, flat
   netlist, VWSIM attempts to build a matrix equation that represents
   a symbolic set of relations; these relations include
   components (e.g., a specific resistor) and sources (e.g., some
   time-varying current source), where their specific values are to be
   instantiated during simulation. If the resulting matrix, <i>A</i>,
   is well-formed (i.e., not singular) and the sources, in <i>b</i>,
   are suitable, then VWSIM prepares to solve for <i>x</i> in matrix
   equation <i>Ax</i> = <i>b</i> by instantiating the symbolic
   expressions in <i>A</i> and <i>b</i> with the current simulation
   values. The solution vector, <i>x</i>, represents the next-time
   values for the simulation variables for a time-step value specified
   by the user -- this process is repeated until simulation time is
   exhausted. VWSIM records the voltages and/or phases of all
   wires (nodes) as well as the currents through all components except
   resistors and JJs. The currents through resistors and JJs can be
   calculated after the simulation, if requested. A VWSIM user can
   then process the simulation history, either by inspection, by
   analysis with an ACL2 program, or by visualizing some projection of
   the recorded information. See @(see vwsim-commands) for a list of
   commands that can be used to interact with the simulation.

   Given a textual description of a circuit, VWSIM will process and
   simulate it following these steps:
   <ol>
   <li>Convert input file, if in SPICE-format, into S-expressions.</li>
   <li>Transform S-expressions into list of circuit module references
   and simulation control statements.</li>
   <li>Convert module references into a hierarchical netlist representation.</li>
   <li>Flatten and sort hierarchical netlist into a list of primitive
   device references.</li>
   <li>Create a symbolic version of the model; i.e., create the
   symbolic <i>Ax</i> = <i>b</i> matrix using the modified nodal
   approach (MNA) procedure.</li>
   <li>Given a time step size (or using an automatically selected time
   step size), solve for x in Ax = b. Use these new x values to extend
   the simulation, and repeat this process until the end of simulation
   time.</li>
   <li>Finally, process and/or save the time-value results produced by
   the simulation; for instance, print results into a file of
   circuit-node values or check the simulation results for specific
   relationships.</li>
   </ol>

   <img src=\"res/vwsim-images/VWSIM-Flowchart-Small.png\"/>
")

(defxdoc vwsim-users-guide
; Below, in "tsee", "t" is for typewriter font.
; Below, in "csee", "c" is for capital.
  :parents (vwsim)
  :short "The VWSIM User's Guide."
  :long "

<h3>Overview</h3>

 <p>VWSIM is an interactive circuit simulator.  After starting a VWSIM
 session, the user interacts with the simulator by issuing commands at
 the ACL2 prompt.  Navigate through the subtopics below to learn about
 using the simulator.</p>

")

(xdoc::order-subtopics
 vwsim-users-guide
 (vwsim-build-and-setup
  vwsim-input
  vwsim-output
  vwsim-commands))

(defxdoc vwsim-build-and-setup
  :parents (vwsim-users-guide)
  :short "How to build the VWSIM simulator."
  :long "

  <h3> Building VWSIM </h3>


  <p> Note for new ACL2 users: the VWSIM simulator is written in
  ACL2. If you are unfamiliar with ACL2, please check out @(see ACL2)
  for more information. The instructions to download and build ACL2
  can be found <a
  href=\"https://www.cs.utexas.edu/users/moore/acl2/current/HTML/installation/installation.html\">here</a>. Once
  ACL2 has been installed on your system, please follow the steps
  below.</p>


  <p>To build the simulator, navigate to the VWSIM directory in the
  ACL2 books. Then, certify the book @('top').</p>

  <p>For example, navigate to the VWSIM directory, and run the
  following command:</p>

  <p>@({[ACL2]/books/build/cert.pl top})</p>

  <p>where [ACL2] is the directory where ACL2 is installed.</p>

  <h3> Running VWSIM </h3>

  <p> Start ACL2 and run the following form at the prompt: </p>

  <p> @({(ld \"driver.lsp\")}) </p>

  <p> That's it! VWSIM should be loaded and ready to simulate
  circuits. Please go to @(see vwsim-users-guide) for information on
  how to use the simulator. </p>

")

#||

 ;; example of how to create a custom link.

 <see topic=\"@(url vwsim-build-and-setup)\">Build and Setup</see>

||#

(defxdoc vwsim-input
  :parents (vwsim-users-guide)
  :short "VWSIM input formats."
  :long "
 <h3>Input</h3>

 <p>VWSIM accepts circuit descriptions in the following formats:</p>

 <ol>
 <h4>SPICE file</h4>

 <p>The circuit netlist can be described in the SPICE format. The
textual description of the circuit is provided in a &quot;.cir&quot;
file.  See @(see vwsim-spice) for the SPICE commands supported in
VWSIM.</p>

 <h4>VWSIM netlist</h4>

 <p> A circuit description can be provided in VWSIM's native netlist
 format.  The circuit netlist is described in a LISP syntax.  See @(see
 vwsim-hdl) for a description of the VWSIM hardware description
 language.</p>

 <h4>LISP file</h4>

 <p> A saved VWSIM circuit simulation can be provided in the form of a
 LISP file.  This is a file that was generated by a previous VWSIM
 simulation, which used the @('save-sim') simulator option.</p>

 </ol>

")

(defxdoc vwsim-output
  :parents (vwsim-users-guide)
  :short "VWSIM output formats."
  :long "
 <h3>Output</h3>

 <p>VWSIM saves all values produced during a simulation; these values
 may be used for subsequent processing such a analysis and/or
 printing.  The saved results can be processed in the following
 ways (see below).  An advanced user of VWSIM can access the entire
 trace of simulation values and write programs to explore the data and
 even control the simulation as it advances; this advanced mechanism
 is not documented presently (within this collection of notes), but
 can be explored by consulting the VWSIM source code.</p>

 <p>A VWSIM user interacts with VWSIM through a (Lisp-style)
 command-line, read-eval-print loop.  Commands can be given to
 request the various output.</p>

 <ol>

 <h4>Comma-Separated Values (CSV) file</h4>

 <p>The user-requested values are written to a file in CSV format.</p>

 <h4>Association-list</h4>

 <p>The user-requested values are returned in a LISP-style
 association (key-value pair) list. The values can be accessed
 interactively by name using @(see assoc-equal).</p>

 <h4>Saved (LISP) file</h4>

 <p>An entire simulation state is saved to a file, which can be
 provided to VWSIM at a later time so as to resume the saved
 simulation. </p>

 <h4>Graphical Plots</h4>

 <p>The user-requested values can be plotted directly from the ACL2
 loop using gnuplot.</p>

 </ol>

")

(defxdoc vwsim-commands
  :parents (vwsim-users-guide)
  :short "VWSIM commands."
  :long "

  <p>VWSIM provides a set of interactive commands that can be issued at
  the ACL2 prompt to analyze and visualize circuit simulations.</p>

")

(defxdoc vwsim-command
  :parents (vwsim-commands)
  :short "Perform simulation of a circuit."
  :long
  "
  <h3>The VWSIM command</h3>

@({
 General Form:
 (vwsim input [keyword options])
})

 <h4>Description</h4>

 <p>@('vwsim') is the top-level simulation command.</p>

 <h4> Usage and Arguments </h4>

@({
Options                Defaults
 :sim-type               'voltage
 :equations               nil
 :spice-print             nil
 :global-nodes            nil
 :time-step               nil
 :time-stop               nil
 :time-start              0
 :output-file             nil
 :save-var                nil
 :save-sim                nil
 :save-sim-shortp         nil
 :concat-char             #\\|
 :return-records          nil
 :load-sim                nil
 })

 <p>where all arguments, which are described below, are evaluated.</p>

<h5> Required arguments </h5>

<p>
@('input') - one of the following options:
<ol>
  <li>a string containing the path to a \".cir\" file.</li>
  <li> a LISP-style VWSIM netlist.</li>
  <li>a string containing the path to a \".lisp\" file.</li>
</ol>
</p>

<h5> Optional arguments </h5>

<p>
@(':sim-type') - the simulation mode; select 'voltage or 'phase.
</p>

<p>
@(':equations') - when non-NIL, return the symbolic simulation
equations. Otherwise, perform the numerical simulation.
</p>

<p>
@(':spice-print') - when non-NIL, the output file should contain only
the values requested in the SPICE file.
</p>

<p>
@(':global-nodes') - a list of globally-defined nodes (wires) in the
circuit.
</p>

<p>
@(':time-step') - when non-NIL, the simulation time step in seconds as
a rational number. Otherwise, the time step is expected to be provided
by @('input').
</p>

<p>
@(':time-stop') - when non-NIL, the simulation stop time in seconds as
a rational number. Otherwise, the stop time is expected to be provided
by @('input').
</p>

<p>
@(':time-start') - when non-NIL, the simulation start time in seconds
as a rational number. Otherwise, the start time is expected to be
provided by @('input').
</p>

<p>
@(':output-file') - when non-NIL, the csv file to write the requested
SPICE simulation values.
</p>

<p>
@(':save-var') - when non-NIL, the simulation result is saved as an
alist in the global variable symbol specified by save-var.
</p>

<p>
@(':save-sim') - when non-NIL, the filename to save the simulation state
for resuming the simulation later.
</p>

<p>
@(':save-sim-shortp') - when non-NIL and @(':save-sim') is non-NIL,
the simulation results will be writen to the file as
single-precision (32-bit) instead of double-precision (64-bits)
floats.
</p>

<p>
@(':concat-char') - SPICE heirarchical circuit concatentation
character for PRINT statements. This is typically the character |.
</p>

<p>
@(':return-records') - when t, the simulation results are returned in an
alist, where the keys are all of the simulation variables. If
@(see symbol-listp), only the variables in the list will be keys in the
alist.
</p>

<p> @(':load-sim') - when non-NIL, @('input') is expected to be a file
that stores a previous VWSIM simulation and does not have extension
\".lisp\". The previous simulation will be loaded and resumed.
</p>

 <h4> Example Forms </h4>
 @({
 (vwsim
 ;; Input SPICE (.cir) file
  \"Testing/test-circuits/cirs/rc-circuit.cir\")

 (vwsim
 ;; Input SPICE (.cir) file
  \"Testing/test-circuits/cirs/rc-circuit.cir\"
  :spice-print t
  :output-file \"Testing/test-circuits/csvs/rc-circuit-output.csv\")
 })

 <p>
 To see an example of running the simulator on a circuit, see @(see
 vwsim-tutorial).
 </p>
")

(xdoc::order-subtopics
 vwsim-commands
 (vwsim-command
  vw-output-command
  vw-output-all-command
  vw-plot-command
  vw-assoc-command))

(defxdoc vw-output-command
  :parents (vwsim-commands)
  :short "Access and save simulation results."
  :long
  "
  <h3>The VW-OUTPUT command</h3>

@({
 General Form:
  (vw-output requests [keyword options])
})

  <h4>Description</h4>

  <p>After performing a simulation using @('vwsim'), @('vw-output')
  provides the means to access simulation results. The results can be
  saved to an assocation-list in the interactive session or written to
  a CSV file. For more information on the output format, see the
  'Output Format' section below.</p>

  <h4> Usage and Arguments </h4>

@({
Options                Defaults
 :output-file             nil
 :save-var                nil
 })

 <p>where all arguments, which are described below, are evaluated.</p>

  <h5>Required arguments</h5>

  <p>
  @('requests') - an association-list of request types and node/device
  names. See @(see vwsim-output-request-format) for the format of this
  alist.
  </p>

  <h5>Optional arguments</h5>

  <p>
  @(':output-file') - when non-NIL, the csv file to write the
  requested simulation values.
  </p>

  <p>
  @(':save-var') - when non-NIL, the requested simulation values are
  saved as an alist in the global variable specified by save-var.
  </p>

  <h5>Output format</h5>

  <p>When @(':output-file') is NIL, @('vw-output') produces an @(see
  alistp). The keys in this association-list (alist) are the requested
  variables in the input argument @('requests'), converted into
  strings. See @(see vwsim-output-request-format) for the syntax of
  the @('requests') input argument.</p>

  <p>The translation of each request, which is of the form @('(type
  . name)'), into a string is as follows:</p>

  <p>@('(NODEV . name)') =&gt; \"V(@('name'))\"</p>

  <p>@('(NODEP . name)') =&gt; \"P(@('name'))\"</p>

  <p>@('(DEVV . name)')  =&gt; \"V(@('name'))\"</p>

  <p>@('(DEVI . name)')  =&gt; \"I(@('name'))\"</p>

  <p>@('(DEVP . name)')  =&gt; \"P(@('name'))\"</p>

  <p>In the output alist, each request will have a corresponding list
  containing the request's values for each simulation time step.</p>

  <p>When :output-file is non-NIL, the alist described above is
  written to a file in the comma-separated-values (CSV) format.
  </p>

")

(defxdoc vw-output-all-command
  :parents (vwsim-commands)
  :short "Access and save all simulation results."
  :long
  "
  <h3>The VW-OUTPUT-ALL command</h3>

@({
 General Form:
  (vw-output-all [keyword options])
})

  <h4>Description</h4>

  <p>@('vw-output-all') calculates the voltage and phase for every
  node, and the the voltage, current, and phase for every device in
  the circuit. The results can be saved to an assocation-list in the
  interactive session or written to a CSV file.</p>

  <h4> Usage and Arguments </h4>

@({
Options                Defaults
 :output-file             nil
 :save-var                nil
 })

  <h5>Optional arguments</h5>

  <p>
  @(':output-file') - when non-NIL, the csv file to write the
  requested simulation values.
  </p>

  <p>
  @(':save-var') - when non-NIL, the simulation values are saved as an
  alist in the global variable specified by save-var.
  </p>

")

(defxdoc vw-plot-command
  :parents (vwsim-commands)
  :short "Plot simulation results."
  :long
  "
  <h3>The VW-PLOT command</h3>

@({
 General Form:
  (vw-plot requests csv-file)
})

  <h4>Description</h4>

  <p>@('vw-plot') plots the requested simulation values using
  gnuplot. The simulation values to be plotted are provided in a CSV
  file. It is expected that the first column in the CSV file contains
  the simulation times. </p>

  <p>Note: In order to use the vw-plot command, it is expected that <a
  href='http://www.gnuplot.info'>gnuplot</a> is already installed on
  your system.</p>

  <h4> Usage and Arguments </h4>

  <h5>Required arguments</h5>

  <p>
    @('requests') - an association-list of request types and
  node/device names. See @(see vwsim-output-request-format) for the
  format of this alist.
  </p>

  <p>
    @('csv-file') - a string containing the path to a CSV file with
    the simulation results to plot.
  </p>
")

(defxdoc vw-assoc-command
  :parents (vwsim-commands)
  :short "Lookup variable in simulation results."
  :long
  "
  <h3>The VW-ASSOC command</h3>

@({
 General Form:
  (vw-assoc request alist)
})

  <h4>Description</h4>

  <p>@('vw-assoc') returns the requested variable's simulation values
  that are saved in an alist produced by the @(see
  vw-output-command).</p>

  <h4> Usage and Arguments </h4>

  <h5>Required arguments</h5>

  <p> @('request') - the symbol $time$ (to request simulation time for
    each time step) or a pair of the form (type . name). See @(see
    vwsim-output-request-format) for the format of this pair. </p>

  <p> @('alist') - an alist that was produced by a call to the @(see
    vw-output-command). It is expected that $time$ and @('request')
    are keys in the alist.</p>

")

(deftutorial vwsim-tutorial "VWSIM tutorial")

(def-vwsim-tutorial-top
  (vwsim-users-guide)
  "<p>Welcome to VWSIM tutorial! We will go through simulating various
  circuits to get familiar with the simulator and its many options.</p>

  <p>VWSIM provides simulation capabilities for hierarchical circuit
  models.  These models specify VWSIM primitives (resistors,
  capacitors, inductors, Josephson junctions, transmission lines,
  transformers, and current, voltage, and phase sources) and how they
  are connected.</p>

  <p>VWSIM accepts input models for simulation in two, text-based
  formats: the SPICE format and the VWSIM native format.  VWSIM does
  not provide CAD or schematic capture capabilities; we do not discuss
  options for using a CAD system to provide a means to create SPICE or
  VWSIM compatible input (models).  However, we note that our typical
  process involves creating a schematic using the GNU Electric CAD
  tool, and then asking that tool to produce a SPICE-compatible
  netlist that VWSIM can process.  Even though VWSIM can read SPICE
  formatted input, VWSIM supports a small number of input components
  compared to a typical SPICE-compatible simulator (see @(see
  vwsim-spice)).  VWSIM has been designed with a focus on RSFQ circuit
  models.</p>

  <p>To prepare input for VWSIM, one may use an editor (or some other
  process) to produce a netlist that can be read by VWSIM in @(see
  vwsim-spice) or @(see vwsim-hdl) format.  Such a hierarchical
  netlist identifies all primitive devices and also describes the
  connection between all primitive devices.  To cause VWSIM to animate
  such a netlist, a user also must provide time-varying voltage,
  current, and phase sources so that the model to be simulated will
  attempt to respond to these sources.  All primitives (components and
  sources) are combined and simplified into a single, flat netlist
  composed of only primitives connected (by references) to other
  primitives.  After a simulation, we observe time-varying changes to
  the model in terms of voltages, currents, and phases -- generally,
  by graphing them using a plotting program, such as GNUPlot.  In some
  cases, we write ACL2 code to perform post-processing of the
  simulation values that were saved during a simulation.</p>

  <p>Given an acceptable model, meaning that each primitive component
  is connected to other primitive components, VWSIM attempts to build
  an internal model @(see vwsim) to be simulated.  If a model can be
  constructed, then VWSIM will attempt to simulate the accepted model
  -- saving intermediate voltage, current, and phase values for
  subsequent processing.</p>

  <p>In our VWSIM use tutorials, we provide several example (circuit)
  models, and we indicate what commands a user evaluates in the ACL2
  Read-Eval-Print Loop (REPL) to cause VWSIM to do its work.</p>
  "
)

(def-vwsim-tutorial-page 1
  ;; workflow example -- simulate, output/access results, save
  ;; results, plot.
  "Simulating a simple circuit"
  ;; provide the .cir file here!!!
  ;; RC circuit
  "
  <p>
  In this tutorial, we demonstrate how to use VWSIM to simulate
  and analyze a simple RC (resistor-capacitor) circuit.
  </p>

  <h4>Preparing VWSIM</h4>

  <p> Prior to analyzing models with VWSIM, see @(see
  vwsim-build-and-setup) for build instructions.  To simulate a
  circuit, start ACL2 and then load the simulator:

  @({(ld \"driver.lsp\")})
  </p>

  <h4>Read and Simulate the Circuit Description</h4>

  <p>We will simulate a simple RC circuit with the following SPICE
  description.  This circuit is composed of three primitives: a
  voltage source (VVS1) that is initially zero (volts), and it rises
  linearly to one volt in one second, a one Ohm resistor (RR1), and a
  one Farad capacitor (CC1).</p>

@({
* RC Circuit

VVS1 vs1 gnd pwl (0 0 1 1V)
RR1  vs1 vc1 1
CC1  vc1 gnd 1

.tran .1 1 0
})

  <p>A copy of this description can be found in
  \"Testing/test-circuits/cirs/rc-circuit.cir\".</p>

  <p>
  VWSIM can simulate the RC circuit using the following command:

  @({(vwsim \"Testing/test-circuits/cirs/rc-circuit.cir\")})

  The command above reads the specified VWSIM circuit model, and
  attempts to parse, flatten, initialize, and simulate the RC model.
  If there is any processing error, VWSIM will stop the process at
  that point.
  </p>

  <h4>Inspect Simulation Results</h4>

  <p>

  As the RC circuit model is simulated, VWSIM stores the simulation
  values for each time step.  Upon completion, we can request specific
  simulation results.  Using the @(see vw-output-command), we can
  fetch the voltage values across the resistor and capacitor, for all
  time steps, and place them in the global variable @('rc-voltages').

  @({(vw-output '((DEVV . RR1) (DEVV . CC1)) :save-var 'rc-voltages)})

  The output result is an @(see alistp).  We can access the
  voltage-time values (across RR1) in the ACL2 loop by executing the
  @(see vw-assoc-command):

  @({(vw-assoc '(DEVV . RR1) (@ rc-voltages))})

  </p>

  <h4>Save and Plot Simulation Results</h4>

  <p> Using the @(see vw-output-command), we can write the voltages
  across resistor RR1 and capacitor CC1 to a comma-separated
  values (CSV) file.  A time-value graph of signal values can be
  plotted; e.g., using gnuplot.

  @({
(vw-output '((DEVV . RR1) (DEVV . CC1))
           :output-file \"Testing/test-circuits/csvs/rc-voltages.csv\")})

  VWSIM provides the @(see vw-plot-command) to run gnuplot from the
  ACL2 prompt.  Here, we plot the voltage across RR1 and CC1 with
  respect to time.

  @({
(vw-plot '((DEVV . RR1) (DEVV . CC1))
         \"Testing/test-circuits/csvs/rc-voltages.csv\")})

  </p>

  <h4>Analyze Simulation Results</h4>

  <p> At this point, it is up to the user to view the plotted results
  to determine whether the desired results were achieved.  In another
  tutorial example, we demonstrate how to write an ACL2 program to
  analyze a simulation result.</p>

")

(def-vwsim-tutorial-page 2
  ;; workflow example with a JTL -- simulate, output/access results,
  ;; save results, plot.
  "Simulating a Josephson Transmission Line"
  ;; provide the .cir file here!!!
  ;; RC circuit
  "<p> In this tutorial, we demonstrate how to use VWSIM to simulate a
  Rapid Single Flux Quantum (RSFQ) circuit. We will model, simulate,
  and analyze a \"Josephson Transmission Line\" (JTL). A JTL accepts a
  RSFQ fluxon (bit) as input and transmits the fluxon from the input
  to the output. Let's simulate our first RSFQ circuit! </p>

  <h4>Preparing VWSIM</h4>

  <p> Prior to analyzing models with VWSIM, see @(see
  vwsim-build-and-setup) for build instructions.  To simulate a
  circuit, start ACL2 and then load the simulator:

  @({(ld \"driver.lsp\")})
  </p>

  <h4>Read and Simulate the Circuit Description</h4>

  <p>We will simulate a simple JTL circuit with the SPICE description
  shown below. This circuit is composed of three subcircuit
  definitions and a top-level circuit. The first subcircuit,
  @('damp_jj'), describes a Josephson junction (JJ) in parallel with a
  \"damping\" resistor (or external shunt). The second subcircuit,
  @('bias'), describes a bias current source, which is defined to be a
  voltage source in series with a resistor. The final subcircuit,
  @('jtl4'), is the definition of our JTL, which uses the subcircuits
  we defined. @('jtl4') is a four-stage JTL since the fluxon passes
  through four JJs before reaching the output. The top-level circuit
  provides fluxons every 20 picoseconds to the JTL, which then
  provides the output to a resistor.</p>

  <h5>Schematic of the four-stage JTL subcircuit</h5>

  <img src=\"res/vwsim-images/jtl4.png\"/>

  <h5>Schematic of the top-level circuit</h5>

  <img src=\"res/vwsim-images/jtl4-top-level.png\"/>

  <h5>SPICE description</h5>

@({

* A hand-written, SPICE description of a four-stage JTL.

*** The model line provides some of the Josephson junction (JJ)
*** parameters.
.model jmitll jj(rtype=1, vg=2.8mV, cap=0.07pF, r0=160, rN=16, icrit=0.1mA)

*** Overdamped JJ subcircuit

.subckt damp_jj pos neg
BJi pos neg jmitll area=2.5
RRi pos neg 3
.ENDS damp_jj

*** Bias current source subcircuit

.SUBCKT bias out gnd
RR1 NN out 17
VrampSppl@0 NN gnd pwl (0 0 1p 0.0026V)
.ENDS bias

*** Four-stage JTL subcircuit

.SUBCKT jtl4 in out gnd
LL1 in net@1 2pH
XJ1 net@1 gnd damp_jj
Xbias1 net@1 gnd bias

LL2 net@1 net@2 2pH

XJ2 net@2 gnd damp_jj
Xbias2 net@2 gnd bias
LL3 net@2 net@3 2pH

XJ3 net@3 gnd damp_jj
Xbias3 net@3 gnd bias
LL4 net@3 net@4 2pH

XJ4 net@4 gnd damp_jj
Xbias4 net@4 gnd bias
LL5 net@4 out 2pH

.ENDS jtl4

*** TOP LEVEL CIRCUIT

* Pulses at 5p, 25p, ...
VD D gnd pulse (0 0.6893mV 5p  1p 1p 2p 20p)
Xjtl4d D out gnd jtl4

RR1 out gnd 5

.END

})

  <p>A copy of this description can be found in
  \"Testing/test-circuits/cirs/four-stage-jtl.cir\".</p>

  <p>Note that the SPICE description file does not contain a
  @('.tran') command! That is, it does not provide a simulation start
  time, simulation step size, and stop time. In fact, VWSIM does not
  require this information to be provided in the SPICE file. The start
  time, stop time, simulation step size, and several other options can
  be provided directly as input arguments to the simulator.</p>

  <p>We will simulate the JTL circuit from 0 seconds to 100
  picoseconds with a step size of 1/10 of a picosecond.</p>

  <p>
  VWSIM can simulate the JTL circuit using the following command:

  @({(vwsim \"Testing/test-circuits/cirs/four-stage-jtl.cir\"
            :time-step (* 1/10 *pico*)
            :time-stop (* 100 *pico*))})

  The arguments to the command above are as follows. The first
  argument to VWSIM is the file that contains the SPICE description of
  the JTL circuit. The second argument is the time step size,
  @(':time-step'). For the time step size, we provide a LISP
  expression that will evaluate to a number. In this case, (* 1/10
  *pico*) evaluates to 1/10 of a picosecond. Check out @(see
  vwsim-constants) for a list of in-built constants that VWSIM
  provides. Note that instead of (* 1/10 *pico*), we could have
  provided the number 1/10000000000000. The final argument is the time
  to stop the simulation, @(':time-stop'), which is 100 picoseconds.

  The command above will then read the specified VWSIM circuit model,
  and attempt to parse, flatten, initialize, and simulate the JTL
  model.  If there is any processing error, VWSIM will stop the
  process at that point.  </p>

  <h4>Inspect Simulation Results</h4>

  <p>

  As the JTL circuit model is simulated, VWSIM stores the simulation
  values for each time step.  Upon completion, we can request specific
  simulation results.  In this case, we would like to inspect whether
  our JTL is working as intended. We can look at the phase across each
  JJ in the JTL and determine whether they fired (i.e. the phase
  across the JJ steps up or down by 2*pi).

  Using the @(see vw-output-command), we can inspect the phase
  across each JJ in the JTL. We will store these phases in the global
  variable @('jj-phases').

@({
(vw-output '((PHASE . BJi/XJ1/XJTL4D)
             (PHASE . BJi/XJ2/XJTL4D)
             (PHASE . BJi/XJ3/XJTL4D)
             (PHASE . BJi/XJ4/XJTL4D))
              :save-var 'jj-phases)
})

  The output result is an @(see alistp).  We can inspect the
  phase-time values across each JJ in the ACL2 loop by executing the
  following command:

  @({(@ jj-phases)})

  Depending on the length of the simulation, this can be a lot to
  print out! We can instead visualize the simulation results using a
  graphing utility.

  </p>

  <h4>Save and Plot Simulation Results</h4>

  <p> Using the @(see vw-output-command), we can write the phases
  across each JJ to a comma-separated values (CSV) file.  A time-value
  graph of signal values can be plotted; e.g., using GNUplot.

@({
(vw-output '((PHASE . BJi/XJ1/XJTL4D)
             (PHASE . BJi/XJ2/XJTL4D)
             (PHASE . BJi/XJ3/XJTL4D)
             (PHASE . BJi/XJ4/XJTL4D))
           :output-file \"Testing/test-circuits/csvs/four-stage-jtl.csv\")
})

  VWSIM provides the @(see vw-plot-command) to run gnuplot from the
  ACL2 prompt.  Here, we plot the phase across each JJ with respect to
  time.

@({
(vw-plot '((PHASE . BJi/XJ1/XJTL4D)
           (PHASE . BJi/XJ2/XJTL4D)
           (PHASE . BJi/XJ3/XJTL4D)
           (PHASE . BJi/XJ4/XJTL4D))
         \"Testing/test-circuits/csvs/four-stage-jtl.csv\")
})

  </p>

  <h4>Analyze Simulation Results</h4>

  <p> At this point, it is up to the user to view the plotted results
  to determine whether the desired results were achieved.  In the next
  tutorial example, we will demonstrate how to write an ACL2 program
  to analyze a simulation result.</p>

")

(def-vwsim-tutorial-page 3
  ;; workflow example with a D-latch -- simulate, output/access results,
  ;; save results, perform computation on results.
  "Simulating an RSFQ D-latch"
  "<p> In this tutorial, we will model, simulate, and analyze a Rapid
  Single Flux Quantum (RSFQ) \"D-latch\" circuit. A D-latch offers a
  mechanism to store a single fluxon (bit) in the RSFQ logic. The
  D-latch we define will have two input wires (@('D'), @('C')) and one
  output wire (@('Out')). The @('D') input requests the latch to store
  a fluxon. The @('C') input requests the latch to release the stored
  fluxon through @('Out'). If there is no fluxon stored in the latch,
  then a fluxon is not released through @('Out').</p>

  <h4>Preparing VWSIM</h4>

  <p> Prior to analyzing models with VWSIM, see @(see
  vwsim-build-and-setup) for build instructions.  To simulate a
  circuit, start ACL2 and then load the simulator:

  @({(ld \"driver.lsp\")})
  </p>

  <h4>Read and Simulate the Circuit Description</h4>

  <p>We will simulate a D-latch circuit with the SPICE description
  shown below. This circuit is composed of 4 subcircuit definitions
  and a top-level circuit. The first subcircuit, @('damp_jj'),
  describes a Josephson junction (JJ) in parallel with a \"damping\"
  resistor (or external shunt). The second subcircuit, @('bias'),
  describes a bias current source, which is defined to be a voltage
  source in series with a resistor. The third subcircuit, @('jtl4'),
  is a four-stage JTL transmission line. These three subcircuits are
  the same circuits defined in the previous tutorial @(see
  vwsim-tutorial-2). The final subcircuit, @('D_latch'), defines the D
  latch we will simulate. A diagram of the D latch is shown below. The
  top-level circuit provides fluxons through pulse generators. The
  generators are connected to Josephson Transmission Lines (JTLs),
  which then connect to either the @('D') or @('C') input of the D
  latch. The D latch @('Out') output wire is also connected to a JTL,
  which provides the output fluxons to a resistor. </p>

  <h5>Schematic of the D-latch subcircuit</h5>

  <img src=\"res/vwsim-images/d-latch.png\"/>

  <h5>Schematic of the top-level circuit</h5>

  <img src=\"res/vwsim-images/d-latch-top-level.png\"/>

  <h5>SPICE description</h5>

@({
* A hand-written, SPICE description of an RSFQ D-latch.

*** The model line provides some of the Josephson junction (JJ)
*** parameters.
.model jmitll jj(rtype=1, vg=2.8mV, cap=0.07pF, r0=160, rN=16, icrit=0.1mA)

*** Overdamped JJ subcircuit

.SUBCKT damp_jj pos neg
BJi pos neg jmitll area=2.5
RRi pos neg 3
.ENDS damp_jj

*** Bias current source subcircuit

.SUBCKT bias out gnd
RR1 NN out 17
VrampSppl@0 NN gnd pwl (0 0 1p 0.0026V)
.ENDS bias

*** 4-stage JTL subcircuit

.SUBCKT jtl4 in out gnd
LL1 in net@1 2pH
XJ1 net@1 gnd damp_jj
Xbias1 net@1 gnd bias

LL2 net@1 net@2 2pH

XJ2 net@2 gnd damp_jj
Xbias2 net@2 gnd bias
LL3 net@2 net@3 2pH

XJ3 net@3 gnd damp_jj
Xbias3 net@3 gnd bias
LL4 net@3 net@4 2pH

XJ4 net@4 gnd damp_jj
Xbias4 net@4 gnd bias
LL5 net@4 out 2pH

.ENDS jtl4

*** D Latch circuit

.SUBCKT D_latch D C out gnd
XJ3 D net@1 damp_jj
XJ1 net@1 gnd damp_jj
Xbias1 net@1 gnd bias

LL net@1 net@2 12pH

XJ4 C net@2 damp_jj
XJ2 net@2 gnd damp_jj
LY net@2 out 2pH
.ENDS D_latch

*** TOP LEVEL CIRCUIT

* Fluxon pulses at 20p, 70p, ...
VD D gnd pulse (0 0.6893mV 20p 1p 1p 2p 50p)
Xjtl4d D rD gnd jtl4

* Fluxon pulses at 5p, 55p, ...
VC C gnd pulse (0 0.6893mV 5p 1p 1p 2p 50p)
Xjtl4c C rC gnd jtl4

* Create instance of D latch subcircuit
XD_latch rD rC out gnd D_latch

* Output JTL
Xjtl_latch out out2 gnd jtl4
RR1 out2 gnd 5

.END
})

  <p>A copy of this description can be found in
  \"Testing/test-circuits/cirs/d-latch.cir\".</p>

  <p>Note that the SPICE description file does not contain a
  @('.tran') command! That is, it does not provide a simulation start
  time, simulation step size, and stop time. In fact, VWSIM does not
  require this information to be provided in the SPICE file. The start
  time, stop time, simulation step size, and several other options can
  be provided directly as input arguments to the simulator.</p>

  <p>We will simulate the D-latch circuit from 0 seconds to 100
  picoseconds with a step size of 1/10 of a picosecond.</p>

  <p>
  VWSIM can simulate the JTL circuit using the following command:

  @({(vwsim \"Testing/test-circuits/cirs/d-latch.cir\"
            :time-step (* 1/10 *pico*)
            :time-stop (* 100 *pico*))})

  The arguments to the command above are as follows. The first
  argument to VWSIM is the file that contains the SPICE description of
  the D-latch circuit. The second argument is the time step size,
  @(':time-step'). For the time step size, we provide a LISP
  expression that will evaluate to a number. In this case, (* 1/10
  *pico*) evaluates to 1/10 of a picosecond. Check out @(see
  vwsim-constants) for a list of in-built constants that VWSIM
  provides. Note that instead of (* 1/10 *pico*), we could have
  provided the number 1/10000000000000. The final argument is the time
  to stop the simulation, @(':time-stop'), which is 100 picoseconds.

  The command above will then read the specified VWSIM circuit model,
  and attempt to parse, flatten, initialize, and simulate the JTL
  model.  If there is any processing error, VWSIM will stop the
  process at that point.  </p>

  <h4>Inspect Simulation Results</h4>

  <p>

  As the D-latch circuit model is simulated, VWSIM stores the
  simulation values for each time step.  Upon completion, we can
  request specific simulation results.  We would like to inspect
  whether our D-latch is working as intended. We can look at the
  current through the quantizing inductor (LL) in the D-latch. When
  there is a fluxon (bit) in the D-latch, there will be a larger
  current circulating in the J1-LL-J2 loop than when there is no
  fluxon stored in the latch.

  Using the @(see vw-output-command), we can inspect the current
  through inductor LL in the D-latch. We will store these currents in
  the global variable @('ll-currents').

@({
(vw-output '((DEVI . LL/XD_LATCH))
           :save-var 'll-currents)
})

  The output result is an @(see alistp).  We can inspect the
  current-time values through LL in the ACL2 loop by executing the
  following command:

  @({(@ ll-currents)})

  Depending on the length of the simulation, this can be a lot to
  print out! We can instead visualize the simulation results using a
  graphing utility.

  </p>

  <h4>Save and Plot Simulation Results</h4>

  <p> Using the @(see vw-output-command), we can write the current
  through LL to a comma-separated values (CSV) file.  A time-value
  graph of signal values can be plotted; e.g., using GNUplot.

@({
(vw-output '((DEVI . LL/XD_LATCH))
           :output-file \"Testing/test-circuits/csvs/d-latch.csv\")
})

  VWSIM provides the @(see vw-plot-command) to run gnuplot from the
  ACL2 prompt.  Here, we plot the phase across each JJ with respect to
  time.

@({
(vw-plot '((DEVI . LL/XD_LATCH))
         \"Testing/test-circuits/csvs/d-latch.csv\")
})

  </p>

  <h4>Analyze Simulation Results</h4>

  <p> Since all of the simulation results are already available in the
  loop, we can perform analysis on the circuit. We will identify when
  a fluxon passes through the Josephson junction J1, which suggests
  that a fluxon is stored in the D-latch.</p>

  <p> We need to inspect the phase across J1 at all simulation times
  and determine when a fluxon passes through the JJ. This will be when
  the phase across the JJ has stepped up or down by a multiple of
  2*pi (i.e. when the phase across the JJ has completed a full
  \"turn\" around the unit circle). To perform this analysis, consider
  the following function definitions.</p>

@({
(defun detect-fluxon-through-jj-recur (jj-phases times turns)
  ;; check if list of phases is empty
  (if (atom jj-phases)
      nil
    (let* (;; get next phase across the JJ
           (phase (car jj-phases))
           (2pi (* 2 (f*pi*)))
           (new-turns (truncate phase 2pi)))
      (if ;; detect a step up/down in 2pi phase across the JJ
          (not (= new-turns turns))
          ;; full fluxon detected
          (cons (car times)
                (detect-fluxon-through-jj-recur
                 (cdr jj-phases) (cdr times) new-turns))
        ;; full fluxon through the jj yet
        (detect-fluxon-through-jj-recur
         (cdr jj-phases) (cdr times) turns)))))

(defun detect-fluxon-through-jj (jj-phases times)
  ;; check if list of phases is empty
  (if (atom jj-phases)
      nil
    (let* ((2pi (* 2 (f*pi*)))
           ;; calculate how many times the JJ has already been turned
           ;; by 2pi radians
           (initial-phase (car jj-phases))
           (initial-turn (truncate initial-phase 2pi)))
      ;; find all times a fluxon passed through the JJ (i.e. the JJ
      ;; turned)
      (detect-fluxon-through-jj-recur
       (cdr jj-phases) (cdr times) initial-turn))))
})

  <p> The @('detect-fluxon-through-jj') function takes two input
  arguments: a list of the phases across the JJ for each simulation
  time step and a list of the simulation times for each simulation
  time step. Then it determines how many times the phase across the JJ
  has already been turned at the beginning of the simulation. Then, it
  calls the function @('detect-fluxon-through-jj-recur') which recurs
  through the rest of the phases and records each time the phase
  across the JJ completes a full turn.
 </p>

  <p> Before we can run these functions, we need to define these
  function definitions in ACL2. Copy and paste the two function
  definitions above into your ACL2 session. </p>

  <p> We need to provide the phase across J1 for each time step and
  the list of simulation times for each time step to our
  @('detect-fluxon-through-jj') function. We will access the phase
  values from the output alist produced by the @(see
  vw-output-command) using the @(see vw-assoc-command). @('vw-assoc')
  takes as input a key-value pair (in this case, we are requesting the
  phase across J1) and an alist produced by @('vw-output'). It then
  returns the requested key along with its simulation values, if the
  key exists in the alist, otherwise it returns NIL. We can take the
  @('cdr') of the list produced by @('vw-assoc') to remove the key
  from the front of the list.</p>

  <p>We can now execute the following two commands:</p>

@({

(vw-output '((PHASE . BJi/XJ1/XD_LATCH))
           :save-var 'loop-phases)

(detect-fluxon-through-jj
 (cdr (vw-assoc '(PHASE . BJi/XJ1/XD_LATCH) (@ loop-phases)))
 (cdr (vw-assoc '$time$ (@ loop-phases))))

})

<p>which results in</p>

@({

(3.11e-11 8.11e-11)

})

<p>This means that, during the simulation, a fluxon passed through J1
at 31 picoseconds and 81 picoseconds. We can check whether this is
what we expected. The pulse generators produce a pulse on the @('D')
input at 20 picoseconds and 70 picoseconds, and on the @('C') input at
5 picoseconds and 55 picoseconds. This sequence requests the latch to
be emptied at 5 picoseconds, filled at 20 picoseconds, emptied at 55
picoseconds, and filled at 70 picoseconds. Our analysis is consistent
with this description. A fluxon passed through J1 every time the latch
was filled (20ps and 70ps). Note: the ~11 picosecond delay from
request to the fluxon passing through J1 is primarily due to the time
it takes for the fluxons to pass through the four-stage JTLs before
reaching the latch.</p>

<p>This concludes the tutorial. You can navigate to the @(see
vwsim-users-guide) to learn more about the different simulator
options.</p>

<p>We hope you enjoy VWSIM. Happy simulating!</p>

")

#||

(def-vwsim-tutorial-page 4
  "Resuming an existing simulation"
  ;; JTL
  "")

||#

;; generates the xdoc topics defined used "def-vwsim-tutorial-page"
(def-vwsim-tutorial-topics)

(defxdoc vwsim-hdl
  :parents (vwsim-input)
  :short "The VWSIM Hardware Description Language (HDL)."
  :long
  "<h3>Introduction</h3>

   <p>VWSIM accepts heirarchical netlist descriptions in its native
   LISP-style format.  Here, we describe the expected syntax of a
   netlist described using the VWSIM HDL.  At a high-level, a netlist
   is a list of modules where each module consists of a name,
   input/output nodes, and a list of occurrences.  An occurrence is
   either a primitive device (resistor, inductor, etc.)  or an
   instantiation of a defined module.  Below, the primitives are
   described first, followed by occurrences, modules, and
   netlists.</p>

   <p>Unlike SPICE, VWSIM HDL separates the circuit netlist
   description from it associated simulation commands (e.g.,
   simulation times, print requests).  Such simulation-control
   commands are provided as arguments when invoking the simulator.</p>

   <p>VWSIM offers a collection of primitive circuit models, which are
   combined into a single model for eventual circuit simulation.
   Below we describe the circuit primitives to which all models must
   eventually be expanded; these basic circuit models have
   mathematical descriptions based in circuit theory and physics.  In
   a companion document, we provide a description of each circuit
   element and its associated mathematical model (as used by the VWSIM
   system).</p>

   <p>Note: see @(see vwsim-names) for the expected format of device
   and node names when defining netlists.</p>

   <h3> Primitive device </h3>

   <p>A primitive, in the VWSIM Lisp format, is one of the following.
   Other input formats will be converted into this format. </p>
   <ol>

   <h4>Voltage Source</h4>
   <code>(name v (pos neg) (branch) (term))</code>
   <p>where</p>
      <ul>
        <li><i>pos</i> is the node connected to the positive terminal.</li>
        <li><i>neg</i> is the node connected to the negative terminal.</li>
        <li><i>branch</i> is the name for the current through the
        device.</li>
        <li><i>term</i> is a @(see vwsim-term).</li>
      </ul>
   <h4>Current Source</h4>
   <code>(name i (pos neg) (branch) (term))</code>
   <p>where</p>
      <ul>
        <li><i>pos</i> is the node connected to the positive terminal.</li>
        <li><i>neg</i> is the node connected to the negative terminal.</li>
        <li><i>branch</i> is the name for the current through the
        device.</li>
        <li><i>term</i> is a @(see vwsim-term).</li>
      </ul>
   <h4>Phase Source</h4>
   <code>(name p (pos neg) (branch) (term))</code>
   <p>where</p>
      <ul>
        <li><i>pos</i> is the node connected to the positive terminal.</li>
        <li><i>neg</i> is the node connected to the negative terminal.</li>
        <li><i>branch</i> is the name for the current through the
        device.</li>
        <li><i>term</i> is a @(see vwsim-term).</li>
      </ul>
   <h4>Resistor</h4>
   <code>(name r (pos neg) (branch) (resistance))</code>
   <p>where</p>
      <ul>
        <li><i>pos</i> is the node connected to the positive terminal.</li>
        <li><i>neg</i> is the node connected to the negative terminal.</li>
        <li><i>branch</i> is the name for the current through the
        device.</li>
        <li><i>resistance</i> (in Ohms) is a quoted positive rational.</li>
      </ul>
   <h4>Inductor</h4>
   <code>(name l (pos neg) (branch) (inductance))</code>
   <p>where</p>
      <ul>
        <li><i>pos</i> is the node connected to the positive terminal.</li>
        <li><i>neg</i> is the node connected to the negative terminal.</li>
        <li><i>branch</i> is the name for the current through the
        device.</li>
        <li><i>inductance</i> (in Henries) is a quoted positive
        rational.</li>
      </ul>
   <h4>Capacitor</h4>
   <code>(name c (pos neg) (branch) (capacitance))</code>
   <p>where</p>
      <ul>
        <li><i>pos</i> is the node connected to the positive terminal.</li>
        <li><i>neg</i> is the node connected to the negative terminal.</li>
        <li><i>branch</i> is the name for the current through the
        device.</li>
        <li><i>capacitance</i> (in Farads) is a quoted positive
        rational.</li>
      </ul>
   <h4>Josephson Junction</h4>
   <code>(name b (pos neg) (branch) (icrit area vg rn r0 cap))</code>
   <p>where</p>
      <ul>
        <li><i>pos</i> is the node connected to the positive terminal.</li>
        <li><i>neg</i> is the node connected to the negative terminal.</li>
        <li><i>branch</i> is the name for the voltage or phase through
        the device depending on the simulation type.</li>
        <li><i>icrit</i> is the JJ critical current; it is a quoted
        positive rational.</li>
        <li><i>area</i> is the JJ area; it is a quoted
        positive rational.</li>
        <li><i>vg</i> is the JJ gap voltage; it is a quoted
        positive rational.</li>
        <li><i>rn</i> is the JJ normal resistance; it is a quoted
        positive rational.</li>
        <li><i>r0</i> is the JJ subgap resistance; it is a quoted
        positive rational.</li>
        <li><i>cap</i> is the JJ capacitance; it is a quoted
        positive rational.</li>
      </ul>
   <h4>Mutual Inductance</h4>
   <code>(name k (inductor0-name inductor1-name) (coupling-factor))</code>
   <p>where</p>
      <ul>
        <li><i>inductor0-name</i> is the name of the first coupled
        inductor. The coupled inductors are expected to be in the same
        module.</li>
        <li><i>inductor1-name</i> is the name of the second coupled
        inductor.</li>
        <li><i>coupling-factor</i> is a @(see vwsim-term); it is a quoted
        rational between -1 and 1, inclusive.</li>
      </ul>
   <h4>Transmission Line</h4>
   <code>(name t (pos0 neg0  pos1 neg1) (br0 br1) (delay impedance))</code>
   <p>where</p>
      <ul>
        <li><i>pos0</i> is the node connected to the positive terminal
        at the first port.</li>
        <li><i>neg0</i> is the node connected to the negative terminal
        at the first port.</li>
        <li><i>pos1</i> is the node connected to the positive terminal
        at the second port.</li>
        <li><i>neg1</i> is the node connected to the negative terminal
        at the second port.</li>
        <li><i>br0</i> is the name for the current through the first
        port.</li>
        <li><i>br0</i> is the name for the current through the second
        port.</li>
        <li><i>delay</i> is the time delay (in seconds) of the
        transmission line; it is a quoted rational.</li>
        <li><i>impedance</i> is the transmission line impedance (in
        Ohms); it is a quoted rational.</li>
      </ul>

   </ol>

   <h3>Occurrence</h3>

   <p>An occurrence is one of the following:</p>

   <ol>
     <li>A primitive device</li>
     <li>A module reference of the form:
       <code>(name module-name module-IOs)</code></li>
       <p> where </p>
      <ul>
        <li><i>module-name</i> is the name of the module being
         referenced.</li>
        <li><i>module-IOs</i> is a list of nodes that will be passed
        to and substituted into the module reference.</li>
      </ul>
   </ol>

   <h3>Module</h3>

   <p>A module defines an unordered collection of references to
   primitives and inferior modules.  A module is of the following
   form:</p>

   <code>(name module-IOs occurrences)</code>
     <p> where </p>
      <ul>

        <li><i>module-IOs</i> is a list of external node (wire
        connections) placeholders that will be available to the module
        occurrences.  Connections to internal node names will be
        provided when a module is referenced by a superior
        occurrence (reference).</li>

        <li><i>occurrences</i> is a list of occurrences.</li>
      </ul>

   <h3>Netlist</h3>

  <p>A netlist is an ordered list of modules. The netlist is defined such that</p>

   <ol>
     <li>The first module is the top-level circuit.</li>
     <li>Each module is defined only once.</li>
     <li>Each (interior) module occurrence that references another module may
     reference a module defined later in the netlist.</li>
   </ol>

   <p>When VWSIM processes an input model, it attempts to assure that all
   module references are valid.</p>

   <p>See @(see vwsim) for a flowchart of how this input model is
   processed for simulation.</p>

  ")

(defxdoc vwsim-term
  :parents (vwsim-hdl)
  :short "The VWSIM Mathematical Term Language."
  :long
  "<h3>Introduction</h3>

  <p>VWSIM provides a language to express mathematical
  terms (expressions). Here, the subset of this language available to
  the user is presented. These expressions can be used when the user
  is describing netlists using the @(see vwsim-hdl). At simulation
  time, these terms are evaluated to double-precision floating point
  numbers.</p>

  <p>A term is one of the following:</p>

  <ul>

  <li>Quoted constant</li>

  <li>Symbol constant</li>

  <li>Symbol variable</li>

  <li>Function Call</li>

  </ul>

  <h4>Quoted Constant</h4>

  <p>A quoted constant is a QUOTE followed by a rational or
  double-precision floating point number.</p>

  <p>Examples:</p>

  <ul>
    <li>@(''1')</li>
    <li>@(''3/7')</li>
    <li>@(''3.4d0')</li>
    <li>@(''7.9d2')</li>
  </ul>

  <h4>Symbol Constant</h4>

  <p>A symbol constant is a @(see symbolp) that has @('*') as the
  first and last character. The available constants are:</p>

  <p>
  <table>
    <tr>
      <th>Constant name</th>
      <th>Description</th>
    </tr>
    <tr>
      <th>@('*pi*')</th>
      <th>Pi</th>
    </tr>
    <tr>
      <th>@('*e*')</th>
      <th>Euler's number</th>
    </tr>
    <tr>
      <th>@('*h*')</th>
      <th>Planck's constant (Joules * seconds)</th>
    </tr>
    <tr>
      <th>@('*h_bar*')</th>
      <th>Planck's Constant divided by two pi</th>
    </tr>
    <tr>
      <th>@('*e_C*')</th>
      <th>Charge of an electron (Coulombs)</th>
    </tr>
    <tr>
      <th>@('*K_b*')</th>
      <th>Boltzmann's constant (Joules/Kelvin)</th>
    </tr>
    <tr>
      <th>@('*deltaV*')</th>
      <th>Size of the Josephson junction (JJ) transition region (Volts)</th>
    </tr>
    <tr>
      <th>@('*phi0*')</th>
      <th>Magnetic Flux Quantum (Webers)</th>
    </tr>
    <tr>
      <th>@('*Icfact*')</th>
      <th>Ratio of JJ critical current to quasiparticle step height</th>
    </tr>
  </table>
  </p>

  <p>The constants also include the multipliers @('*kilo*'),
  @('*mega*'), @('*giga*'), @('*tera*'), @('*peta*'), @('*milli*'),
  @('*micro*'), @('*nano*'), @('*pico*'), and @('*femto*'). See @(see
  vwsim-constants) for the values of all of the constants.</p>

  <h4>Symbol Variable</h4>

  <p>A symbol variable is a @(see symbolp) that denotes a variable
  value that will be looked up at simulation time. The user is allowed
  to use the @('$time$') and @('$hn$') symbol variables.</p>

  <p>@('$time$') is the current simulation time as a floating point
  number.</p>

  <p>@('$hn$') is the current simulation step size as a floating point
  number.</p>

  <p>Note: it is recommended to use the @('$time$<') function whenever
  possible. See the description below.</p>

  <h4>Function Call</h4>

  <p>A function call is of the form:</p>

  <p><tt>(fun-name arg0 arg1 ...)</tt></p>

  <p>where each available fun-name and its arity is described below,
  and each argument is a term.</p>

  <p>A note on the use of booleans: the vwsim-term language provides a
  few functions that deal with booleans (@('$time$<'), @('f-not'),
  @('f<'), @('f='), @('if')). Since the evaluation of terms only
  produces a floating point number, these functions understand the
  number 0.0d0 to be FALSE and any other value to be TRUE.</p>

  <h5>Unary Functions</h5>

  <p>
  <table>

    <tr>
      <th>Function</th>
      <th>Description</th>
    </tr>
    <tr>
      <th>@('$time$<')</th>
      <th>Check whether the current simulation time is less than the
      provided argument. Returns a boolean (see discussion above about
      booleans). </th>
    </tr>
    <tr>
      <th>@('f-not')</th>
      <th>Logical not</th>
    </tr>
    <tr>
      <th>@('f0-')</th>
      <th>Negation</th>
    </tr>
    <tr>
      <th>@('f-abs')</th>
      <th>Absolute value</th>
    </tr>
    <tr>
      <th>@('f-1/x')</th>
      <th>Reciprocal</th>
    </tr>
    <tr>
      <th>@('f-sqrt')</th>
      <th>Square root</th>
    </tr>
    <tr>
      <th>@('f-sin')</th>
      <th>Sine</th>
    </tr>
    <tr>
      <th>@('f-cos')</th>
      <th>Cosine</th>
    </tr>
    <tr>
      <th>@('f-tan')</th>
      <th>Tangent</th>
    </tr>
    <tr>
      <th>@('f-tanh')</th>
      <th>Hyperbolic tangent</th>
    </tr>
    <tr>
      <th>@('f-exp')</th>
      <th>Expontential function (e^x)</th>
    </tr>
  </table>
  </p>

  <h5>Binary Functions</h5>

  <p>
  <table>
    <tr>
      <th>Function</th>
      <th>Description</th>
    </tr>
    <tr>
      <th>@('f+')</th>
      <th>Addition</th>
    </tr>
    <tr>
      <th>@('f-')</th>
      <th>Subtraction</th>
    </tr>
    <tr>
      <th>@('f*')</th>
      <th>Multiplication</th>
    </tr>
    <tr>
      <th>@('f/')</th>
      <th>Division</th>
    </tr>
    <tr>
      <th>@('f<')</th>
      <th>Less than</th>
    </tr>
    <tr>
      <th>@('f=')</th>
      <th>Equality</th>
    </tr>
    <tr>
      <th>@('f-mod')</th>
      <th>Modulo</th>
    </tr>
  </table>
  </p>

  <h5>Ternary Functions</h5>

  <p>
  <table>
    <tr>
      <th>Function</th>
      <th>Description</th>
    </tr>
    <tr>
      <th>@('if')</th>
      <th>If the first argument evaluates to 0.0d0 (FALSE), then the
      third argument is evaluated. Otherwise, the second argument is
      evaluated.</th>
    </tr>
  </table>
  </p>

  <p>Some more examples of terms:</p>

  <ul>
    <li>@('(f+ '1 '2)')</li>
    <li>@('(f+ '1.2d0 *pi*)')</li>
    <li>@('(f* '2 $hn$)')</li>
    <li>@('(if (f-not (f< '1 *phi0*)) '4 '5)')</li>
    <li>@('(if ($time$< '2/100) '1.0d0 '2.0d0)')</li>
  </ul>

  ")

(defxdoc vwsim-names
  :parents (vwsim-input)
  :short "Format of device and node names."
  :long " <p>All input is processed assuming the input is ASCII text;
  thus, VWSIM input should be provided as ASCII text.  Once read,
  VWSIM converts all names into Lisp symbols, which it uses
  internally.  So, some of the restrictions below concern our use of
  ACL2 (Lisp) as the VWSIM implementation language.</p>

  <p>VWSIM restricts device and node names as follows:</p>

  <ol>
    <li>The string must be non-empty.</li>

    <li>The string must consist only of @(see standard-char-p).</li>

    <li>The string cannot be the reserved Boolean symbols, \"t\" or
    \"nil\". </li>

    <li>The first character of the string must be @(see alpha-char-p),
    a digit from 0-9, or one of the following characters: _ @ + - . In
    SPICE files, the use of + and - in names is disallowed as these
    are interpreted by SPICE as arithmetic operators.  Although
    allowed in VWSIM HDL, we don't recommend starting a name with the
    + or - characters.</li>

    <li>Each node name specified for a device must be distinct.</li>

    <li>The device name must be distinct from its node (wire) names.
    Note: In SPICE, the first character of a device name is the type.
    For example, 'VS1' is the name of a voltage source.</li>
  </ol>
")

(defsection vwsim-spice
  :parents (vwsim-input)
  :short "VWSIM-compatible SPICE commands."
  :long
  "<p>SPICE provides many textual commands to define and simulate a
  circuit.  The small subset of SPICE commands that VWSIM understands
  are presented below.  The commands are case-insensitive (due to our
  use of Lisp, which upcases lower-case characters).</p>

  <p>Note: see @(see vwsim-names) for the expected format of device
  and node names when defining netlists.</p>

  <h3>Devices</h3>

  <ol>
  <h4>Voltage Source</h4>
      <code>V<i>name</i> <i>N+</i> <i>N-</i> <i>Type</i> (<i>Values</i>)</code>
      <p>where</p>
      <ul>
        <li><i>N+</i> is the node connected to the positive terminal.</li>
        <li><i>N-</i> is the node connected to the negative terminal.</li>
        <li><i>Type</i> is PWL, EXP, SIN, or PULSE.</li>
        <li><i>Values</i> is a list of space-separated constants that
        depends on the <i>Type</i>. See @(see
        vwsim-input-source-waveforms) for more information on how to
        specify waveforms.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>VV1 a gnd pwl (0 0 1 2 10 20)</li>
      <li>VV2 a gnd pulse (0 1 2 1 1 3 15)</li>
      </ul>
  <h4>Current Source</h4>
      <code>I<i>name</i> <i>N+</i> <i>N-</i> <i>Type</i> (<i>Values</i>)</code>
      <p>where</p>
      <ul>
        <li><i>N+</i> is the node connected to the positive terminal.</li>
        <li><i>N-</i> is the node connected to the negative terminal.</li>
        <li><i>Type</i> is PWL, EXP, PULSE, or SIN.</li>
        <li><i>Values</i> is a list of space-separated constants that
        depends on the <i>Type</i>. See @(see
        vwsim-input-source-waveforms) for more information on how to
        specify waveforms.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>II1 a gnd pwl (0 0 1 2 10 20)</li>
      <li>II2 a gnd pulse (0 1 2 1 1 3 15)</li>
      </ul>
  <h4>Phase Source</h4>
      <code>P<i>name</i> <i>N+</i> <i>N-</i> <i>Type</i> (<i>Values</i>)</code>
      <p>where</p>
      <ul>
        <li><i>N+</i> is the node connected to the positive terminal.</li>
        <li><i>N-</i> is the node connected to the negative terminal.</li>
        <li><i>Type</i> is PWL, EXP, PULSE, or SIN.</li>
        <li><i>Values</i> is a list of space-separated constants that
        depends on the <i>Type</i>. See @(see
        vwsim-input-source-waveforms) for more information on how to
        specify waveforms.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>PP1 a gnd pwl (0 0 1 2 10 20)</li>
      <li>PP2 a gnd pulse (0 1 2 1 1 3 15)</li>
      </ul>
  <h4>Resistor</h4>
      <code>R<i>name</i> <i>N+</i> <i>N-</i> <i>Value</i></code>
      <p>where</p>
      <ul>
      <li><i>N+</i> is the node connected to the positive terminal.</li>
      <li><i>N-</i> is the node connected to the negative terminal.</li>
      <li><i>Value</i> is the resistance in Ohms. It is a positive constant.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>RR1 a gnd 10</li>
      <li>RR2 a b 2.5</li>
      </ul>
  <h4>Inductor</h4>
      <code>L<i>name</i> <i>N+</i> <i>N-</i> <i>Value</i></code>
      <p>where</p>
      <ul>
      <li><i>N+</i> is the node connected to the positive terminal.</li>
      <li><i>N-</i> is the node connected to the negative terminal.</li>
      <li><i>Value</i> is the inductance in Henries. It is a positive constant.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>LL1 a gnd 10</li>
      <li>LL2 a b 2.5</li>
      </ul>
  <h4>Capacitor</h4>
      <code>C<i>name</i> <i>N+</i> <i>N-</i> <i>Value</i></code>
      <p>where</p>
      <ul>
      <li><i>N+</i> is the node connected to the positive terminal.</li>
      <li><i>N-</i> is the node connected to the negative terminal.</li>
      <li><i>Value</i> is the capacitance in Farads. It is a positive constant.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>CC1 a gnd 10</li>
      <li>CC2 a b 2.5</li>
      </ul>
  <h4>Josephson Junction</h4>
      <code>B<i>name</i> <i>N+</i> <i>N-</i> <i>Model</i> area=<i>Value</i></code>
      <p>where</p>
      <ul>
      <li><i>N+</i> is the node connected to the positive terminal.</li>
      <li><i>N-</i> is the node connected to the negative terminal.</li>
      <li><i>Model</i> is the name of a model defined using the model command.</li>
      <li><i>Value</i> is the JJ area. It is a positive constant.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>BJ1 a gnd jjmodel area=2.5</li>
      </ul>
  <h4>Mutual Inductance</h4>
      <code>Kname Ind1 Ind2 Value</code>
      <p>where</p>
      <ul>
      <li><i>Ind1</i> is the name of the first coupled inductor.</li>
      <li><i>Ind1</i> is the name of the second coupled inductor.</li>
      <li><i>Value</i> is the coupling factor. It is a constant between -1 and 1, inclusive.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>KM1 LL1 LL2 0.5</li>
      </ul>
  <h4>Transmission Line</h4>
      <code>T<i>name</i> <i>N1+</i> <i>N1-</i> <i>N2+</i> <i>N2-</i>
      TD=<i>Value1</i> Z0=<i>Value2</i></code>
      <p>where</p>
      <ul>
      <li><i>N1+</i> is the node connected to the first positive terminal.</li>
      <li><i>N1-</i> is the node connected to the first negative terminal.</li>
      <li><i>N2+</i> is the node connected to the second positive terminal.</li>
      <li><i>N2-</i> is the node connected to the second negative terminal.</li>
      <li><i>Value1</i> is the delay (propagation time). It is a non-negative constant.</li>
      <li><i>Value2</i> is the impedance. It is a non-negative constant.</li>
      </ul>
      <p>Examples:</p>
      <ul>
      <li>T1 A1 gnd B1 gnd TD=200p Z0=1</li>
      </ul>
  </ol>

  <h3>Statements</h3>

  <ol>
  <h4>Transient Analysis</h4>
      <code>.tran <i>tstep</i> <i>tstop</i> [<i>tstart</i>]</code>
      <ul>
      <li><i>tstep</i> is the printing/simulation step size (in seconds).</li>
      <li><i>tstop</i> is the time to stop the simulation (in seconds).</li>
      <li><i>tstart</i> is the time to start the simulation (in
      seconds). If not provided, the simulation starts at 0 seconds.</li>
      </ul>
  <h4>Global Node</h4>
      <code>.global <i>Node</i> </code>
      <ul>
      <li><i>Node</i> is a node (wire) name that is available to all
      subcircuits.</li>
      </ul>
  <h4>Subcircuit Definition</h4>
      <code>.subckt <i>Name</i> <i>Nodes</i></code>
      <p>where</p>
      <ul>
      <li><i>Name</i> is the subcircuit name.</li>
      <li><i>Nodes</i> is a space-separated list of external nodes</li>
      </ul>
      <p>The lines that immediately follow the .subckt line define the
      subcircuit.</p>
      <code>.ends [name]</code>
      <p>where</p>
      <ul>
      <li><i>name</i> is an optional subcircuit name.</li>
      </ul>
      <p>The .ends line indicates the end of the subcircuit
      definition. If a subcircuit name is provided, it will be checked
      that the subcircuit being specified is ended. Note that this
      allows nested subcircuit definitions. That is, it is acceptable
      to use the .subckt line while already defining a subcircuit.</p>
  <h4>Model</h4>
      <code>.model <i>Name</i> <i>Type</i>([<i>Parameters</i>])</code>
      <p>where</p>
      <ul>
      <li><i>Name</i> is the name of the model.</li>
      <li><i>Type</i> is the device type.</li>
      <li><i>Parameters</i> is an optional space-separated list. Each
      parameter is of the form:
      <tt><i>ParameterName</i>=<i>Value</i></tt></li>
      </ul>
      <p>VWSIM currently only supports the <i>Type</i> \"jj\". The
      parameters for the JJ model are: </p>
      <table>
       <tr>
         <th>Parameter Name</th>
         <th>Description</th>
       </tr>
       <tr>
         <th>icrit</th>
         <th>JJ critical current.</th>
       </tr>
       <tr>
         <th>vg</th>
         <th>JJ gap voltage.</th>
       </tr>
       <tr>
         <th>rn</th>
         <th>JJ normal resistance.</th>
       </tr>
       <tr>
         <th>r0</th>
         <th>JJ subgap resistance.</th>
       </tr>
       <tr>
         <th>cap</th>
         <th>JJ capacitance.</th>
       </tr>
      </table>
  <h4>Print</h4>
      <code>.print <i>PrintType</i> <i>Name</i></code>
      <p>See @(see vwsim-output-request-format) for the format of
      <i>PrintType</i> and <i>Name</i></p>
  </ol>

  <h3>Unit Prefixes</h3>
  <p>A SPICE value can be followed by a unit prefix. The prefix is a
  multiplier applied on the value.</p>
  <table>
    <tr>
      <th style=\"border-right: 3px;\">Prefix</th>
      <th>T</th>
      <th>G</th>
      <th>MEG/X</th>
      <th>K</th>
      <th>M</th>
      <th>U</th>
      <th>N</th>
      <th>P</th>
      <th>F</th>
    </tr>
    <tr>
      <th>Value</th>
      <th>10e+12</th>
      <th>10e+9</th>
      <th>10e+6</th>
      <th>10e+3</th>
      <th>10e-3</th>
      <th>10e-6</th>
      <th>10e-9</th>
      <th>10e-12</th>
      <th>10e-15</th>
    </tr>
  </table>
  <p>Examples:</p>
  <ul>
    <li>LL1 a b 2p</li>
    <li>VVS1 c d pwl (0 0 2p 10.2m 5p 7k)</li>
  </ul>


  <h3>Comments</h3>
  <p>The character * at the beginning of a new line denotes a commented line.</p>"
  )

(defxdoc vwsim-input-source-waveforms
  :parents (vwsim-input)
  :short "SPICE-compatible input source waveforms."
  :long "

<p> VWSIM provides various types of waveform generators that are used
during simulation to provide a simulation model with current, voltage,
and phase sources.</p>

<p> VWSIM understands four waveform types: <b>Piecewise Linear</b>,
<b>Exponential</b>, <b>Sinusoidal</b>, and <b>Pulse</b>. For each of
these waveforms, their
parameters and the equations generated from these parameters are
described below. </p>

<h3>Piecewise Linear (PWL)</h3>

<h4>Parameters</h4>

<p>
<table>
  <tr>
  <th>parameter</th>
  <th>description</th>
  <th>units</th>
  </tr>
  <tr>
  <th>t1</th>
  <th>initial time</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>v1</th>
  <th>initial val</th>
  <th>volts, amps, or phase</th>
  </tr>
  <tr>
  <th>...</th>
  <th>...</th>
  <th>...</th>
  </tr>
  <tr>
  <th>tn</th>
  <th>nth time</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>vn</th>
  <th>value at tn</th>
  <th>volts, amps, or phase</th>
  </tr>
</table>
</p>

<h4>Equations</h4>

<p> Using the parameters above, a piecewise linear waveform can be
described as </p>

<p> Each pair of values (ti, vi) specifies that the value of the
source is vi at time = ti. The value of the source at intermediate
values of time is determined by using linear interpolation on the
input values.  For times after the final time value, the value of the
source is the final value.</p>

<h3>Exponential (EXP)</h3>

<h4>Parameters</h4>

<p>
<table>
  <tr>
  <th>parameter</th>
  <th>description</th>
  <th>default</th>
  <th>units</th>
  </tr>
  <tr>
  <th>v1</th>
  <th>initial value</th>
  <th></th>
  <th>volts, amps, or phase</th>
  </tr>
  <tr>
  <th>v2</th>
  <th>pulsed value</th>
  <th></th>
  <th>volts, amps, or phase</th>
  </tr>
  <tr>
  <th>td1</th>
  <th>rise delay time </th>
  <th>0.0</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>tau1</th>
  <th>rise time constant</th>
  <th>tstep</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>td2</th>
  <th>fall delay time</th>
  <th>td1+tstep</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>tau2</th>
  <th>fall time constant</th>
  <th>tstep</th>
  <th>seconds</th>
  </tr>
</table>
</p>

<h4>Equations</h4>

<p>
Using the parameters above, an exponential waveform can be described
as
</p>

<table>
  <tr>
  <th>time</th>
  <th>equation</th>
  </tr>
  <tr>
  <th>0</th>
  <th>v1</th>
  </tr>
  <tr>
  <th>td1</th>
  <th>v1+(v2-v1)(1-e^(-(time-td1)/tau1))</th>
  </tr>
  <tr>
  <th>td2</th>
  <th>v1+(v2-v1)(1-e^(-(time-td1)/tau1))+(v1-v2)(1-e^(-(time-td2)/tau2))
  </th>
  </tr>
</table>

<h3>Sinusoidal (SIN)</h3>

<h4>Parameters</h4>

<p>
<table>
  <tr>
  <th>parameter</th>
  <th>description</th>
  <th>default</th>
  <th>units</th>
  </tr>
  <tr>
  <th>vo</th>
  <th>offset</th>
  <th></th>
  <th>volts, amps, or phase</th>
  </tr>
  <tr>
  <th>va</th>
  <th>amplitude</th>
  <th></th>
  <th>volts, amps, or phase</th>
  </tr>
  <tr>
  <th>freq</th>
  <th>frequency</th>
  <th>1/tstop</th>
  <th>hz</th>
  </tr>
  <tr>
  <th>td</th>
  <th>delay</th>
  <th>0.0</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>theta</th>
  <th>damping factor</th>
  <th>0.0</th>
  <th>hz</th>
  </tr>
  <tr>
  <th>phi</th>
  <th>phase delay</th>
  <th>0.0</th>
  <th>degrees</th>
  </tr>
</table>
</p>

<h4>Equations</h4>

<p>
Using the parameters above, a sinusoidal waveform can be described as
</p>

<table>
 <tr>
 <th>time</th>
 <th>equation</th>
 </tr>
 <tr>
 <th>0 to td</th>
 <th>vo + va * sin((pi * phi/180))</th>
 </tr>
 <tr>
 <th>td to tstop</th>
 <th> vo + va * e^(-(time-td)* theta) * sin(2 pi * (freq * (time-td)) + pi * phi/360)
 </th>
 </tr>
</table>

<h3>Pulse (PULSE)</h3>

<h4>Parameters</h4>

<p>
<table>
  <tr>
  <th>parameter</th>
  <th>description</th>
  <th>default</th>
  <th>units</th>
  </tr>
  <tr>
  <th>v1</th>
  <th>initial value</th>
  <th></th>
  <th>volts, amps, or phase</th>
  </tr>
  <tr>
  <th>v2</th>
  <th>pulsed value</th>
  <th></th>
  <th>volts, amps, or phase</th>
  </tr>
  <tr>
  <th>td</th>
  <th>time delay</th>
  <th>0.0</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>tr</th>
  <th>rise time</th>
  <th>tstep</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>tf</th>
  <th>fall time</th>
  <th>tstep</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>pw</th>
  <th>pulse width</th>
  <th>tstep</th>
  <th>seconds</th>
  </tr>
  <tr>
  <th>per</th>
  <th>period</th>
  <th>tstep</th>
  <th>seconds</th>
  </tr>
</table>
</p>

<h4>Equations</h4>

<p>
Using the parameters above, a pulse waveform for a single pulse with no period can be described as
</p>

<table>
  <tr>
  <th>time</th>
  <th>equation</th>
  </tr>
  <tr>
  <th>0</th>
  <th>v1</th>
  </tr>
  <tr>
  <th>td</th>
  <th>v1</th>
  </tr>
  <tr>
  <th>td+tr</th>
  <th>v2</th>
  </tr>
  <tr>
  <th>td+tr+pw</th>
  <th>v2</th>
  </tr>
  <tr>
  <th>td+tr+pw+tf</th>
  <th>v1</th>
  </tr>
  <tr>
  <th>tstop</th>
  <th>v1</th>
  </tr>
</table>

<p>If a period is specified, a train of pulses is generated. Each pulse
in the train will start at td + (k*per) until tstop is reached.</p>

<p>Note: the minimum value for per is tr+tf+pw.</p>

")

(defsection vwsim-output-request-format
  :parents (vwsim-output)
  :short "How to format output requests from a VWSIM simulation."
  :long
  "
  <h4>Requesting Simulation Values</h4>

 <p> The user can request voltage, phase, and current values from a
 circuit simulation. The request types are:</p>

  <p>@('NODEV') - node (wire) voltage</p>
  <p>@('NODEP') - node (wire) phase</p>
  <p>@('DEVV')  - voltage across device</p>
  <p>@('DEVI')  - current through device</p>
  <p>@('PHASE') - phase difference across device</p>

  <p>The request is a cons pair of the form (type . name). The
  type is paired with the name of a node or device. The name is
  expected to be of the form <q>primitive-name/module-name/...</q> (in
  SPICE, the names are separated by | instead of /), which is the
  flattened hierarchical name of the node or device. That is, the name
  consists of the primitive name, followed by the heirarchy of
  module (subcircuit) names that contain the primitive. For example,
  consider the following RC circuit with a module defined in SPICE
  syntax:

  @({
.SUBCKT SUB_DEF A C
  RR1 A B 1
  CC1 B C 1
.ENDS

VVS1 V1 GND pwl (0 0 1 1)
SUB0 A  GND SUB_DEF
    })

  After the circuit is flattened, the resistor has the name
  @('RR1/SUB0'), the capacitor has name @('CC1/SUB0'), and the voltage
  source has the name @('VVS1') (since it is a top-level device). If
  we wish to inspect the voltage across the resistor and the current
  through the capacitor after a simulation has been completed, we
  could construct the following association-list:

  @({
'((DEVV . RR1/SUB0)
  (DEVI . CC1/SUB0))
})

  In SPICE, we would provide .print commands of the following form:

  @({
.print DEVV RR1|SUB0
.print DEVI CC1|SUB0
})

</p>


  <p> A complete table of acceptable requests is shown below. X
  indicates that the command can be used to get the value of that node
  or device.  </p>

 <table>
   <tr>
     <th></th>
     <th>@('N')</th>
     <th>@('R')</th>
     <th>@('L')</th>
     <th>@('C')</th>
     <th>@('B')</th>
     <th>@('V')</th>
     <th>@('I')</th>
     <th>@('P')</th>
     <th>@('T')</th>
   </tr>
   <tr>
     <th>@('NODEV')</th>
     <th>X</th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
   </tr>
   <tr>
     <th>@('NODEP')</th>
     <th>X</th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
     <th></th>
   </tr>
   <tr>
     <th>@('DEVV')</th>
     <th></th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
   </tr>
   <tr>
     <th>@('DEVI')</th>
     <th></th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
   </tr>
   <tr>
     <th>@('PHASE')</th>
     <th></th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>
     <th>X</th>

   </tr>
 </table>
")

;; Adds a "resource" directory containing images
;;                            rendered dirname   current path
(xdoc::add-resource-directory "vwsim-images"       "images")

; During certification, this next command produces a directory where
; some of the contents include the comments we want included with a
; manual.

(make-event
 (let ((sync-path
        (canonical-pathname "~/Sync/sf/Hunt/" 'save-vwsim state)))
   (if (and sync-path
            (string-prefixp
             sync-path
             (canonical-pathname "." 'save-vwsim state)))
       '(xdoc::save "doc" :error t) ;; Write the manual in HTML
     '(value-triple nil))))

; During certification, this next Lisp form produces the documentation
; that is read and displayed by the ``M-x acl2-doc'' E-lisp command.

(make-event
 (let ((sync-path
        (canonical-pathname "~/Sync/sf/Hunt/" 'save-vwsim state)))
   (if (and sync-path
            (string-prefixp
             sync-path
             (canonical-pathname "." 'save-vwsim state)))
       '(xdoc::save-rendered-event
         ;; outfile: the file where the documentation is written
         "doc/rendered-vwsim-acl2-doc.lsp"
         ;; header: text added to beginning of outfile
         "; Documentation for VWSIM"
         ;; topic-list-name: a symbol that can be the first argument
         ;; of defconst
         '*vwsim-documentation*
         ;; error: causes an error upon encountering a syntax error in
         ;; xdoc source
         t) ;; write the acl2-doc manual
     '(value-triple nil))))

; The above form will generate an entire ACL2 manual (but, we're
; unsure of how much of the ACL2 manual is included) -- including the
; VWSIM documentation.  This generated file can be found in:
; .../doc/rendered-vwsim-acl2-doc.lsp

;; To preview the documentation generated in acl2-doc, execute the
;; following form in emacs or add it to your emacs config file.

#||
(extend-acl2-doc-manual-alist
; The name of the manual. You can select this manual by running the
; command "I" with a prefix argument in acl2-doc. That is, run C-u
; I. Then, type vwsim-preview.
 'vwsim-preview
; documentation source, typically of the form *doc*.lsp
 "~/Sync/sf/Hunt/vwsim-2.9/doc/rendered-vwsim-acl2-doc.lsp"
; the "top" node name. In this case, we want to jump directly to the
; VWSIM topic.
 'VWSIM
 )
||#
