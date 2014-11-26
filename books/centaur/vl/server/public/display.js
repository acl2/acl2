// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

var ORIGNAME = getParameterByName("origname"); // Originally case-insensitive.  Gets corrected by onConnected.

if (!ORIGNAME) {
    window.alert("No origname to display?")
}

var SUMMARY = false;
function onConnected()
{
    log("Connected");
    toolbar_init();
    log("Toolbar initialized.");

    vlsGetJson({ url: "/vls-get-summary",
		 data: {origname:ORIGNAME},
		 success: function(summary)
		 {
		     log("Got summaries.");
		     if (summary == "NIL") {
			 $("#sourcecode").html(ORIGNAME + " not found.");
			 return;
		     }
		     SUMMARY = summary;
		     ORIGNAME = SUMMARY[":NAME"];
		     loadEverythingElse();
		 }});
}

function loadEverythingElse()
{
    log("Loading everything else.");
    $("#banner").html(ORIGNAME);

    var desc = "";
    var type = SUMMARY[":TYPE"];
    var file = SUMMARY[":FILE"];
    var line = SUMMARY[":LINE"];
    var col  = SUMMARY[":COL"];
    desc += "<i>" + niceDescriptionType(type) + "</i><br/>";
    desc += "<small>";
    desc += "<a href=\"javascript:void(0)\" onclick=\"showLoc('" + file + "', " + line + ", " + col + ")\">";
    desc += file + ":" + line + ":" + col;
    desc += "</small>";
    $("#desctype").html(desc);

    log("Type is " + type);

    // Add the port table/IOs button only for modules
    if (type == ":VL-MODULE")
    {
	var btn = "";
	btn += "<a href='javascript:void(0)' onclick='makePortTable();'>";
	btn += "<img class='toolbutton' src='images/io.png' data-powertip='<p>Printable block diagram.</p>'/>";
	btn += "</a> ";
	$("#disptools").append(btn);
    }

    // Add raw source display button only if this is a container-type thing with a start/end location.
    if (type == ":VL-MODULE" ||
	type == ":VL-PACKAGE" ||
	type == ":VL-CONFIG" ||
	type == ":VL-INTERFACE" ||
	type == ":VL-TYPEDEF" ||
	type == ":VL-PROGRAM")
    {
	var btn = "";
	btn += "<a href='javascript:void(0)' onclick='toggleMarkup();'>";
	btn += "<img class='toolbutton' src='images/markup.png' data-powertip='<p>Switch to parsed/raw display.</p>'/>";
	btn += "</a> "
	$("#disptools").append(btn);
    }

    installParsedSource();
    installHierarchy();
}


function installHierarchy()
{
    // Only called for modules.

    var hier = "";
    hier += "<span id='hier_parents'></span>";
    hier += "<span id='hier_children'></span>";
    $("#hierarchy").html(hier);

    vlsGetJson({ url: "/vls-get-parents",
		 data: {origname:ORIGNAME},
		 success: function(parents) {
		      if (parents == "NIL" || parents.length == 0) {
    			  // Seems nicer just not to say anything at all.
			  log("Not showing empty parents " + JSON.stringify(parents));
    			  // $("#hier_parents").html("No parents");
    			  return;
    		      }

    		     var ret = "Used by ";
    		     for(var i = 0; i < parents.length; ++i) {
    			 var par = parents[i];
    			 ret += "<a href=\"javascript:void(0)\" onclick=\"showModule('" + par + "')\">" + par + "</a>";
    			 if (i == parents.length - 2) {
    			     ret += " and ";
    			 }
    			 else if (i != parents.length - 1) {
    			     ret += ", ";
    			 }
    		     }
    		     ret += ".<br/>";
    		     $("#hier_parents").append(ret);
		 }});

    vlsGetJson({ url: "/vls-get-children",
		 cache: true,
		 data: {origname:ORIGNAME},
		 success: function(children) {
		     if (children == "NIL" || children.length == 0) {
			 // Seems nicer just not to say anything at all.
			  log("Not showing empty children " + JSON.stringify(children));
			 // $("#hier_children").html("Leaf module (no children).");
			 return;
		     }

		     var ret = "Uses ";
		     for(var i = 0; i < children.length; ++i) {
			 var child = children[i];
			 ret += "<a href=\"javascript:void(0)\" onclick=\"showModule('" + child + "')\">" + child + "</a>";
			 if (i == children.length - 2) {
			     ret += " and ";
			 }
			 else if (i != children.length - 1) {
			     ret += ", ";
			 }
		     }
		     ret += ".";
		     $("#hier_children").append(ret);
		 }});
}


var SHOWING = "";

function installParsedSource()
{
    vlsGetHtml({ url: "/vls-get-origsrc",
		 data: {origname:ORIGNAME},
		 success: function(data) {
		     $("#sourcecode").html(data);
		     SHOWING = "parsed";
		 }});
}

function installRawSource()
{
    vlsGetHtml({ url: "/vls-get-plainsrc",
		 data: {origname:ORIGNAME},
		 success: function(data)
		 {
		     $("#sourcecode").html("<pre>" + htmlEncode(data) + "</pre>");
		     SHOWING = "raw";
		 }});
}

function toggleMarkup()
{
    if (SHOWING != "raw") {
	installRawSource();
    }
    else {
	installParsedSource();
    }
}


function makePortTable()
{
    var url = "porttable.html?"
                  + "&base=" + BASE
                  + "&model=" + MODEL
                  + "&origname=" + ORIGNAME;
			  //var opts = "status=0,toolbar=1,height=600,width=780,resizable=1,scrollbars=1,location=1";
    var wname = "portTableWindow_" + ORIGNAME;
    var win = window.open(url, wname);
    win.focus();
}

function showModule(name)
{
    var page = "display.html?"
                    + "&base=" + BASE
                    + "&model=" + MODEL
                    + "&origname=" + name;
    if (window.opener == null)
	location.href = page;
    else
	window.opener.location.href = page;
}


function showWireExt(mod,wire) {
    var url = "describe.html?"
                  + "&base=" + BASE
                  + "&model=" + MODEL
                  + "&origname=" + mod
 	          + "&what=" + wire;
    var opts = "status=0,toolbar=1,height=600,width=780,resizable=1,scrollbars=1,location=1";
    var wname = "describeWindow_mod" + mod + "&what=" + wire;
    var win = window.open(url, wname, opts);
    win.focus();
    return false;
}

function showWire(wire) {
//    var url = "describe.pl?model=cns&base=2014-09-09-19-12&mod=rregs&trans=&what=" + name;
//    var opts = "status=0,toolbar=1,height=500,width=700,resizable=1,scrollbars=1,location=1";
//    var win = window.open(url, "describeWindow", opts);
//    win.focus();
    showWireExt(ORIGNAME, wire);
}

$(document).ready(function() { connect(onConnected); });

