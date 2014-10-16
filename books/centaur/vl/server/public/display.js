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
    toolbar_init();

    $.ajax({
	url: "/get-summary",
	cache: true,
	data: {base:BASE, model:MODEL, origname:ORIGNAME},
	dataType: "json",
	type: "get",
	success: function(data,textStatus,jqXHR)
	{
	    var error = data[":ERROR"];
	    var summary = data[":VALUE"];

	    if (error != "NIL") {
		$("#sourcecode").html(data[":ERROR"]);
		return;
	    }
	    if (summary == "NIL") {
		$("#sourcecode").html(ORIGNAME + " not found.");
		return;
	    }

	    SUMMARY = summary;
	    ORIGNAME = SUMMARY[":NAME"];

	    loadEverythingElse();
	},
	error: function() {
	    $("#sourcecode").html("Error running /get-summary");
	}
    });
}

function loadEverythingElse()
{
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

    console.log("Type is " + type);

    if (type == ":VL-MODULE")
    {
	var btn = "";
	btn += "<a href='javascript:void(0)' onclick='makePortTable();'>";
	btn += "<img class='toolbutton' src='images/io.png' data-powertip='<p>Printable block diagram.</p>'/>";
	btn += "</a> ";
	$("#disptools").append(btn);
    }

    if (type == ":VL-MODULE" ||
	type == ":VL-PACKAGE" ||
	type == ":VL-CONFIG" ||
	type == ":VL-INTERFACE" ||
	type == ":VL-TYPEDEF" ||
	type == ":VL-PROGRAM")
    {
	// Should be able to do a raw source display.
	var btn = "";
	btn += "<a href='javascript:void(0)' onclick='toggleMarkup();'>";
	btn += "<img class='toolbutton' src='images/markup.png' data-powertip='<p>Switch to parsed/raw display.</p>'/>";
	btn += "</a> "
	$("#disptools").append(btn);
    }


    installParsedSource();

    if (type == ":VL-MODULE") {
	installHierarchy();
    }
}


function installHierarchy()
{
    // Only called for modules.

    var hier = "";
    hier += "<span id='hier_parents'></span>";
    hier += "<span id='hier_children'></span>";
    $("#hierarchy").html(hier);

    $.ajax({
	url: "/get-parents",
	cache: true,
	data: {base:BASE, model:MODEL, origname:ORIGNAME},
	dataType: "json",
	type: "get",
	success: function(data,textStatus,jqXHR)
	{
	    var error = data[":ERROR"];
	    var parents = data[":VALUE"];
	    if (error != "NIL") {
		$("#hier_parents").html(data[":ERROR"]);
		return;
	    }

	    if (parents == "NIL" || parents.length == 0) {
		// Seems nicer just not to say anything at all.
		// $("#hier_parents").html("No parents");
		return;
	    }

	    var ret = "Parents ";
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
	},
	error: function() {
	    $("#hier_parents").html("Error running /get-parents");
	}
    });


    $.ajax({
	url: "/get-children",
	cache: true,
	data: {base:BASE, model:MODEL, origname:ORIGNAME},
	dataType: "json",
	type: "get",
	success: function(data,textStatus,jqXHR)
	{
	    var error = data[":ERROR"];
	    var children = data[":VALUE"];
	    if (error != "NIL") {
		$("#hier_children").html(data[":ERROR"]);
		return;
	    }
	    if (children == "NIL" || children.length == 0) {
		// Seems nicer just not to say anything at all.
		// $("#hier_children").html("Leaf module (no children).");
		return;
	    }

	    var ret = "Children ";
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
	},
	error: function() {
	    $("#hier_children").html("Error running /get-children");
	}
    });
}


var SHOWING = "";

function installParsedSource()
{
    $.ajax({
	url: "/get-origsrc",
	cache: true,
	data: {base:BASE, model:MODEL, origname:ORIGNAME},
	dataType: "html",
	type: "get",
	success: function(data,textStatus,jqXHR)
	{
	    $("#sourcecode").html(data);
	    SHOWING = "parsed";
	},
	error: function() {
	    $("#sourcecode").html("Error running /get-origsrc");
	}
    });
}

function installRawSource()
{
    $.ajax({
	url: "/get-plainsrc",
	cache: true,
	data: {base:BASE, model:MODEL, origname:ORIGNAME},
	dataType: "text",
	type: "get",
	success: function(data,textStatus,jqXHR)
	{
	    $("#sourcecode").html("<pre>" + htmlEncode(data) + "</pre>");
	    SHOWING = "raw";
	},
	error: function() {
	    $("#sourcecode").html("Error running /get-origsrc");
	}
    });
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

