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

$(document).ready(function() { connect(onConnected); });

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
    installWarnings();
}


function makeModuleList(id, names)
{
    log("makeModuleList(" + id + ") with " + names.length + " names");

    var ret = "";
    var max = 8;
    if (names.length <= max)
    {
	// Short enough list that there is no need to elide it.
	for(var i = 0; i < names.length; ++i) {
    	    var name = names[i];
    	    ret += "<a href=\"javascript:void(0)\" onclick=\"showModule('" + name + "')\">" + name + "</a>";
    	    if (i == names.length - 2) {
    		ret += " and ";
    	    }
    	    else if (i != names.length - 1) {
    		ret += ", ";
    	    }
	}
	return ret;
    }

    // Otherwise we have a long list, let's elide it and make it expandable.
    for(var i = 0; i < max; ++i) {
	var name = names[i];
	ret += "<a href=\"javascript:void(0)\" onclick=\"showModule('" + name + "')\">" + name + "</a> ";
	if (i != names.length - 1) {
	    ret += ", ";
	}
    }

    ret += "<span id='elide_" + id + "'>";
    ret += " and ";
    ret += "<a class=\"expandelided\" href=\"javascript:void(0)\" onclick=\"expandElidedModuleList('" + id + "')\">";
    ret += (names.length - max);
    ret += " more";
    ret += "</a>";
    ret += "</span>";

    ret += "<span id='show_" + id + "' style='display:none;'>";
    for(var i = max; i < names.length; ++i) {
    	var name = names[i];
    	ret += "<a href=\"javascript:void(0)\" onclick=\"showModule('" + name + "')\">" + name + "</a>";
    	if (i == names.length - 2) {
    	    ret += " and ";
    	}
    	else if (i != names.length - 1) {
    	    ret += ", ";
    	}
    }
    ret += "</span>";

    return ret;
}

function expandElidedModuleList(id) {
    $("#elide_" + id).hide();
    $("#show_" + id).show();
}

function installHierarchy()
{
    // Build Parents ("Used by") and Children ("Used in") Lists, if applicable.
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
    		     var ret = "<p>Used by ";
		     ret += makeModuleList('parents', parents);
    		     ret += ".</p>";
    		     $("#hier_parents").append(ret);
		 }});

    vlsGetJson({ url: "/vls-get-children",
		 data: {origname:ORIGNAME},
		 success: function(children) {
		     if (children == "NIL" || children.length == 0) {
			 // Seems nicer just not to say anything at all.
			  log("Not showing empty children " + JSON.stringify(children));
			 // $("#hier_children").html("Leaf module (no children).");
			 return;
		     }
		     var ret = "<p>Uses ";
		     ret += makeModuleList('children', children);
		     ret += ".</p>";
		     $("#hier_children").append(ret);
		 }});
}

// function warningTypesSummary(wtypes) {
//     // Wtypes is a hash that binds type -> count
//     var tuples = [];
//     for(var key in wtypes) tuples.push([key, wtypes[key]]);
//     tuples.sort(function(a,b) {
// 	count1 = a[1];
// 	count2 = b[1];
// 	return (count1 < count2) ? -1
//              : (count2 < count1) ? 1
// 	     : 0;
//     });

// }

function warningToItem(w) {
    var ret = "";
    ret += "<li class='vl_warning'>";
    if (w.fatalp)
	ret += "<span class='vl_fatal_warning_type' title=\"From " + htmlEncode(w.fn) + "\">";
    else
	ret += "<span class='vl_nonfatal_warning_type' title=\"From " + htmlEncode(w.fn) + "\">";
    ret += htmlEncode(w.type);
    ret += "</span><br/>";
    ret += w.html;
    ret += "</li>";
    return ret;
}

function expandElidedWarnings() {
    $("#elided_warnings").hide();
    $("#full_warnings").show();
}

function collapseWarnings() {
    $("#elided_warnings").show();
    $("#full_warnings").hide();
}

function closeExtraStuff() {
    $("#extrastuff").hide();
}

function installWarnings()
{
    vlsGetJson({ url: "/vls-get-warnings",
		 data: {origname:ORIGNAME},
		 success: function(warnings)
		 {
		     // Basic sanity check on server data.
		     assert(warnings.constructor === Array, "warnings not an array?");
		     for(var i = 0;i < warnings.length; i++) {
			 var w = warnings[i];
			 assert("tag" in w,    "warning has no tag");
			 assert("type" in w,   "warning has no type");
			 assert("fatalp" in w, "warning has no fatalp");
			 assert("html" in w,   "warning has no html");
			 assert("fn" in w,     "warning has no fn");
		     }

		     if (warnings.length == 0) {
			 // Seems nicer not to say anything at all.
			 log("Not showing empty warnings " + JSON.stringify(warnings));
			 return;
		     }

		     // Partition into fatal versus nonfatal warnings.
		     var fatal = [];
		     var nonfatal = [];
		     for(var i = 0; i < warnings.length; i++) {
			 var w = warnings[i];
			 if (w.fatalp)
			     fatal.push(w);
			 else
			     nonfatal.push(w);
		     }

		     fatal.sort(function(a,b) { return (a.type < b.type) ? 1 : (a.type > b.type) ? -1 : 0; });
		     nonfatal.sort(function(a,b) { return (a.type < b.type) ? 1 : (a.type > b.type) ? -1 : 0; });

		     var acc = "";
		     acc += "<a href=\"javascript:void(0)\" onClick=\"closeExtraStuff()\">";
		     acc += "<img src='images/close_small.png' align='right'/>";
		     acc += "</a>";

		     acc += "<p class='warninghead' align='left'>Warnings &mdash; " + fatal.length + " fatal, " + nonfatal.length + " nonfatal</p>";

		     var all = fatal.concat(nonfatal);
		     var cutoff = 3;

		     if (all.length < cutoff)
		     {
			 acc += "<ul class='vl_warning_list'>";
			 for(var i = 0;i < all.length; ++i)
			     acc += warningToItem(all[i]);
			 acc += "</ul>";
		     }

		     else
		     {
			 acc += "<ul class='vl_warning_list' id='full_warnings' style='display:none'>";
			 for(var i = 0;i < cutoff; ++i)
			     acc += warningToItem(all[i]);

			 acc += "<p class='vl_warning_more'>";
			 acc += "<a class=\"expandelided\" href=\"javascript:void(0)\" onclick=\"collapseWarnings()\">";
			 acc += "show fewer";
			 acc += "</a>";
			 acc += "</p>";

			 for(var i = cutoff;i < all.length; ++i)
			     acc += warningToItem(all[i]);

			 acc += "</ul>";

			 acc += "<ul class='vl_warning_list' id='elided_warnings'>";
			 for(var i = 0;i < cutoff; ++i)
			     acc += warningToItem(all[i]);

			 acc += "<li class='vl_warning_more'>";
			 acc += "<br/><a class=\"expandelided\" href=\"javascript:void(0)\" onclick=\"expandElidedWarnings()\">";
			 acc += "show " + (all.length - cutoff) + " more";
			 acc += "</a>";
			 acc += "</li>";

			 acc += "</ul>";
		     }

		     $("#warnings").html(acc);
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
                    + "&model=" + MODEL
                    + "&origname=" + name;
    if (window.opener == null)
	location.href = page;
    else
	window.opener.location.href = page;
}


function showWireExt(mod,wire) {
    var url = "describe.html?"
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
//    var url = "describe.pl?model=cns&mod=rregs&trans=&what=" + name;
//    var opts = "status=0,toolbar=1,height=500,width=700,resizable=1,scrollbars=1,location=1";
//    var win = window.open(url, "describeWindow", opts);
//    win.focus();
    showWireExt(ORIGNAME, wire);
}



