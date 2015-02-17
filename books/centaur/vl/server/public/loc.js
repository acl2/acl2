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

var ORIGNAME = getParameterByName("origname");
var WHAT = getParameterByName("what");
var FILE = getParameterByName("file");
var LINE = getParameterByName("line");
var COL = getParameterByName("col");


function onConnected()
{
    $.ajax({
	url: "/vls-showloc",
	cache: false,
	data: {"model":MODEL, "file":FILE, "line":LINE, "col":COL},
	dataType: "text",
	type: "get",
	success: function(data,textStatus,jqXHR)
	{
	    console.log("HTML is " + data);
	    $("#content").html(data);
	},
	error: function()
	{
	    $("#content").html("<p>Error with /vls-showloc request.</p>");
	}
    });
}

$(document).ready(function() {
   var title = FILE + ":" + LINE + ":" + COL + " &mdash; " + MODEL;
   $("title").html(title);

   var n = FILE.lastIndexOf("/");
   var shortfile = FILE.substring(n+1);

   $("#file_id").html(shortfile + ", line " + LINE);
   $("#location_id").html("<small>" + MODEL + "</small>");
   connect(onConnected);
});

function showloc_hac() {
    document.getElementById('showloc_hac_link').style.display = "none";
    document.getElementById('showloc_hac').style.display = "block";
}

function showloc_hbc() {
    document.getElementById('showloc_hbc_link').style.display = "none";
    document.getElementById('showloc_hbc').style.display = "block";
    location.href = "#hac_goal";
}
