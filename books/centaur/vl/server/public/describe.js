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

function replaceDots(id) {
    document.getElementById(id + "_link").style.display = "none";
    document.getElementById(id).style.display = "block";
}

var firstTimeLoad = 1;

var paneId = 0;

function makePane (what, data)
{
    paneId = paneId + 1;

    var ret = "";
    ret += "<div class='pane' id='pane_" + paneId + "'>";

    ret += "<table class='panetop'>";
    ret += "<tr><td>";
    ret += "<h3 style='margin:0'>";
    ret += "  <a href='javascript:void(0);' onclick='togglePane(" + paneId + ")'>";
    ret +=    htmlEncode(what);
    ret += "  </a>";
    ret += "</h3>";
    ret += "</td><td align='right'>";
    ret += "<a href='javascript:void(0);' onclick='nukePane(" + paneId + ")'>";
    ret += "<img src='images/close.png'></img>";
    ret += "</a>";
    ret += "</td></tr>";
    ret += "</table>";
    ret += "<div class='paneguts' id='paneguts_" + paneId + "'>";
    ret += data;
    ret += "</div>";
    ret += "</div>";
    return ret;
}

function togglePane(id) {
    $("#paneguts_" + id).toggle();
}

function nukePane(id) {
    $("#pane_" + id).hide();
}

function doDescribe(what) {
    vlsGetHtml({ url: "/vls-describe",
		 data: {"origname":ORIGNAME, "what":what},
		 success: function(data)
		 {
		     if (firstTimeLoad) {
			 $("#content").html(makePane(what, data));
			 firstTimeLoad = 0;
		     }
		     else {
			 $("#content").append(makePane(what, data));
			 $('html, body').animate({
			     scrollTop: $("#pane_" + paneId).offset().top
			 }, 100);
		     }
		 }});
}

function onConnected()
{
    // Sanity check to make sure that the model is loaded.
    doDescribe(WHAT);
}

$(document).ready(function() {
   var title = ORIGNAME + "." + WHAT + " &mdash; " + MODEL;
   $("title").html(title);
   $("#wire_id").html(WHAT);
   $("#location_id").html("Searching in <b>" + ORIGNAME + "</b><br/><small>" + MODEL + ")</small>");
   connect(onConnected);
});


function showWire(name)
{
    doDescribe(name);
    // console.log("origname is " + ORIGNAME);
    // var url = "describe.html?model=" + MODEL + "&origname=" + ORIGNAME + "&what=" + name;
    // var opts = "status=0,toolbar=1,height=600,width=780,resizable=1,scrollbars=1,location=1";
    // var wname = "describeWindow_mod=" + ORIGNAME + "&what=" + name;
    // var win = window.open(url, wname, opts);
    // win.focus();
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
