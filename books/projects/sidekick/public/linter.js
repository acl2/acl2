/*

ACL2 Sidekick
Copyright (C) 2014 Kookamara LLC

Contact:

  Kookamara LLC
  11410 Windermere Meadows
  Austin, TX 78759, USA
  http://www.kookamara.com/

License: (An MIT/X11-style license)

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the "Software"),
  to deal in the Software without restriction, including without limitation
  the rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.

*/

function rule_to_string(x)
{
    console.assert(":RULE" in x, "Rule has no :RULE.");
    console.assert(":ORIGIN" in x, "Rule has no :ORIGIN.");
    console.assert(":BODY" in x, "Rule has no :BODY.");
    var name = x[":RULE"];
    var origin = x[":ORIGIN"];
    var body = x[":BODY"];

    var icon;

    if (origin instanceof Array) {
	origin = origin[origin.length-1];
	icon = "frombook.png";
    }
    else if (origin == ":BUILT-IN") {
	origin = "Built into ACL2";
	icon = "fromacl2.png";
    }
    else {
	origin = "Current session";
	icon = "fromsession.png";
    }

    var ret = "";
    ret += "<p>";
    ret += "<img src='icons/" + icon + "' align='left' style='padding-right: .3em;'/>";
    ret += "<span class='rulename'>" + htmlEncode(name.toLowerCase()) + "</span><br/>";
    ret += "<small><span class='from'>" + htmlEncode(origin) + "</span></small></p>"
    ret += "<pre>" + htmlEncode(body) + "</pre>";
    return ret;
}

function get_lint ()
{
    $.get("/lint", null, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#lint").html("<p>" + htmlEncode(err) + "</p>");
	    return;
	}
	console.log("Hello");
	var redundant = data[":REDUNDANT"];
	if (redundant == "NIL") {
	    $("#lint").html("<p>Nothing to report</p>");
	}
	console.assert(redundant instanceof Array, "thought redundant would be an array");
	var tbl = jQuery("<table class='redundant_table'></table>");
	for(var i = 0; i < redundant.length; ++i) {
	    var item = redundant[i];
	    console.assert(item[":TYPE"] == ":REDUNDANT", "Bad :TYPE for redundant entry.");
	    var entry = "";
	    entry += "<tr><td width='45%'>";
	    entry += rule_to_string(item[":RULE1"]);
	    entry += "</td><td class='vs' width='10%'>vs.</td><td width='45%'>";
	    entry += rule_to_string(item[":RULE2"]);
	    entry += "</td></tr>";
	    tbl.append(entry);
	}
	$("#lint").html("<h5>Redundant or Conflicting Rules</h5>");
	$("#lint").append(tbl);
 
    }).fail(function() {
	$("#lint").html("Error getting lint report.");
    });

}

$(document).ready(get_lint);

