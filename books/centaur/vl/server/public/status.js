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

function bucketize_descalist (data)
{
    var buckets = {};
    for(var name in data)
    {
	var type = data[name];
	if (!buckets[type]) { buckets[type] = []; }
	buckets[type].push(name);
    }
    return buckets;
}

function render_bucket (typename, bucket)
{
    var ret = jQuery("<div>");
    ret.append("<h4>" + typename + "</h4>");

    if (!bucket) {
	ret.append("<p>None</p>")
	return ret;
    }

    bucket.sort(alphanum);

    var ul = jQuery("<ul></ul>");
    for(var i = 0;i < bucket.length; ++i) {
	var name = bucket[i];
	var ent = "";
	ent += "<li>";
	ent += "<a href='display.html?model=" + MODEL + "&origname=" + name + "'>";
	ent += name;
	ent += "</a>";
	ent += "</li>";
	ul.append(ent);
    }

    ret.append(ul);
    return ret;
}

function status_init()
{
    $.ajax({
	url: "/vls-get-desctypes",
	cache: true,
	data: {"model":MODEL},
	dataType: "json",
	type: "get",
	success: function(data,textStatus,jqXHR)
	{
	    var err = data[":ERROR"];
	    if (err) {
		$("#status").html("Error: " + err);
	    }

	    var buckets = bucketize_descalist(data[":VALUE"]);

	    // Idea:
	    //   column 1: interfaces, packages, fundecls, typedefs (there aren't many of these)
	    //   column 2: modules (there are lots of these)
	    //   column 3: paramdecls (there are lots of these)
	    //   column 4: anything else (if anything else exists)

	    var tbl = jQuery("<table class='statustable'></table>");
	    var row = jQuery("<tr></tr>");
	    var col;

	    // (Sol): Seems best to have most important items in first
	    // columns since if the page gets wide it might not all
	    // fit on one screen.
  	    col = jQuery("<td></td>");
	    col.append(render_bucket("Modules", buckets[":VL-MODULE"]));
	    row.append(col);

  	    col = jQuery("<td></td>");
	    col.append(render_bucket("Packages", buckets[":VL-PACKAGE"]));
	    row.append(col);

	    col = jQuery("<td></td>");
	    col.append(render_bucket("Functions", buckets[":VL-FUNDECL"]));
	    row.append(col);

  	    col = jQuery("<td></td>");
	    col.append(render_bucket("Typedefs", buckets[":VL-TYPEDEF"]));
	    row.append(col);

	    col = jQuery("<td></td>");
	    col.append(render_bucket("Parameters", buckets[":VL-PARAMDECL"]));
	    row.append(col);

  	    col = jQuery("<td></td>");
	    col.append(render_bucket("Interfaces", buckets[":VL-INTERFACE"]));
	    row.append(col);

	    delete buckets[":VL-TYPEDEF"];
	    delete buckets[":VL-INTERFACE"];
	    delete buckets[":VL-PACKAGE"];
	    delete buckets[":VL-FUNDECL"];
	    delete buckets[":VL-MODULE"];
	    delete buckets[":VL-PARAMDECL"];

	    col = jQuery("<td></td>");
	    if (buckets.length != 0) {
		col = jQuery("<td></td>");
		for (var type in buckets) {
		    col.append(render_bucket(type, buckets[type]));
		}
		row.append(col);
	    }
	    tbl.append(row);
	    $("#status").html(tbl);
	},
	error: function()
	{
	    $("#status").html("Error invoking /vls-get-desctypes");
	}
    });
}

function onConnected()
{
    toolbar_init();
    status_init();
}

$(document).ready(function() { connect(onConnected); });
