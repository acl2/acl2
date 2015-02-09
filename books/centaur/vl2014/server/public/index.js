// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
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

function make_model_list_table(data)
{
    var div = jQuery("<table></table>");
    if (data == "NIL") {
	div.append("<p>No models</p>");
	return div;
    }

    var keys = Object.keys(data);
    for(var i in keys)
    {
	var base = keys[i];
	var models = data[base];
	var entry = "";
	entry += "<tr>";
	entry += "<td class='modelnames'>";
	for(var m = 0; m < models.length; m++)
	{
	    var model = models[m];
	    entry += "<a href=\"javascript:void(0)\" ";
	    entry += "onclick=\"loadModel('" + base + "', '" + model + "')\">";
	    entry += model;
	    entry += "</a>";
	    if (m != models.length - 1)
		entry += ", ";
	}
	entry += "</td>";
	entry += "<td class='basename'><nobr>" + base + "</nobr></td>";
	entry += "</tr>";
	div.append(entry);
    }
    return div;
}

function get_loaded()
{
    // Don't use vlsGetJson because this is a special pre-model-loading command
    // that has no MODEL/BASE.
    $.ajax({
	url: "/list-loaded",
	data: null,
	dataType: "json",
	cache: false,
	success: function(data,textStatus,jqXHR) {
	    if (data[":ERROR"]) {
		$("#loaded").html("Error: " + data[":ERROR"]);
		return;
	    }
	    var div = make_model_list_table(data[":VALUE"]);
	    $("#loaded").html(div);
	},
	fail: function() {
	    $("#loaded").html("<p>Error listing models.</p>");
	}
    });
}

function get_unloaded()
{
    // Don't use vlsGetJson because this is a special pre-model-loading command
    // that has no MODEL/BASE.
    $.ajax({
	url: "/list-unloaded",
	data: null,
	dataType: "json",
	cache: false,
	success: function(data,textStatus,jqXHR) {
	    if (data[":ERROR"]) {
		$("#unloaded").html("<p>Error: " + data[":ERROR"]);
		return;
	    }

	    var div = make_model_list_table(data[":VALUE"]);
	    $("#unloaded").html(div);
	},
	fail: function() {
	    $("#unloaded").html("<p>Error listing unloaded.</p>");
	}
    });
}

$(document).ready(function()
{
    get_loaded();
    get_unloaded();
});

var showedLoadingMessage = false;

function loadModel(base, model)
{
    console.log("loadModel(" + base + ", " + model + ")");
    $.ajax({
	url: "/load-model",
	cache: false,
	data: {"base":base, "model":model},
	dataType: "json",
	type: "post",
	success: function(data,textStatus,jqXHR)
	{
	    if (data[":ERROR"]) {
		$("body").html("Error: " + data[":ERROR"]);
		return;
	    }

	    var value = data[":VALUE"];
	    var status = value[":STATUS"];
	    console.log("Status: " + status);
	    if (status == ":LOADED") {
		window.location = "main.html?base=" + encodeURIComponent(base) + "&model=" + encodeURIComponent(model);
	    }
	    else if (status == ":STARTED")
	    {
		if (!showedLoadingMessage) {
		    var msg = "";
		    msg += "<div id='loadbox'>";
		    msg += "<h2><b>Loading " + model + " from " + base + "</b></h2>";
		    msg += "<p>This can take some time.  It usually completes within <b>2 minutes</b>, ";
		    msg += "except for some very large models.</p>";
		    msg += "<p>The page will automatically refresh when the model is ready.</p>";
		    msg += "<p id='progress'>.</p>";
		    msg += "<hr>";
		    msg += "</div>";
		    $("#loading").html(msg);
		    showedLoadingMessage = true;
		}
		else {
		    $("#progress").append(".");
		}
		setTimeout(function() { loadModel(base, model); }, 5000);
	    }
	    else {
		$("#content").html("<p>Unexpected response from server: "
				   + "value " + value
				   + "status " + status + "</p>");
	    }
	},
	fail: function()
	{
	    $("#content").html("<p>Error posting load_model request.</p>");
	}
    });
}
