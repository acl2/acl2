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

function safeIntValue(str)
{
    "use strict";
    assert(/[0-9]+/.test(str), "Invalid number " + str);
    return Number(str);
}

function sortModelList(data)
{
    "use strict";

    var arr = [];
    for(var model in data)
    {
	if (!data.hasOwnProperty(model)) continue;
	var elem = data[model];
	assert("name" in elem);
	assert("date" in elem);
	assert("ltime" in elem);
	assert("compat" in elem);
	elem.model = model;
	elem.ltime = safeIntValue(elem.ltime);
	arr.push(elem);
    }

    return arr.sort(function(a,b) { return b.ltime - a.ltime; });
}

function make_model_list_table(data)
{
    "use strict";
    var div = jQuery("<table></table>");
    if (data == "NIL") {
	div.append("<p>No models</p>");
	return div;
    }

    log("make_model_list_table");
    log(data);

    var arr = sortModelList(data);

    for(var i in arr)
    {
	var elem = arr[i];
	var model = elem.model;

	var entry = "";
	entry += "<tr>";
	entry += "<td class='modelnames'>";

	if (elem.compat == "T") {
	    entry += "<a href=\"javascript:void(0)\" ";
	    entry += "onclick=\"loadModel('" + model + "')\">";
	    entry += elem.name;
	    entry += "</a> ";
	}
	else {
	    entry += elem.name;
	}

	entry += " &nbsp; <small>" + elem.date + "</small>";

	entry += "</td>";
	entry += "</tr>";
	div.append(entry);
    }
    return div;
}

function get_loaded()
{
    "use strict";
    // Don't use vlsGetJson because this is a special pre-model-loading command
    // that has no MODEL
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
    "use strict";
    // Don't use vlsGetJson because this is a special pre-model-loading command
    // that has no MODEL
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

function loadModel(model)
{
    "use strict";
    log("loadModel(" + model + ")");
    $.ajax({
	url: "/load-model",
	cache: false,
	data: {"model":model},
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
	    log("Status: " + status);
	    if (status == ":LOADED") {
		window.location = "main.html?model=" + encodeURIComponent(model);
	    }
	    else if (status == ":STARTED")
	    {
		if (!showedLoadingMessage) {
		    var msg = "";
		    msg += "<div id='loadbox'>";
		    msg += "<h2><b>Loading " + model + "</b></h2>";
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
		setTimeout(function() { loadModel(model); }, 5000);
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
