package org.neu.acl2.handproof.web;

import java.util.List;

import org.eclipse.xtext.web.server.validation.ValidationResult;

public class MyValidationResult extends ValidationResult {
	private final String output;
	private final String query;

	public MyValidationResult(List<Issue> issues, String output, String query) {
		super();
		// Can't set because issues field is final but the constructor for ValidationResult doesn't
		// take an argument for it ¯\_(ツ)_/¯
		// Classic XText...
		for(Issue issue : issues) {
			this.getIssues().add(issue);
		}
		this.output = output;
		this.query = query;
	}
	
	public String getOutput() {
		return this.output;
	}
	
	public String getQuery() {
		return this.query;
	}
}
