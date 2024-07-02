package org.neu.acl2.handproof.web;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.eclipse.xtext.diagnostics.Severity;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;
import org.eclipse.xtext.web.server.model.IXtextWebDocument;
import org.eclipse.xtext.web.server.validation.ValidationResult;
import org.eclipse.xtext.web.server.validation.ValidationService;

import com.google.inject.Inject;

/** 
 * It is unclear to me under what conditions this validation service is used, versus CheckModeValidationService.
 * My guess is that it is used for internal validation requests.
 * @author drew
 *
 */
public class MyValidationService extends ValidationService {
	@Inject IResourceValidator myResourceValidator;
	
	public MyValidationService() {
		super();
		System.out.println("injected myvalidationservice");
	}
	
	@Override
	public MyValidationResult compute(IXtextWebDocument it, CancelIndicator cancelIndicator) {
		List<Issue> issues = this.myResourceValidator.validate(it.getResource(), CheckMode.FAST_ONLY, cancelIndicator);
		
		List<ValidationResult.Issue> filteredIssues = issues.stream()
				.filter(issue -> issue.getSeverity() != Severity.IGNORE && issue.getMessage() != "DATA")
				.map(issue -> new ValidationResult.Issue(issue.getMessage(), 
									translate(issue.getSeverity()),
									issue.getLineNumber(), 
									issue.getColumn(), 
									issue.getOffset(), 
									issue.getLength()))
				.collect(Collectors.toList());
		
		String output = "";
		String query = "";
		Optional<Issue> dataIssue = issues.stream().filter(issue -> issue.getSeverity() == Severity.INFO && issue.getMessage() == "DATA").findFirst();
		if(dataIssue.isPresent()) {
			Issue issue = dataIssue.get();
			output = issue.getData()[0];
			query = issue.getData()[1];
		}
		
		MyValidationResult result = new MyValidationResult(filteredIssues, output, query);
		return result;
	}
}
