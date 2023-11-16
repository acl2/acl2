package org.neu.acl2.handproof.web;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.eclipse.xtext.diagnostics.Severity;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.util.concurrent.CancelableUnitOfWork;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;
import org.eclipse.xtext.web.server.model.IXtextWebDocument;
import org.eclipse.xtext.web.server.model.XtextWebDocumentAccess;
import org.eclipse.xtext.web.server.validation.ValidationResult;

import com.google.inject.Inject;

/**
 * This service is only called for validation requests that specify a CheckMode
 * @author drew
 *
 */
public class CheckModeValidationService {
	@Inject
	IResourceValidator resourceValidator;

	public ValidationResult validate(XtextWebDocumentAccess it, CheckMode mode) {
		final CancelableUnitOfWork<List<Issue>, IXtextWebDocument> _function = new CancelableUnitOfWork<List<Issue>, IXtextWebDocument>() {
			@Override
			public List<Issue> exec(final IXtextWebDocument it, final CancelIndicator cancelIndicator)
					throws Exception {
				return resourceValidator.validate(it.getResource(), mode, cancelIndicator);
			}
		};

		List<Issue> issues = it.readOnly(_function);
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

	protected String translate(Severity severity) {
		switch (severity) {
		case WARNING:
			return "warning";
		case ERROR:
			return "error";
		case INFO:
			return "info";
		default:
			return "ignore";
		}
	}
}
