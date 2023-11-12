package org.neu.acl2.handproof.validation;

public interface IValidationMessageHandler {
	
	void handleError(String title, String message);
	void handleWarning(String title, String message);
	void handleInfo(String title, String message);
	void handleOutput(String output);

}
