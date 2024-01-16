package org.neu.acl2.handproof.validation;

import org.apache.log4j.Logger;

import com.google.inject.Singleton;

@Singleton
public class LoggingValidationMessageHandler implements IValidationMessageHandler {
	
	private boolean shouldHandleOutput = true;

	@Override
	public void handleError(String title, String message) {
		Logger.getLogger(this.getClass()).error(title + ": " + message);
	}

	@Override
	public void handleWarning(String title, String message) {
		Logger.getLogger(this.getClass()).warn(title + ": " + message);
	}

	@Override
	public void handleInfo(String title, String message) {
		Logger.getLogger(this.getClass()).info(title + ": " + message);
	}
	
	@Override
	public void handleOutput(String output) {
		if(shouldHandleOutput) {
			Logger.getLogger(this.getClass()).info(output);
		}
	}
	
	public void setShouldHandleOutput(boolean val) {
		this.shouldHandleOutput = val;
	}
}
