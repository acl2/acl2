package org.neu.acl2.handproof.validation;

import com.google.inject.Singleton;

@Singleton
public class ValidationFilePathProvider implements IValidationFilePathProvider {
	private String filePath;
	
	public String getPath() {
		return this.filePath;
	}
	
	public void setPath(String path) {
		this.filePath = path;
	}
}
