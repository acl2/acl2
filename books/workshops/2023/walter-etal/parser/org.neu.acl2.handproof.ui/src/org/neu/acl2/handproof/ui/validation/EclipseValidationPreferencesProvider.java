package org.neu.acl2.handproof.ui.validation;

import java.util.List;

import org.neu.acl2.handproof.validation.IValidationPreferencesProvider;

import com.google.inject.Inject;

public class EclipseValidationPreferencesProvider implements IValidationPreferencesProvider {
	
	@Inject
	private ValidationPreferenceAccess preferenceAccess;
	
	@Override
	public List<String> getProveFileSHPaths() {
		List<String> paths = this.defaultProveFileSHPaths();
		String prefAccessPath = preferenceAccess.getProveFileShPath();
		if(prefAccessPath != null) {
			paths.add(0, prefAccessPath);
		}
		return paths;
	}
}
