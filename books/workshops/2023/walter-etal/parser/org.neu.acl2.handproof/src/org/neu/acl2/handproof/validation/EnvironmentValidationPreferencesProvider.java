package org.neu.acl2.handproof.validation;

import java.util.List;

public class EnvironmentValidationPreferencesProvider implements IValidationPreferencesProvider {

	@Override
	public List<String> getProveFileSHPaths() {
		List<String> paths = this.defaultProveFileSHPaths();
		String pathFromEnv = getProveFileShPathFromEnvironment();
		if(pathFromEnv != null) {
			paths.add(0, pathFromEnv);
		}
		return paths;
	}
	
	public static String getProveFileShPathFromEnvironment() {
		if(System.getenv("PROVE_FILE_SH") != null) {
			return System.getenv("PROVE_FILE_SH");
		}
		return null;
	}

}
