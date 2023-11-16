package org.neu.acl2.handproof.validation;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public interface IValidationPreferencesProvider {
	
	/**
	 * Get the first path 
	 * @return
	 */
	default String getProveFileSH() {
		List<String> paths = this.getProveFileSHPaths();
		String cmd = "prove-file-java.sh";
		for (String path : paths) {
			File f = new File(path);
			if (f.exists() && !f.isDirectory()) {
				cmd = path;
				break;
			}
		}
		return cmd;
	}
	
	List<String> getProveFileSHPaths();
	
	default List<String> defaultProveFileSHPaths() {
		ArrayList<String> paths = new ArrayList<String>();
		// DREW: added some paths used by our packages.
		// using standard Homebrew configuration on Linux
		paths.add("/home/linuxbrew/.linuxbrew/bin/prove-file-java.sh");
		// Using standard Homebrew configuration on macOS x86
		paths.add("/usr/local/bin/prove-file-java.sh");
		// Using standard Homebrew configuration on macOS M1
		paths.add("/opt/homebrew/bin/prove-file-java.sh");
		// On the Khoury VDI system
		paths.add("/proj/acl2s/prove-file-java.sh");
		return paths;
	}

}
