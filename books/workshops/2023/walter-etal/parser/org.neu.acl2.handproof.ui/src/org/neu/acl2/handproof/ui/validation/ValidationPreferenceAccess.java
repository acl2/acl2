package org.neu.acl2.handproof.ui.validation;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.xtext.ui.editor.preferences.IPreferenceStoreAccess;
import org.eclipse.xtext.ui.editor.preferences.IPreferenceStoreInitializer;
import org.neu.acl2.handproof.validation.EnvironmentValidationPreferencesProvider;

import com.google.inject.Inject;

public class ValidationPreferenceAccess {
	public static final String PREF_PROVE_FILE_SH_PATH = "prove-file-sh-path";

	public static class Initializer implements IPreferenceStoreInitializer {

		@Override
		public void initialize(IPreferenceStoreAccess access) {
			IPreferenceStore store = access.getWritablePreferenceStore();
			store.setDefault(PREF_PROVE_FILE_SH_PATH, "");
		}
	
	}
	
	@Inject
	private IPreferenceStoreAccess access;
	
	public String getProveFileShPath() {
		IPreferenceStore store = this.access.getPreferenceStore();
		if(store.contains(PREF_PROVE_FILE_SH_PATH) && !store.getString(PREF_PROVE_FILE_SH_PATH).isEmpty()) {
			return store.getString(PREF_PROVE_FILE_SH_PATH);
		} else {
			return EnvironmentValidationPreferencesProvider.getProveFileShPathFromEnvironment();
		}
	}
}
