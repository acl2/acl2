/*
 * generated by Xtext 2.29.0
 */
package org.neu.acl2.handproof;


/**
 * Initialization support for running Xtext languages without Equinox extension registry.
 */
public class HandProofStandaloneSetup extends HandProofStandaloneSetupGenerated {

	public static void doSetup() {
		new HandProofStandaloneSetup().createInjectorAndDoEMFRegistration();
	}
}
