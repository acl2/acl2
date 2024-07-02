package org.neu.acl2.handproof.ui.validation;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.xtext.ui.editor.validation.MarkerCreator;
import org.eclipse.xtext.validation.Issue;
import org.neu.acl2.handproof.validation.HandProofValidator;

import com.google.inject.Inject;

/**
 * This class exists to allow us to filter out certain types of validation messages that we produce to communicate with the web client.
 * @author drew
 *
 */
public class MyMarkerCreator extends MarkerCreator {
	@Inject
	CheckerOutputStorage checkerOutput;
	
	@Override
	public void createMarker(Issue issue, IResource resource, String markerType) throws CoreException {
		if(issue.getMessage().equals("DATA")) {
		} else if(issue.getCode().equals(HandProofValidator.VALIDATION_TIMING)) {
		} else {
			IMarker marker = resource.createMarker(markerType);
			super.setMarkerAttributes(issue, resource, marker);
			marker.setAttribute(IMarker.TRANSIENT, true);
		}
	}

}
