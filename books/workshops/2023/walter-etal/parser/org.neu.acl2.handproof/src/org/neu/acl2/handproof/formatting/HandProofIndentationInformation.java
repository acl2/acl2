package org.neu.acl2.handproof.formatting;

import org.eclipse.xtext.formatting.IIndentationInformation;

public class HandProofIndentationInformation implements IIndentationInformation {

	@Override
	public String getIndentString() {
		return "  ";
	}

}
