package org.neu.acl2.handproof.web;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.web.server.occurrences.OccurrencesService;
import org.neu.acl2.handproof.handProof.SExpression;

public class MyOccurrencesService extends OccurrencesService {
	@Override
	protected boolean filter(EObject element) {
		if(element instanceof SExpression) {
			return false;
		}
		return super.filter(element);
	}
}
