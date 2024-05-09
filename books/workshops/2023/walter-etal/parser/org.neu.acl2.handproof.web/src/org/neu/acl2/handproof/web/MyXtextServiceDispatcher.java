package org.neu.acl2.handproof.web;

import java.security.InvalidParameterException;
import java.util.List;

import javax.xml.transform.Source;

import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.web.server.IServiceContext;
import org.eclipse.xtext.web.server.IServiceResult;
import org.eclipse.xtext.web.server.InvalidRequestException;
import org.eclipse.xtext.web.server.XtextServiceDispatcher;
import org.eclipse.xtext.web.server.model.XtextWebDocumentAccess;
import org.eclipse.xtext.xbase.lib.Functions.Function0;

import com.google.inject.Inject;

public class MyXtextServiceDispatcher extends XtextServiceDispatcher {
	@Inject
	CheckModeValidationService checkModeValidationService;
	
	@Inject
	CodeFoldingService codeFoldingService;
	
	public CheckModeValidationService getCheckModeValidationService() {
		return this.checkModeValidationService;
	}
	
	@Override
	protected ServiceDescriptor createServiceDescriptor(String serviceType, IServiceContext context) {
		if(serviceType.equals("validator")) {
			return getValidationService(context);
		} else if(serviceType.equals("codeFolding")) {
			return getCodeFoldingService(context);
		}
		// TODO Auto-generated method stub
		return super.createServiceDescriptor(serviceType, context);
	}
	
	@Override
	protected ServiceDescriptor getValidationService(IServiceContext context) throws InvalidRequestException, InvalidParameterException {
		XtextWebDocumentAccess document = getDocumentAccess(context);
		final CheckMode requestedMode = getCheckModeParameter(context);
		
		return new ServiceDescriptor() {
			@Override
			public Function0<? extends IServiceResult> getService() {
				return () -> {
					try {
						return getCheckModeValidationService().validate(document, requestedMode);
					} catch (Throwable throwable) {
						return handleError(this, throwable);
					}
				};
			}
		};
	}
	
	protected ServiceDescriptor getCodeFoldingService(IServiceContext context) throws InvalidRequestException {
		XtextWebDocumentAccess document = getDocumentAccess(context);
		ServiceDescriptor serviceDescriptor = new ServiceDescriptor();
		serviceDescriptor.setService(() -> {
			try {
				return codeFoldingService.getResult(document);
			} catch (Throwable throwable) {
				return handleError(serviceDescriptor, throwable);
			}
		});
		return serviceDescriptor;
	}
	
	private CheckMode getCheckModeParameter(IServiceContext context) throws InvalidRequestException, InvalidParameterException {
		if(context.getParameterKeys().contains("checkmode")) {
			if(context.getParameter("checkmode") == null || context.getParameter("checkmode").length() == 0) {
				throw new InvalidParameterException("CheckMode parameter cannot be empty!");
			}
			switch(context.getParameter("checkmode").toLowerCase()) {
				case "all": return CheckMode.ALL; 
				case "fast": return CheckMode.FAST_ONLY;
				case "normal": return CheckMode.NORMAL_ONLY;
				case "expensive": return CheckMode.EXPENSIVE_ONLY;
				default: throw new InvalidParameterException("Did not recognize the CheckMode parameter: " + context.getParameter("checkmode"));
			}
		} else {
			return CheckMode.FAST_ONLY;
		}
	}
}
