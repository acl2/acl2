package org.neu.acl2.handproof.errorhandling;

import java.util.Arrays;
import java.util.stream.Collectors;
import static org.eclipse.xtext.diagnostics.Diagnostic.*;

import org.antlr.runtime.MissingTokenException;
import org.antlr.runtime.RecognitionException;
import org.eclipse.xtext.nodemodel.SyntaxErrorMessage;
import org.eclipse.xtext.parser.antlr.AbstractInternalAntlrParser;
import org.eclipse.xtext.parser.antlr.SyntaxErrorMessageProvider;
import org.neu.acl2.handproof.services.HandProofGrammarAccess;

import com.google.inject.Inject;

public class HandProofSyntaxErrorMessageProvider extends SyntaxErrorMessageProvider {
	
	private HandProofGrammarAccess grammarAccess;
	
	@Inject
	public HandProofSyntaxErrorMessageProvider(HandProofGrammarAccess grammarAccess) {
		this.grammarAccess = grammarAccess;
	}
	
	@Override
	public SyntaxErrorMessage getSyntaxErrorMessage(IParserErrorContext context) {
//		System.out.println(context);
//		System.out.println(context.getRecognitionException());
//		if(context.getRecognitionException() instanceof MissingTokenException) {
//			MissingTokenException e = (MissingTokenException) context.getRecognitionException();
//			System.out.println(e.inserted);
//			System.out.println(e.node);
//			System.out.println(e.token);
//			throw new RuntimeException("foo");
//		}
		RecognitionException e = context.getRecognitionException();
		if(e != null) {
//			System.out.println(e);
			StackTraceElement stackTrace[] = e.getStackTrace();
			SyntaxErrorMessage msg = super.getSyntaxErrorMessage(context);
//			System.out.println(msg);
			
			if(e instanceof MissingTokenException) {
				int expectedTokenId = ((MissingTokenException)e).expecting;
				System.out.println("Was a MissingTokenException");
				if(expectedTokenId >= 0) {
					System.out.println(context.getTokenNames()[expectedTokenId]);
					if(context.getTokenNames()[expectedTokenId].equals("RULE_RPAR")) {
						System.out.println("Was expecting an RPAR");
						if(Arrays.stream(stackTrace).anyMatch(item -> item.getMethodName().equals("ruleSExpression"))) {
							System.out.println("Probably missing a paren, going back to last token...");
//							throw new RuntimeException("foo");
							return new SyntaxErrorMessage("Missing a closing parenthesis", SYNTAX_DIAGNOSTIC);
//							return new SyntaxErrorMessage("Missing a closing parenthesis", SYNTAX_DIAGNOSTIC_WITH_RANGE, new String[] { e });
						}
					}
				} else {
					System.out.println("No expected token was provided.");
				}
			}
		}
		
//		System.out.println(msg.getIssueData());
//		System.out.println(context.getRecognitionException().getStackTrace());
//		System.out.println(
//				Arrays.stream(context.getRecognitionException().getStackTrace()).map(item -> item.getClassName() + ':' + item.getMethodName()).collect(Collectors.joining("\n"))
//		);
//		throw new RuntimeException("foo");
		return super.getSyntaxErrorMessage(context);
		//return msg;
	}
}
