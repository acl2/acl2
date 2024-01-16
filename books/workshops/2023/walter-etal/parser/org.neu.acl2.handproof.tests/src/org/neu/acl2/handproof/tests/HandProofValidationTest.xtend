package org.neu.acl2.handproof.tests

import com.google.inject.Inject
import org.eclipse.xtext.testing.InjectWith
import org.eclipse.xtext.testing.extensions.InjectionExtension
import org.eclipse.xtext.testing.util.ParseHelper
import org.junit.jupiter.api.^extension.ExtendWith
import org.neu.acl2.handproof.handProof.ProofDocument
import org.eclipse.xtext.testing.validation.ValidationTestHelper
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions
import java.util.stream.Stream
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.DynamicTest
import java.nio.file.Files
import java.nio.file.Paths
import static org.junit.jupiter.api.DynamicTest.dynamicTest
import org.eclipse.xtext.resource.XtextResource
import org.eclipse.xtext.validation.CheckMode
import org.eclipse.xtext.util.CancelIndicator
import org.eclipse.xtext.diagnostics.Severity

@ExtendWith(InjectionExtension)
@InjectWith(HandProofInjectorProvider)
class HandProofValidationTest {
	@Inject
	ParseHelper<ProofDocument> parseHelper
	
	@Inject extension ValidationTestHelper
	
	@Test 
	def void loadModel() {
		val result = parseHelper.parse('''
			(definec sum (n :nat) :nat
			   (if (equal n 0)
			       0
			     (+ n (sum (- n 1)))))
			
			Conjecture sum-base:
			(implies (and (natp n)
			              (equal n 0))
			         (equal (sum n) (/ (* n (+ n 1)) 2)))
			
			Context:
			C1. (natp n)
			C2. (equal n 0)
			
			Proof by: Equational Reasoning
			
			Goal: (equal (sum n) (/ (* n (+ n 1)) 2))
			
			Proof:
			(sum n)
			== { C2 }
			1
			== { Arithmetic, C2 }
			(/ (* n (+ n 1)) 2)
			
			QED
		''')
		Assertions.assertNotNull(result)
		result.assertNoErrors();
		//result.assertWarning(MyDslPackage.Literals.GREETING, MyDslValidator.INVALID_NAME)
	}
	
	
	@Test
	def void weird() {
		val result = parseHelper.parse('''
		(definec len2 (x :tl) :nat
		  (if (endp x)
		      0
		    (+ 1 (len2 (rest x)))))
		
		(definec in2 (a :all l :tl) :bool
		  (if (endp l)
		      nil
		    (or (== a (first l)) (in2 a (rest l)))))
		   
		(definec app2 (x :tl y :tl) :tl
		  (if (endp x)
		      y
		    (cons (first x) (app2 (rest x) y))))
		
		(definec rev2 (x :tl) :tl
		  (if (endp x)
		      x
		    (app2 (rev2 (cdr x)) (list (car x)))))
		
		;; Question 2e.
		
		Conjecture 2e:
		(implies (endp x)
		         (implies (in2 a (app2 x y))
		                  (implies (not (in2 a x))
		                           (in2 a y))))
		
		Exportation:
		(implies (and (endp x)
		              (in2 a (app2 x y))
		              (not (in2 a x)))
		         (in2 a y))
		
		Contract Completion:
		(implies (and (tlp x)
		              (tlp y)
		              (endp x)
		              (in2 a (app2 x y))
		              (not (in2 a x)))
		         (in2 a y))
		
		Context:
		C1. (tlp x)
		C2. (tlp y)
		C3. (endp x)
		C4. (in2 a (app2 x y))
		C5. (not (in2 a x))
		
		Derived Context:
		D1. (equal x nil) {Def tlp, C1, C3}
		D2. (in2 a y) {C4, Def app2, D1}
		
		QED
		
		;; Question 2g.
		Conjecture 2g:
		(implies (and (consp x)
		              (implies (and (tlp (rest x))
		                            (tlp y))
		                       (implies (in2 a (app2 (rest x) y))
		                                (implies (not (in2 a (rest x)))
		                                         (in2 a y)))))
		         (implies (in2 a (app2 x y))
		                  (implies (not (in2 a x))
		                           (in2 a y))))
		
		Exportation:
		(implies (and (consp x)
		     (implies (and (tlp (rest x))
		                   (tlp y)
		                   (in2 a (app2 (rest x) y))
		                   (not (in2 a (rest x))))
		              (in2 a y))
		     (in2 a (app2 x y))
		     (not (in2 a x)))
		         (in2 a y))
		
		Contract Completion:
		(implies (and (tlp x)
		              (tlp y)
		              (consp x)
		     (implies (and (tlp (rest x))
		                   (tlp y)
		                   (in2 a (app2 (rest x) y))
		                   (not (in2 a (rest x))))
		              (in2 a y))
		     (in2 a (app2 x y))
		     (not (in2 a x)))
		         (in2 a y))
		
		Context:
		C1. (tlp x)
		C2. (tlp y)
		C3. (consp x)
		C4. (implies (and (tlp (rest x))
		                  (tlp y)
		                  (in2 a (app2 (rest x) y))
		                  (not (in2 a (rest x))))
		             (in2 a y))
		C5. (in2 a (app2 x y))
		C6. (not (in2 a x))
		
		Derived Context:
		D1. (tlp (rest x)) {Def tlp, C1, C3}
		D2. (not (or (== a (first x))
		             (in2 a (rest x))))  {Def in2, C6, C3}
		D3. (and (not (== a (first x)))
		         (not (in2 a (rest x)))) {D2, PL}
		D4. (not (== a (first x))) {D3, PL}
		D5. (not (in2 a (rest x))) {D3, PL}
		D6. (in2 a (cons (first x) (app2 (rest x) y))) {C5, Def app2, C3}
		D7. (or (== a (first x))
		        (in2 a (app2 (rest x) y)))  {Def in2, D6, cons axioms}
		D8. (in2 a (app2 (rest x) y))  {D7, D4, PL}
		D9. (in a y) {C4, D1, C2, D8, D5, MP}
		
		QED
		''')
		Assertions.assertNotNull(result)
		result.assertNoErrors();
	}
	
	@TestFactory
	def Stream<DynamicTest> testFiles() {
		Files.walk(Paths.get("../../tests/pass/"))
				.filter([file | Files.isRegularFile(file)])
	            .map([file | dynamicTest(
	                    "Test for file: " + file,
	                    [|  val contents = new String(Files.readAllBytes(file))
	                    	val result = parseHelper.parse(contents)
	                    	Assertions.assertNotNull(result)
							val errors = result.eResource.errors
							Assertions.assertTrue(errors.isEmpty, '''Unexpected errors: «errors.join(", ")»''')
							result.assertNoErrors()
	                    ])
	               ])
	}
	
	@TestFactory
	def Stream<DynamicTest> testFailFiles() {
		Files.walk(Paths.get("../../tests/fail/"))
				.filter([file | Files.isRegularFile(file) && file.toString.endsWith(".lisp")])
	            .map([file | dynamicTest(
	                    "Test for file: " + file,
	                    [|  val contents = new String(Files.readAllBytes(file))
	                    	val result = parseHelper.parse(contents)
	                    	Assertions.assertNotNull(result)
							val errors = result.eResource.errors
							Assertions.assertTrue(errors.isEmpty, '''Unexpected errors: «errors.join(", ")»''')
							val validator = (result.eResource as XtextResource).getResourceServiceProvider()
									.getResourceValidator();
							val issues = validator.validate(result.eResource, CheckMode.ALL, CancelIndicator.NullImpl);
							Assertions.assertTrue(issues.stream().anyMatch([issue | issue.severity == Severity.ERROR]))
	                    ])
	               ])
	}
}