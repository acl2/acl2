package org.neu.acl2.handproof.util;

import java.util.List;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.util.PolymorphicDispatcher;
import org.neu.acl2.handproof.handProof.ArithmeticHint;
import org.neu.acl2.handproof.handProof.AxiomHint;
import org.neu.acl2.handproof.handProof.BackquotedSExpressionExpr;
import org.neu.acl2.handproof.handProof.CommaSExpression;
import org.neu.acl2.handproof.handProof.Const;
import org.neu.acl2.handproof.handProof.Context;
import org.neu.acl2.handproof.handProof.ContextHint;
import org.neu.acl2.handproof.handProof.DefHint;
import org.neu.acl2.handproof.handProof.DefineC;
import org.neu.acl2.handproof.handProof.DefineCSExp;
import org.neu.acl2.handproof.handProof.DefunC;
import org.neu.acl2.handproof.handProof.DefunCSExp;
import org.neu.acl2.handproof.handProof.DerivedContext;
import org.neu.acl2.handproof.handProof.EvalHint;
import org.neu.acl2.handproof.handProof.HintList;
import org.neu.acl2.handproof.handProof.InputContract;
import org.neu.acl2.handproof.handProof.LemmaHint;
import org.neu.acl2.handproof.handProof.ModusPonensHint;
import org.neu.acl2.handproof.handProof.ObviousMagicHint;
import org.neu.acl2.handproof.handProof.OptionallyDottedSExpList;
import org.neu.acl2.handproof.handProof.OptionallyDottedSExpListExpr;
import org.neu.acl2.handproof.handProof.OutputContract;
import org.neu.acl2.handproof.handProof.Proof;
import org.neu.acl2.handproof.handProof.ProofBody;
import org.neu.acl2.handproof.handProof.ProofBy;
import org.neu.acl2.handproof.handProof.ProofDocument;
import org.neu.acl2.handproof.handProof.ProofList;
import org.neu.acl2.handproof.handProof.ProofName;
import org.neu.acl2.handproof.handProof.ProofTypeEquationalReasoning;
import org.neu.acl2.handproof.handProof.ProofTypeInduction;
import org.neu.acl2.handproof.handProof.PropLogicHint;
import org.neu.acl2.handproof.handProof.Property;
import org.neu.acl2.handproof.handProof.PropertySExp;
import org.neu.acl2.handproof.handProof.QuotedSExpressionExpr;
import org.neu.acl2.handproof.handProof.SExpList;
import org.neu.acl2.handproof.handProof.SExpression;
import org.neu.acl2.handproof.handProof.Symbol;
import org.neu.acl2.handproof.handProof.contextItem;
import org.neu.acl2.handproof.handProof.dcontextItem;

public class CheckerValueConverter {
	
	private static <T> int indexOfIdentity(List<T> list, T o) {
		int i = 0;
		for(T item : list) {
			if(o == item) {
				return i;
			}
			i++;
		}
		return -1;
	}

	private List<EObject> allNodes;

	public CheckerValueConverter(List<EObject> allNodes) {
		this.allNodes = allNodes;
	}

	private final PolymorphicDispatcher<String> toLispDispatcher = PolymorphicDispatcher.createForSingleTarget("toLisp", this);
	
	// TODO: figure out a way to prevent infinite recursion here
	public String toLisp(EObject o) {
		return toLispDispatcher.invoke(o);
	}
	
	public String toLisp(ProofDocument val) {
		StringBuilder b = new StringBuilder();
		b.append("(\n");
		for(EObject proofOrStmt : val.getProofsAndStatements()) {
			if(proofOrStmt instanceof SExpression) {
				b.append(toTaggedSExpr((SExpression)proofOrStmt));
			} else {
				b.append(toLisp(proofOrStmt));
			}
			b.append("\n");
		}
		b.append("\n)");
		return b.toString();
	}
	
	public String toTaggedSExpr(SExpression sexpr) {
		StringBuilder b = new StringBuilder("#S(structs::TaggedSExpr");
		b.append(" :id ");
		b.append("" + indexOfIdentity(this.allNodes, sexpr));
		b.append(" :expr ");
		b.append(toLisp(sexpr));
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(ProofName val) {
		if(val.getName().matches("[0-9]+")) {
			return "|" + val.getName() + "|";
		} else {
			return val.getName();
		}
	}

	public String toLisp(Proof val) {
		StringBuilder b = new StringBuilder("#S(structs::Proof");
		b.append(" :id ");
		b.append("" + indexOfIdentity(this.allNodes, val));
		b.append(" :kind \"");
		b.append(val.getHeader().getName().getKind());
		b.append("\" :name \"");
		b.append(val.getHeader().getName().getName());
		b.append("\" :stmt ");
		b.append(toTaggedSExpr(val.getStatement()));
		
		// TODO: pass exportation section here for better error message locations
		b.append(" :exportation ");
		if(val.getExportation() != null) {
			b.append(toTaggedSExpr(val.getExportation().getExpression()));
		} else {
			b.append("nil ");
		}

		// TODO: pass contract completion section here for better error message locations
		b.append(" :contract-completion ");
		if(val.getCompletion() != null) {
			b.append(toTaggedSExpr(val.getCompletion().getExpression()));
		} else {
			b.append("nil ");
		}
		
		if(val.getProofby() == null || val.getProofby().getType() == null || val.getProofby().getType() instanceof ProofTypeEquationalReasoning) {
			b.append(" :strategy ");
			if(val.getProofby() == null || val.getProofby().getType() == null) {
				b.append("#S(structs::ProofStrategy :kind :equational-reasoning)");
			} else {
				b.append(toLisp(val.getProofby()));
			}

			if(val.getContext() != null) {
				b.append(" :ctx ");
				b.append(toLisp(val.getContext()));
			}
			
			if(val.getDerivedContext() != null) {
				b.append(" :derived-ctx ");
				b.append(toLisp(val.getDerivedContext()));
			}
			
			if(val.getGoal() != null) {
				b.append(" :goal ");
				b.append(toTaggedSExpr(val.getGoal().getGoal()));
			} else {
				b.append(" :goal ");
				b.append(" :missing ");
			}

			ProofBody pb = (ProofBody) val.getBody();
			if(pb != null) {
				int numSteps = pb.getRestStatements().size();
				b.append(" :steps (");
				for(int i = 0; i < numSteps; i++) {
					if(i == 0) {
						b.append(stepToLisp(pb.getRels().get(0), pb.getFirstStatement(), pb.getRestStatements().get(0), pb.getHints().get(0)));
						b.append(" ");
					} else {
						b.append(stepToLisp(pb.getRels().get(i), pb.getRestStatements().get(i-1), pb.getRestStatements().get(i), pb.getHints().get(i)));
						b.append(" ");
					}
				}
				b.append(")");
			}
		}
		
		if(val.getProofby() != null && val.getProofby().getType() instanceof ProofTypeInduction) {
			b.append(" :strategy ");
			b.append(toLisp(val.getProofby()));
			
			if(val.getContext() != null) {
				b.append(" :ctx ");
				b.append(toLisp(val.getContext()));
			}
			
			if(val.getDerivedContext() != null) {
				b.append(" :derived-ctx ");
				b.append(toLisp(val.getDerivedContext()));
			}
			
			if(val.getGoal() != null) {
				b.append(" :goal ");
				b.append(toTaggedSExpr(val.getGoal().getGoal()));
			} else {
				b.append(" :goal ");
            	b.append(" :missing ");
            }

			ProofList pl = (ProofList) val.getBody();
			if(pl != null) {
				b.append(" :cases (\n");
				for(Proof p : pl.getProofs()) {
					b.append(toLisp(p));
					b.append("\n");
				}
				b.append(")\n");
			}
		}
		b.append(")");
		return b.toString();
	}
	
	public String relToLisp(String rel) {
		return rel;
	}
	
	public String stepToLisp(String rel, SExpression before, SExpression after, HintList hints) {
		StringBuilder b = new StringBuilder("#S(structs::ProofStep");
		b.append(" :id ");
		b.append("(" + indexOfIdentity(this.allNodes, before) + " " + indexOfIdentity(this.allNodes, after) + ")");
		b.append(" :rel ");
		b.append(relToLisp(rel));
		b.append(" :before ");
		b.append(toTaggedSExpr(before));
		b.append(" :after ");
		b.append(toTaggedSExpr(after));
		b.append(" :hints ");
		b.append(toLisp(hints));
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(ProofBy val) {
		if(val.getType() instanceof ProofTypeEquationalReasoning) {
			return "#S(structs::ProofStrategy :kind :equational-reasoning)";
		} else if(val.getType() instanceof ProofTypeInduction) {
			return "#S(structs::ProofStrategy :kind :induction :params " + toTaggedSExpr(val.getCases()) + ")";
		}
		throw new RuntimeException("Unsupported proof strategy: " + val.toString());
	}
	
	public String toLisp(Context val) {
		StringBuilder b = new StringBuilder("(");
		val.getContext().forEach(item -> {
			b.append(toLisp(item));
			b.append(" ");
		});
		
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(DerivedContext val) {
		StringBuilder b = new StringBuilder("(");
		val.getDerivedContext().forEach(item -> {
			b.append(toLisp(item));
			b.append(" ");
		});
		
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(DefineC val) {
		StringBuilder b = new StringBuilder("#S(structs::TaggedSExpr");
		b.append(" :id ");
		b.append("" + indexOfIdentity(this.allNodes, val));
		b.append(" :expr ");
		b.append("(definec ");
		b.append(val.getName());
		b.append(" ");
		b.append(toLisp(val.getParameters()));
		b.append(" ");
		b.append(val.getReturnType());
		b.append("\n");
		if(val.getIc() != null) {
			b.append(toLisp(val.getIc()));
			b.append("\n");
		}
		if(val.getOc() != null) {
			b.append(toLisp(val.getOc()));
			b.append("\n");
		}
		val.getBody().forEach(item -> {
			b.append(toLisp(item));
			b.append("\n");
		});
		b.append("))");
		return b.toString();
	}
	
	public String toLisp(InputContract val) {
		return ":input-contract " + toLisp(val.getBody());
	}
	
	public String toLisp(OutputContract val) {
		return ":output-contract " + toLisp(val.getBody());
	}
	
	public String toLisp(DefunC val) {
		StringBuilder b = new StringBuilder("#S(structs::TaggedSExpr");
		b.append(" :id ");
		b.append("" + indexOfIdentity(this.allNodes, val));
		b.append(" :expr ");
		b.append("(defunc ");
		b.append(val.getName());
		b.append(" ");
		b.append(toLisp(val.getArguments()));
		b.append(" ");
		b.append(toLisp(val.getIc()));
		b.append(" ");
		b.append(toLisp(val.getOc()));
		b.append("\n");
		val.getBody().forEach(item -> {
			b.append(toLisp(item));
			b.append("\n");
		});
		b.append("))");
		return b.toString();
	}
	
	public String toLisp(Property val) {
		StringBuilder b = new StringBuilder("#S(structs::TaggedSExpr");
		b.append(" :id ");
		b.append("" + indexOfIdentity(this.allNodes, val));
		b.append(" :expr ");
		b.append("(property ");
		if(val.getName() != null) {
			b.append(val.getName());
			b.append(" ");
		}
		b.append(toLisp(val.getArgs()));
		b.append("\n");
		val.getBody().forEach(item -> {
			b.append(toLisp(item));
			b.append("\n");
		});
		b.append("))");
		return b.toString();
	}
	
	public String toLisp(OptionallyDottedSExpListExpr val) {
		return toLisp(val.getList());
	}
	
	public String toLisp(SExpList val) {
		StringBuilder b = new StringBuilder();
		b.append("(");
		val.getBody().forEach(sexp -> {
			b.append(toLisp(sexp));
			b.append(" ");
		});
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(OptionallyDottedSExpList val) {
		StringBuilder b = new StringBuilder();
		b.append("(");
		val.getBody().forEach(sexp -> {
			b.append(toLisp(sexp));
			b.append(" ");
		});
		if(val.getRight() != null) {
			b.append(". ");
			b.append(toLisp(val.getRight()));
		}
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(CommaSExpression val) {
		if(val.getSplice() != null) {
			return ",@" + toLisp(val.getSexp());
		} else {
			return "," + toLisp(val.getSexp());
		}
	}
	
	public String toLisp(QuotedSExpressionExpr val) {
		return "'" + toLisp(val.getSexp());
	}
	
	public String toLisp(BackquotedSExpressionExpr val) {
		return "`" + toLisp(val.getSexp());
	}
	
	public String toLisp(Const val) {
		return val.getValue();
	}
	
	public String toLisp(Symbol val) {
		return val.getValue();
	}
	
	public String toLisp(DefineCSExp val) {
		return toLisp(val.getValue());
	}
	
	public String toLisp(DefunCSExp val) {
		return toLisp(val.getValue());
	}
	
	public String toLisp(PropertySExp val) {
		return toLisp(val.getValue());
	}
	
	public String toLisp(contextItem val) {
		StringBuilder b = new StringBuilder("#S(structs::CtxItem ");
		b.append(" :name proof::");
		b.append(val.getName());
		b.append(" :stmt ");
		b.append(toTaggedSExpr(val.getBody()));
		b.append(" :id ");
		b.append(indexOfIdentity(this.allNodes, val));
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(dcontextItem val) {
		StringBuilder b = new StringBuilder("#S(structs::CtxItem");
		b.append(" :name proof::");
		b.append(val.getName());
		b.append(" :stmt ");
		b.append(toTaggedSExpr(val.getBody()));
		b.append(" :hints ");
		b.append(toLisp(val.getHints()));
		b.append(" :id ");
		b.append(indexOfIdentity(this.allNodes, val));
		b.append(")");
		return b.toString();
	}
	
	private String taggedSExprWithExpr(EObject val, String expr) {
		StringBuilder b = new StringBuilder("#S(structs::TaggedSExpr ");
		b.append(":expr ");
		b.append(expr);
		b.append(" :id ");
		b.append(indexOfIdentity(this.allNodes, val));
		b.append(")");
		return b.toString();
	}
	
	public String toLisp(ObviousMagicHint val) {
		return taggedSExprWithExpr(val, ":noop");
	}
	
	public String toLisp(ModusPonensHint val) {
		return taggedSExprWithExpr(val, ":modus-ponens");
	}
	
	public String toLisp(ArithmeticHint val) {
		return taggedSExprWithExpr(val, ":arith");
	}
	
	public String toLisp(PropLogicHint val) {
		return taggedSExprWithExpr(val, ":prop-logic");
	}
	
	public String toLisp(EvalHint val) {
		return taggedSExprWithExpr(val, ":eval");
	}
	
	public String toLisp(DefHint val) {
		return taggedSExprWithExpr(val, "(:fun " + val.getName() + ")");
	}
	
	public String toLisp(ContextHint val) {
		return taggedSExprWithExpr(val, "(:context proof::" + val.getName() + ")");
	}
	
	public String toLisp(AxiomHint val) {
		return taggedSExprWithExpr(val, "(:axiom proof::" + val.getName() + ")");
	}
	
	public String toLisp(LemmaHint val) {
		StringBuilder b = new StringBuilder("(:lemma ");
		b.append(toLisp(val.getName()));
		if(val.getInstantiation() != null) {
			b.append(" acl2s::");
			b.append(toLisp(val.getInstantiation()));
		} else {
			b.append(" nil");
		}
		b.append(")");
		return taggedSExprWithExpr(val, b.toString());
	}
	
	public String toLisp(HintList val) {
		StringBuilder b = new StringBuilder("(");
		b.append(toLisp(val.getFirst()));
		if(val.getRest() != null) {
			b.append(" ");
			val.getRest().forEach(hint -> b.append(toLisp(hint) + " "));
		}
		b.append(")");
		return b.toString();
	}
}
