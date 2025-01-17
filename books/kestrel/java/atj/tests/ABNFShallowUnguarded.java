import edu.kestrel.acl2.aij.*;
import java.math.BigInteger;

public class ABNFShallowUnguarded {

    static {
        ABNFShallowUnguardedEnvironment.build();
    }

    public static void initialize() {
    }

    public static class KEYWORD {

        static final Acl2Symbol $Q_LEAFRULE = Acl2Symbol.make("KEYWORD", "LEAFRULE");

        static final Acl2Symbol $Q_LEAFTERM = Acl2Symbol.make("KEYWORD", "LEAFTERM");

        static final Acl2Symbol $Q_NONLEAF = Acl2Symbol.make("KEYWORD", "NONLEAF");

        static final Acl2Symbol $Q_RULENAME = Acl2Symbol.make("KEYWORD", "RULENAME");
    }

    public static class COMMON_LISP {

        public static Acl2Value atom(Acl2Value x) {
            return not(consp(x));
        }

        public static Acl2Value car(Acl2Value x) {
            return Acl2NativeFunction.execCar(x);
        }

        public static Acl2Value cdr(Acl2Value x) {
            return Acl2NativeFunction.execCdr(x);
        }

        public static Acl2Value char_code(Acl2Value x) {
            return Acl2NativeFunction.execCharCode(x);
        }

        public static Acl2Value characterp(Acl2Value x) {
            return Acl2NativeFunction.execCharacterp(x);
        }

        public static Acl2Value code_char(Acl2Value x) {
            return Acl2NativeFunction.execCodeChar(x);
        }

        public static Acl2Value cons(Acl2Value x, Acl2Value y) {
            return Acl2NativeFunction.execCons(x, y);
        }

        public static Acl2Value consp(Acl2Value x) {
            return Acl2NativeFunction.execConsp(x);
        }

        public static Acl2Value eq(Acl2Value x, Acl2Value y) {
            return equal(x, y);
        }

        public static Acl2Value eql(Acl2Value x, Acl2Value y) {
            return equal(x, y);
        }

        public static Acl2Value equal(Acl2Value x, Acl2Value y) {
            return Acl2NativeFunction.execEqual(x, y);
        }

        public static Acl2Value if$(Acl2Value x, Acl2Value y, Acl2Value z) {
            return Acl2NativeFunction.execIf(x, y, z);
        }

        public static Acl2Value integerp(Acl2Value x) {
            return Acl2NativeFunction.execIntegerp(x);
        }

        public static Acl2Value less_than(Acl2Value x, Acl2Value y) {
            return Acl2NativeFunction.execLessThan(x, y);
        }

        public static Acl2Value not(Acl2Value p) {
            if (p != Acl2Symbol.NIL) {
                return NIL;
            } else {
                return T;
            }
        }

        public static Acl2Value stringp(Acl2Value x) {
            return Acl2NativeFunction.execStringp(x);
        }

        static final Acl2Symbol NIL = Acl2Symbol.NIL;

        static final Acl2Symbol T = Acl2Symbol.T;
    }

    public static class ACL2 {

        public static Acl2Value atom(Acl2Value x1) {
            return COMMON_LISP.atom(x1);
        }

        public static Acl2Value binary_plus(Acl2Value x, Acl2Value y) {
            return Acl2NativeFunction.execBinaryPlus(x, y);
        }

        public static Acl2Value car(Acl2Value x1) {
            return COMMON_LISP.car(x1);
        }

        public static Acl2Value cdr(Acl2Value x1) {
            return COMMON_LISP.cdr(x1);
        }

        public static Acl2Value char_code(Acl2Value x1) {
            return COMMON_LISP.char_code(x1);
        }

        public static Acl2Value char_fix$DOLLARinline(Acl2Value x) {
            if (characterp(x) != Acl2Symbol.NIL) {
                return x;
            } else {
                return code_char($N_0);
            }
        }

        public static Acl2Value characterp(Acl2Value x1) {
            return COMMON_LISP.characterp(x1);
        }

        public static Acl2Value code_char(Acl2Value x1) {
            return COMMON_LISP.code_char(x1);
        }

        public static Acl2Value cons(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.cons(x1, x2);
        }

        public static Acl2Value consp(Acl2Value x1) {
            return COMMON_LISP.consp(x1);
        }

        public static Acl2Value downcase$DOLLARinline(Acl2Value x) {
            Acl2Value code = char_code(x);
            Acl2Value $tmp1;
            if (not(less_than(code, $N_65)) != Acl2Symbol.NIL) {
                $tmp1 = not(less_than($N_90, code));
            } else {
                $tmp1 = Acl2Symbol.NIL;
            }
            if ($tmp1 != Acl2Symbol.NIL) {
                return code_char(binary_plus(code, $N_32));
            } else {
                return char_fix$DOLLARinline(x);
            }
        }

        public static Acl2Value eq(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.eq(x1, x2);
        }

        public static Acl2Value eql(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.eql(x1, x2);
        }

        public static Acl2Value equal(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.equal(x1, x2);
        }

        public static Acl2Value hide(Acl2Value x) {
            return x;
        }

        public static Acl2Value if$(Acl2Value x1, Acl2Value x2, Acl2Value x3) {
            return COMMON_LISP.if$(x1, x2, x3);
        }

        public static Acl2Value integerp(Acl2Value x1) {
            return COMMON_LISP.integerp(x1);
        }

        public static Acl2Value len(Acl2Value x) {
            return Acl2NativeFunction.execLen(x);
        }

        public static Acl2Value less_than(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.less_than(x1, x2);
        }

        public static Acl2Value mv_nth(Acl2Value n, Acl2Value l) {
            while (atom(l) == Acl2Symbol.NIL) {
                if (zp(n) != Acl2Symbol.NIL) {
                    return car(l);
                } else {
                    l = cdr(l);
                    n = binary_plus($N_minus1, n);
                }
            }
            return NIL;
        }

        public static Acl2Value nat_list_fix$DOLLARinline(Acl2Value x) {
            if (atom(x) != Acl2Symbol.NIL) {
                return NIL;
            } else {
                return cons(nfix(car(x)), nat_list_fix$DOLLARinline(cdr(x)));
            }
        }

        public static Acl2Value nat_match_insensitive_char_p(Acl2Value nat, Acl2Value char$1) {
            Acl2Value $tmp2 = equal(nat, char_code(char$1));
            if ($tmp2 == Acl2Symbol.NIL) {
                Acl2Value $tmp1 = equal(nat, char_code(upcase$DOLLARinline(char$1)));
                if ($tmp1 == Acl2Symbol.NIL) {
                    $tmp1 = equal(nat, char_code(downcase$DOLLARinline(char$1)));
                }
                $tmp2 = $tmp1;
            }
            return $tmp2;
        }

        public static Acl2Value nfix(Acl2Value x) {
            Acl2Value $tmp1;
            if (integerp(x) != Acl2Symbol.NIL) {
                $tmp1 = not(less_than(x, $N_0));
            } else {
                $tmp1 = Acl2Symbol.NIL;
            }
            if ($tmp1 != Acl2Symbol.NIL) {
                return x;
            } else {
                return $N_0;
            }
        }

        public static Acl2Value not(Acl2Value x1) {
            return COMMON_LISP.not(x1);
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$QMARK$PCENTi(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichars($C_$PCENT, $C_i, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, NIL), nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$QMARKrepeat(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_repeat(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, NIL), nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STAR_alpha$SLASHdigit$SLASHdash(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_alpha$SLASHdigit$SLASHdash(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STAR_alpha$SLASHdigit$SLASHdash(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STAR_dot_1$STARbit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_dot_1$STARbit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STAR_dot_1$STARbit(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STAR_dot_1$STARdigit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_dot_1$STARdigit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STAR_dot_1$STARdigit(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STAR_dot_1$STARhexdig(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_dot_1$STARhexdig(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STAR_dot_1$STARhexdig(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STAR_in_either_range(Acl2Value min1, Acl2Value max1, Acl2Value min2, Acl2Value max2, Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_in_either_range(min1, max1, min2, max2, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STAR_in_either_range(min1, max1, min2, max2, input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STAR_rule_$SLASH_$STARcwsp_cnl(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_rule_$SLASH_$STARcwsp_cnl(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STAR_rule_$SLASH_$STARcwsp_cnl(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STARbit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_bit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STARbit(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STARcwsp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_cwsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STARcwsp(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STARcwsp_cnl(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_$STARcwsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
            } else {
                mv = parse_cnl(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(trees, cons(cons(tree, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STARdigit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_digit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STARdigit(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STARdigit_star_$STARdigit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_$STARdigit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees1 = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees1, input);
            } else {
                mv = parse_ichar($C_$STAR, input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
                } else {
                    mv = parse_$STARdigit(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value trees2 = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees2, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(trees1, cons(cons(tree, NIL), cons(trees2, NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STARhexdig(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_hexdig(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STARhexdig(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_$STARwsp$SLASHvchar(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_wsp$SLASHvchar(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                mv = parse_$STARwsp$SLASHvchar(input$1);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$2);
                } else {
                    $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input$2);
                }
                $tmp2 = $tmp1;
            }
            mv = $tmp2;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_1$STAR_dot_1$STARbit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_dot_1$STARbit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STAR_dot_1$STARbit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_1$STAR_dot_1$STARdigit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_dot_1$STARdigit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STAR_dot_1$STARdigit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_1$STAR_dot_1$STARhexdig(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_dot_1$STARhexdig(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STAR_dot_1$STARhexdig(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_1$STARbit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_bit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STARbit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_1$STARcwsp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_cwsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STARcwsp(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_1$STARdigit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_digit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STARdigit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_1$STARhexdig(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_hexdig(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STARhexdig(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_alpha(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_in_range($N_65, $N_90, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_37, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_in_range($N_97, $N_122, input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_37, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_alpha$SLASHdigit$SLASHdash(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_alpha(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_digit(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                } else {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$2);
                }
                mv = $tmp2;
                $BANG$BANG$BANGerror = mv.$0;
                $BANG$BANG$BANGval = mv.$1;
                updated_stream = mv.$2;
                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                } else {
                    mv = parse_ichar($C_$DASH, input);
                    $BANG$BANG$BANGerror = mv.$0;
                    tree = mv.$1;
                    input$2 = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$2);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_alt_rest(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_alt_rest_comp(input);
            Acl2Value error$QMARK = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input1 = mv.$2;
            if (error$QMARK != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            } else {
                if (less_than(len(input1), len(input)) != Acl2Symbol.NIL) {
                    mv = parse_alt_rest(input1);
                    Acl2Value trees = mv.$1;
                    Acl2Value input2 = mv.$2;
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input2);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, NIL);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_alt_rest_comp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_$STARcwsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees1 = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees1, input);
            } else {
                mv = parse_ichar($C_$SLASH, input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree_slash = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_slash, input);
                } else {
                    mv = parse_$STARcwsp(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value trees2 = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees2, input);
                    } else {
                        mv = parse_concatenation(input);
                        $BANG$BANG$BANGerror = mv.$0;
                        Acl2Value tree_conc = mv.$1;
                        input = mv.$2;
                        if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_conc, input);
                        } else {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(trees1, cons(cons(tree_slash, NIL), cons(trees2, cons(cons(tree_conc, NIL), NIL))))), input);
                        }
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_alternation(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_concatenation(input);
            Acl2Value error$QMARK = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input1 = mv.$2;
            if (error$QMARK != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(error$QMARK, NIL, input1);
            } else {
                if (less_than(len(input1), len(input)) != Acl2Symbol.NIL) {
                    mv = parse_alt_rest(input1);
                    error$QMARK = mv.$0;
                    Acl2Value trees = mv.$1;
                    Acl2Value input2 = mv.$2;
                    if (error$QMARK != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(error$QMARK, NIL, input2);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_15, cons(cons(tree, NIL), cons(trees, NIL))), input2);
                    }
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($S_, NIL, NIL);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_any(Acl2Value input) {
            if (consp(input) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, car(input), cdr(input));
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($P_5, NIL, input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_bin$SLASHdec$SLASHhex_val(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_bin_val(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_dec_val(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                } else {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$2);
                }
                mv = $tmp2;
                $BANG$BANG$BANGerror = mv.$0;
                $BANG$BANG$BANGval = mv.$1;
                updated_stream = mv.$2;
                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                } else {
                    mv = parse_hex_val(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    tree = mv.$1;
                    input$2 = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$2);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_bin_val(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_b, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARbit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    mv = parse_bin_val_rest(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_rest = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_rest, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_25, cons(cons(tree, NIL), cons(trees, cons(cons(tree_rest, NIL), NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_bin_val_rest(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_1$STAR_dot_1$STARbit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(trees, NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_dash_1$STARbit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                } else {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$2);
                }
                mv = $tmp2;
                $BANG$BANG$BANGerror = mv.$0;
                $BANG$BANG$BANGval = mv.$1;
                updated_stream = mv.$2;
                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, NIL), nat_list_fix$DOLLARinline(input));
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_bit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_0, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_26, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_ichar($C_1, input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_26, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_case_insensitive_string(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_$QMARK$PCENTi(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_$PCENTi = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_$PCENTi, input);
            } else {
                mv = parse_quoted_string(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree_qstring = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_qstring, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_31, cons(cons(tree_$PCENTi, NIL), cons(cons(tree_qstring, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_case_sensitive_string(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichars($C_$PCENT, $C_s, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_$PCENTs = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_$PCENTs, input);
            } else {
                mv = parse_quoted_string(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree_qstring = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_qstring, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_28, cons(cons(tree_$PCENTs, NIL), cons(cons(tree_qstring, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_char_val(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_case_insensitive_string(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_27, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_case_sensitive_string(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_27, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_cnl(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_comment(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_2, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_crlf(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_2, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_cnl_wsp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_cnl(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_cnl = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_cnl, input);
            } else {
                mv = parse_wsp(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree_wsp = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_wsp, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree_cnl, NIL), cons(cons(tree_wsp, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_comment(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$SCOLON, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_semicolon = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_semicolon, input);
            } else {
                mv = parse_$STARwsp$SLASHvchar(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees_text = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees_text, input);
                } else {
                    mv = parse_crlf(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_crlf = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_crlf, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_7, cons(cons(tree_semicolon, NIL), cons(trees_text, cons(cons(tree_crlf, NIL), NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_conc_rest(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_conc_rest_comp(input);
            Acl2Value error$QMARK = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input1 = mv.$2;
            if (error$QMARK != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, nat_list_fix$DOLLARinline(input));
            } else {
                if (less_than(len(input1), len(input)) != Acl2Symbol.NIL) {
                    mv = parse_conc_rest(input1);
                    Acl2Value trees = mv.$1;
                    Acl2Value input2 = mv.$2;
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, cons(tree, trees), input2);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, NIL, NIL);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_conc_rest_comp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_1$STARcwsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
            } else {
                mv = parse_repetition(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(trees, cons(cons(tree, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_concatenation(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_repetition(input);
            Acl2Value error$QMARK = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input1 = mv.$2;
            if (error$QMARK != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(error$QMARK, NIL, input1);
            } else {
                if (less_than(len(input1), len(input)) != Acl2Symbol.NIL) {
                    mv = parse_conc_rest(input1);
                    error$QMARK = mv.$0;
                    Acl2Value trees = mv.$1;
                    Acl2Value input2 = mv.$2;
                    if (error$QMARK != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(error$QMARK, NIL, input2);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_16, cons(cons(tree, NIL), cons(trees, NIL))), input2);
                    }
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($S_, NIL, NIL);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_cr(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_exact($N_13, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_6, cons(cons(tree, NIL), NIL)), input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_crlf(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_cr(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_cr = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_cr, input);
            } else {
                mv = parse_lf(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree_lf = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_lf, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_3, cons(cons(tree_cr, NIL), cons(cons(tree_lf, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_cwsp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_wsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_12, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_cnl_wsp(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_12, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dash_1$STARbit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$DASH, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARbit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dash_1$STARdigit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$DASH, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARdigit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dash_1$STARhexdig(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$DASH, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARhexdig(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dec_val(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_d, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARdigit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    mv = parse_dec_val_rest(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_rest = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_rest, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_24, cons(cons(tree, NIL), cons(trees, cons(cons(tree_rest, NIL), NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dec_val_rest(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_1$STAR_dot_1$STARdigit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(trees, NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_dash_1$STARdigit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                } else {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$2);
                }
                mv = $tmp2;
                $BANG$BANG$BANGerror = mv.$0;
                $BANG$BANG$BANGval = mv.$1;
                updated_stream = mv.$2;
                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, NIL), nat_list_fix$DOLLARinline(input));
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_defined_as(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_$STARcwsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees1 = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees1, input);
            } else {
                mv = parse_equal_$SLASH_equal_slash(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
                } else {
                    mv = parse_$STARcwsp(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value trees2 = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees2, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_35, cons(trees1, cons(cons(tree, NIL), cons(trees2, NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_digit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_in_range($N_48, $N_57, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_23, cons(cons(tree, NIL), NIL)), input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dot_1$STARbit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$DOT, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARbit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dot_1$STARdigit(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$DOT, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARdigit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dot_1$STARhexdig(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$DOT, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARhexdig(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_dquote(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_exact($N_34, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_30, cons(cons(tree, NIL), NIL)), input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_element(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_rulename(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_18, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_group(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                } else {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_18, cons(cons(tree, NIL), NIL)), input$2);
                }
                mv = $tmp2;
                $BANG$BANG$BANGerror = mv.$0;
                $BANG$BANG$BANGval = mv.$1;
                updated_stream = mv.$2;
                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                } else {
                    mv = parse_option(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    tree = mv.$1;
                    Acl2Value input$3 = mv.$2;
                    MV_Acl2Value_Acl2Value_Acl2Value $tmp3;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        $tmp3 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$3);
                    } else {
                        $tmp3 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_18, cons(cons(tree, NIL), NIL)), input$3);
                    }
                    mv = $tmp3;
                    $BANG$BANG$BANGerror = mv.$0;
                    $BANG$BANG$BANGval = mv.$1;
                    updated_stream = mv.$2;
                    if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                    } else {
                        mv = parse_char_val(input);
                        $BANG$BANG$BANGerror = mv.$0;
                        tree = mv.$1;
                        Acl2Value input$4 = mv.$2;
                        MV_Acl2Value_Acl2Value_Acl2Value $tmp4;
                        if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                            $tmp4 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$4);
                        } else {
                            $tmp4 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_18, cons(cons(tree, NIL), NIL)), input$4);
                        }
                        mv = $tmp4;
                        $BANG$BANG$BANGerror = mv.$0;
                        $BANG$BANG$BANGval = mv.$1;
                        updated_stream = mv.$2;
                        if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                        } else {
                            mv = parse_num_val(input);
                            $BANG$BANG$BANGerror = mv.$0;
                            tree = mv.$1;
                            Acl2Value input$5 = mv.$2;
                            MV_Acl2Value_Acl2Value_Acl2Value $tmp5;
                            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                                $tmp5 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$5);
                            } else {
                                $tmp5 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_18, cons(cons(tree, NIL), NIL)), input$5);
                            }
                            mv = $tmp5;
                            $BANG$BANG$BANGerror = mv.$0;
                            $BANG$BANG$BANGval = mv.$1;
                            updated_stream = mv.$2;
                            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                            } else {
                                mv = parse_prose_val(input);
                                $BANG$BANG$BANGerror = mv.$0;
                                tree = mv.$1;
                                input$5 = mv.$2;
                                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$5);
                                } else {
                                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_18, cons(cons(tree, NIL), NIL)), input$5);
                                }
                            }
                        }
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_elements(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_alternation(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STARcwsp(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_14, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_equal_$SLASH_equal_slash(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichars($C_$EQ, $C_$SLASH, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_ichar($C_$EQ, input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_exact(Acl2Value nat, Acl2Value input) {
            nat = nfix(nat);
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_any(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value input_nat = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, input_nat, input);
            } else {
                if (not(eql(input_nat, nat)) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($P_5, NIL, cons(input_nat, input));
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_leafterm(cons(nat, NIL)), input);
                }
            }
        }

        public static Acl2Value parse_grammar(Acl2Value nats) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_rulelist(nats);
            Acl2Value error$QMARK = mv.$0;
            Acl2Value tree$QMARK = mv.$1;
            Acl2Value rest = mv.$2;
            if (error$QMARK != Acl2Symbol.NIL) {
                return NIL;
            } else {
                if (rest != Acl2Symbol.NIL) {
                    return NIL;
                } else {
                    return tree$QMARK;
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_group(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$OROUND, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_open_round = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_open_round, input);
            } else {
                mv = parse_$STARcwsp(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees_open_pad = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees_open_pad, input);
                } else {
                    mv = parse_alternation(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_alt = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_alt, input);
                    } else {
                        mv = parse_$STARcwsp(input);
                        $BANG$BANG$BANGerror = mv.$0;
                        Acl2Value trees_close_pad = mv.$1;
                        input = mv.$2;
                        if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees_close_pad, input);
                        } else {
                            mv = parse_ichar($C_$CROUND, input);
                            $BANG$BANG$BANGerror = mv.$0;
                            Acl2Value tree_close_round = mv.$1;
                            input = mv.$2;
                            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_close_round, input);
                            } else {
                                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_33, cons(cons(tree_open_round, NIL), cons(trees_open_pad, cons(cons(tree_alt, NIL), cons(trees_close_pad, cons(cons(tree_close_round, NIL), NIL)))))), input);
                            }
                        }
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_hex_val(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_x, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_1$STARhexdig(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    mv = parse_hex_val_rest(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_rest = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_rest, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_21, cons(cons(tree, NIL), cons(trees, cons(cons(tree_rest, NIL), NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_hex_val_rest(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_1$STAR_dot_1$STARhexdig(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value trees = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(trees, NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_dash_1$STARhexdig(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                } else {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$2);
                }
                mv = $tmp2;
                $BANG$BANG$BANGerror = mv.$0;
                $BANG$BANG$BANGval = mv.$1;
                updated_stream = mv.$2;
                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, NIL), nat_list_fix$DOLLARinline(input));
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_hexdig(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_digit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_22, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_ichar($C_A, input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                Acl2Value input$2 = mv.$2;
                MV_Acl2Value_Acl2Value_Acl2Value $tmp2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$2);
                } else {
                    $tmp2 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_22, cons(cons(tree, NIL), NIL)), input$2);
                }
                mv = $tmp2;
                $BANG$BANG$BANGerror = mv.$0;
                $BANG$BANG$BANGval = mv.$1;
                updated_stream = mv.$2;
                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                } else {
                    mv = parse_ichar($C_B, input);
                    $BANG$BANG$BANGerror = mv.$0;
                    tree = mv.$1;
                    Acl2Value input$3 = mv.$2;
                    MV_Acl2Value_Acl2Value_Acl2Value $tmp3;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        $tmp3 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$3);
                    } else {
                        $tmp3 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_22, cons(cons(tree, NIL), NIL)), input$3);
                    }
                    mv = $tmp3;
                    $BANG$BANG$BANGerror = mv.$0;
                    $BANG$BANG$BANGval = mv.$1;
                    updated_stream = mv.$2;
                    if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                    } else {
                        mv = parse_ichar($C_C, input);
                        $BANG$BANG$BANGerror = mv.$0;
                        tree = mv.$1;
                        Acl2Value input$4 = mv.$2;
                        MV_Acl2Value_Acl2Value_Acl2Value $tmp4;
                        if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                            $tmp4 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$4);
                        } else {
                            $tmp4 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_22, cons(cons(tree, NIL), NIL)), input$4);
                        }
                        mv = $tmp4;
                        $BANG$BANG$BANGerror = mv.$0;
                        $BANG$BANG$BANGval = mv.$1;
                        updated_stream = mv.$2;
                        if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                        } else {
                            mv = parse_ichar($C_D, input);
                            $BANG$BANG$BANGerror = mv.$0;
                            tree = mv.$1;
                            Acl2Value input$5 = mv.$2;
                            MV_Acl2Value_Acl2Value_Acl2Value $tmp5;
                            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                                $tmp5 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$5);
                            } else {
                                $tmp5 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_22, cons(cons(tree, NIL), NIL)), input$5);
                            }
                            mv = $tmp5;
                            $BANG$BANG$BANGerror = mv.$0;
                            $BANG$BANG$BANGval = mv.$1;
                            updated_stream = mv.$2;
                            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                            } else {
                                mv = parse_ichar($C_E, input);
                                $BANG$BANG$BANGerror = mv.$0;
                                tree = mv.$1;
                                Acl2Value input$6 = mv.$2;
                                MV_Acl2Value_Acl2Value_Acl2Value $tmp6;
                                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                                    $tmp6 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$6);
                                } else {
                                    $tmp6 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_22, cons(cons(tree, NIL), NIL)), input$6);
                                }
                                mv = $tmp6;
                                $BANG$BANG$BANGerror = mv.$0;
                                $BANG$BANG$BANGval = mv.$1;
                                updated_stream = mv.$2;
                                if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
                                } else {
                                    mv = parse_ichar($C_F, input);
                                    $BANG$BANG$BANGerror = mv.$0;
                                    tree = mv.$1;
                                    input$6 = mv.$2;
                                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$6);
                                    } else {
                                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_22, cons(cons(tree, NIL), NIL)), input$6);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_htab(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_exact($N_9, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_10, cons(cons(tree, NIL), NIL)), input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_ichar(Acl2Value char$1, Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_any(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value nat = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, nat, input);
            } else {
                if (not(nat_match_insensitive_char_p(nat, char$1)) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($P_5, NIL, cons(nat, input));
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_leafterm(cons(nat, NIL)), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_ichars(Acl2Value char1, Acl2Value char2, Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_any(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value nat1 = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, nat1, input);
            } else {
                if (not(nat_match_insensitive_char_p(nat1, char1)) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($P_5, NIL, cons(nat1, input));
                } else {
                    mv = parse_any(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value nat2 = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, nat2, input);
                    } else {
                        if (not(nat_match_insensitive_char_p(nat2, char2)) != Acl2Symbol.NIL) {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make($P_5, NIL, cons(nat2, input));
                        } else {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_leafterm(cons(nat1, cons(nat2, NIL))), input);
                        }
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_in_either_range(Acl2Value min1, Acl2Value max1, Acl2Value min2, Acl2Value max2, Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_in_range(min1, max1, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_in_range(min2, max2, input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_in_range(Acl2Value min, Acl2Value max, Acl2Value input) {
            min = nfix(min);
            max = nfix(max);
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_any(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value nat = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, nat, input);
            } else {
                Acl2Value $tmp1;
                if (not(less_than(nat, min)) != Acl2Symbol.NIL) {
                    $tmp1 = not(less_than(max, nat));
                } else {
                    $tmp1 = Acl2Symbol.NIL;
                }
                if (not($tmp1) != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($P_5, NIL, cons(nat, input));
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_leafterm(cons(nat, NIL)), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_lf(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_exact($N_10, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_4, cons(cons(tree, NIL), NIL)), input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_num_val(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$PCENT, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_$PCENT = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_$PCENT, input);
            } else {
                mv = parse_bin$SLASHdec$SLASHhex_val(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree_val = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_val, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_20, cons(cons(tree_$PCENT, NIL), cons(cons(tree_val, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_option(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$OSQUARE, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_open_square = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_open_square, input);
            } else {
                mv = parse_$STARcwsp(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees_open_pad = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees_open_pad, input);
                } else {
                    mv = parse_alternation(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_alt = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_alt, input);
                    } else {
                        mv = parse_$STARcwsp(input);
                        $BANG$BANG$BANGerror = mv.$0;
                        Acl2Value trees_close_pad = mv.$1;
                        input = mv.$2;
                        if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees_close_pad, input);
                        } else {
                            mv = parse_ichar($C_$CSQUARE, input);
                            $BANG$BANG$BANGerror = mv.$0;
                            Acl2Value tree_close_square = mv.$1;
                            input = mv.$2;
                            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_close_square, input);
                            } else {
                                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_32, cons(cons(tree_open_square, NIL), cons(trees_open_pad, cons(cons(tree_alt, NIL), cons(trees_close_pad, cons(cons(tree_close_square, NIL), NIL)))))), input);
                            }
                        }
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_prose_val(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_ichar($C_$LT, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_open_angle = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_open_angle, input);
            } else {
                mv = parse_$STAR_in_either_range($N_32, $N_61, $N_63, $N_126, input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees_text = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees_text, input);
                } else {
                    mv = parse_ichar($C_$GT, input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_close_angle = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_close_angle, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_19, cons(cons(tree_open_angle, NIL), cons(trees_text, cons(cons(tree_close_angle, NIL), NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_quoted_string(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_dquote(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_open_quote = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_open_quote, input);
            } else {
                mv = parse_$STAR_in_either_range($N_32, $N_33, $N_35, $N_126, input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    mv = parse_dquote(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree_close_quote = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_close_quote, input);
                    } else {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_29, cons(cons(tree_open_quote, NIL), cons(trees, cons(cons(tree_close_quote, NIL), NIL)))), input);
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_repeat(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_$STARdigit_star_$STARdigit(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_34, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_1$STARdigit(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_34, cons(trees, NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_repetition(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_$QMARKrepeat(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree_repeat = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_repeat, input);
            } else {
                mv = parse_element(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree_element = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree_element, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_17, cons(cons(tree_repeat, NIL), cons(cons(tree_element, NIL), NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_rule(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_rulename(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree1 = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree1, input);
            } else {
                mv = parse_defined_as(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value tree2 = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree2, input);
                } else {
                    mv = parse_elements(input);
                    $BANG$BANG$BANGerror = mv.$0;
                    Acl2Value tree3 = mv.$1;
                    input = mv.$2;
                    if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                        return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree3, input);
                    } else {
                        mv = parse_cnl(input);
                        $BANG$BANG$BANGerror = mv.$0;
                        Acl2Value tree4 = mv.$1;
                        input = mv.$2;
                        if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree4, input);
                        } else {
                            return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_13, cons(cons(tree1, NIL), cons(cons(tree2, NIL), cons(cons(tree3, NIL), cons(cons(tree4, NIL), NIL))))), input);
                        }
                    }
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_rule_$SLASH_$STARcwsp_cnl(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_rule(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_$STARcwsp_cnl(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_rulelist(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_rule_$SLASH_$STARcwsp_cnl(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STAR_rule_$SLASH_$STARcwsp_cnl(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_1, cons(cons(tree, trees), NIL)), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_rulename(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_alpha(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                mv = parse_$STAR_alpha$SLASHdigit$SLASHdash(input);
                $BANG$BANG$BANGerror = mv.$0;
                Acl2Value trees = mv.$1;
                input = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, trees, input);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_36, cons(cons(tree, NIL), cons(trees, NIL))), input);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_sp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_exact($N_32, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_11, cons(cons(tree, NIL), NIL)), input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_vchar(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_in_range($N_33, $N_126, input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            input = mv.$2;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input);
            } else {
                return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_8, cons(cons(tree, NIL), NIL)), input);
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_wsp(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_sp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_9, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_htab(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf($P_9, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static MV_Acl2Value_Acl2Value_Acl2Value parse_wsp$SLASHvchar(Acl2Value input) {
            MV_Acl2Value_Acl2Value_Acl2Value mv = parse_wsp(input);
            Acl2Value $BANG$BANG$BANGerror = mv.$0;
            Acl2Value tree = mv.$1;
            Acl2Value input$1 = mv.$2;
            MV_Acl2Value_Acl2Value_Acl2Value $tmp1;
            if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
            } else {
                $tmp1 = MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
            }
            mv = $tmp1;
            $BANG$BANG$BANGerror = mv.$0;
            Acl2Value $BANG$BANG$BANGval = mv.$1;
            Acl2Value updated_stream = mv.$2;
            if (not($BANG$BANG$BANGerror) != Acl2Symbol.NIL) {
                return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, $BANG$BANG$BANGval, updated_stream);
            } else {
                mv = parse_vchar(input);
                $BANG$BANG$BANGerror = mv.$0;
                tree = mv.$1;
                input$1 = mv.$2;
                if ($BANG$BANG$BANGerror != Acl2Symbol.NIL) {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make($BANG$BANG$BANGerror, tree, input$1);
                } else {
                    return MV_Acl2Value_Acl2Value_Acl2Value.make(NIL, ABNF.tree_nonleaf(NIL, cons(cons(tree, NIL), NIL)), input$1);
                }
            }
        }

        public static Acl2Value str_fix$DOLLARinline(Acl2Value x) {
            if (stringp(x) != Acl2Symbol.NIL) {
                return x;
            } else {
                return $S_;
            }
        }

        public static Acl2Value stringp(Acl2Value x1) {
            return COMMON_LISP.stringp(x1);
        }

        public static Acl2Value unary_minus(Acl2Value x) {
            return Acl2NativeFunction.execUnaryMinus(x);
        }

        public static Acl2Value upcase$DOLLARinline(Acl2Value x) {
            Acl2Value code = char_code(x);
            Acl2Value $tmp1;
            if (not(less_than(code, $N_97)) != Acl2Symbol.NIL) {
                $tmp1 = not(less_than($N_122, code));
            } else {
                $tmp1 = Acl2Symbol.NIL;
            }
            if ($tmp1 != Acl2Symbol.NIL) {
                return code_char(binary_plus(code, unary_minus($N_32)));
            } else {
                return char_fix$DOLLARinline(x);
            }
        }

        public static Acl2Value zp(Acl2Value x) {
            if (integerp(x) != Acl2Symbol.NIL) {
                return not(less_than($N_0, x));
            } else {
                return T;
            }
        }

        static final Acl2Symbol NIL = Acl2Symbol.NIL;

        static final Acl2Symbol T = Acl2Symbol.T;
    }

    public static class ABNF {

        public static Acl2Value atom(Acl2Value x1) {
            return COMMON_LISP.atom(x1);
        }

        public static Acl2Value binary_plus(Acl2Value x1, Acl2Value x2) {
            return ACL2.binary_plus(x1, x2);
        }

        public static Acl2Value car(Acl2Value x1) {
            return COMMON_LISP.car(x1);
        }

        public static Acl2Value cdr(Acl2Value x1) {
            return COMMON_LISP.cdr(x1);
        }

        public static Acl2Value char_code(Acl2Value x1) {
            return COMMON_LISP.char_code(x1);
        }

        public static Acl2Value characterp(Acl2Value x1) {
            return COMMON_LISP.characterp(x1);
        }

        public static Acl2Value code_char(Acl2Value x1) {
            return COMMON_LISP.code_char(x1);
        }

        public static Acl2Value cons(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.cons(x1, x2);
        }

        public static Acl2Value consp(Acl2Value x1) {
            return COMMON_LISP.consp(x1);
        }

        public static Acl2Value eq(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.eq(x1, x2);
        }

        public static Acl2Value eql(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.eql(x1, x2);
        }

        public static Acl2Value equal(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.equal(x1, x2);
        }

        public static Acl2Value hide(Acl2Value x1) {
            return ACL2.hide(x1);
        }

        public static Acl2Value if$(Acl2Value x1, Acl2Value x2, Acl2Value x3) {
            return COMMON_LISP.if$(x1, x2, x3);
        }

        public static Acl2Value integerp(Acl2Value x1) {
            return COMMON_LISP.integerp(x1);
        }

        public static Acl2Value len(Acl2Value x1) {
            return ACL2.len(x1);
        }

        public static Acl2Value less_than(Acl2Value x1, Acl2Value x2) {
            return COMMON_LISP.less_than(x1, x2);
        }

        public static Acl2Value maybe_rulename_fix$DOLLARinline(Acl2Value x) {
            if (not(x) != Acl2Symbol.NIL) {
                return NIL;
            } else {
                Acl2Value val = rulename_fix$DOLLARinline(x);
                return val;
            }
        }

        public static Acl2Value mv_nth(Acl2Value x1, Acl2Value x2) {
            return ACL2.mv_nth(x1, x2);
        }

        public static Acl2Value nfix(Acl2Value x1) {
            return ACL2.nfix(x1);
        }

        public static Acl2Value not(Acl2Value x1) {
            return COMMON_LISP.not(x1);
        }

        public static Acl2Value rulename_fix$DOLLARinline(Acl2Value x) {
            Acl2Value get = ACL2.str_fix$DOLLARinline(car(cdr(x)));
            return cons(KEYWORD.$Q_RULENAME, cons(get, NIL));
        }

        public static Acl2Value tree_fix$DOLLARinline(Acl2Value x) {
            Acl2Value case_do_not_use_elsewhere = tree_kind$DOLLARinline(x);
            if (eql(case_do_not_use_elsewhere, KEYWORD.$Q_LEAFTERM) != Acl2Symbol.NIL) {
                Acl2Value get = ACL2.nat_list_fix$DOLLARinline(car(cdr(x)));
                return cons(KEYWORD.$Q_LEAFTERM, cons(get, NIL));
            } else {
                if (eql(case_do_not_use_elsewhere, KEYWORD.$Q_LEAFRULE) != Acl2Symbol.NIL) {
                    Acl2Value get = rulename_fix$DOLLARinline(car(cdr(x)));
                    return cons(KEYWORD.$Q_LEAFRULE, cons(get, NIL));
                } else {
                    if (eql(case_do_not_use_elsewhere, KEYWORD.$Q_NONLEAF) != Acl2Symbol.NIL) {
                        Acl2Value rulename$QMARK = maybe_rulename_fix$DOLLARinline(car(cdr(x)));
                        Acl2Value branches = tree_list_list_fix$DOLLARinline(car(cdr(cdr(x))));
                        return cons(KEYWORD.$Q_NONLEAF, cons(rulename$QMARK, cons(branches, NIL)));
                    } else {
                        return Acl2Symbol.NIL;
                    }
                }
            }
        }

        public static Acl2Value tree_kind$DOLLARinline(Acl2Value x) {
            Acl2Value $tmp1 = atom(x);
            if ($tmp1 == Acl2Symbol.NIL) {
                $tmp1 = eq(car(x), KEYWORD.$Q_LEAFTERM);
            }
            if ($tmp1 != Acl2Symbol.NIL) {
                return KEYWORD.$Q_LEAFTERM;
            } else {
                if (eq(car(x), KEYWORD.$Q_LEAFRULE) != Acl2Symbol.NIL) {
                    return KEYWORD.$Q_LEAFRULE;
                } else {
                    return KEYWORD.$Q_NONLEAF;
                }
            }
        }

        public static Acl2Value tree_leafterm(Acl2Value get) {
            get = ACL2.nat_list_fix$DOLLARinline(get);
            return cons(KEYWORD.$Q_LEAFTERM, cons(get, NIL));
        }

        public static Acl2Value tree_list_fix$DOLLARinline(Acl2Value x) {
            if (atom(x) != Acl2Symbol.NIL) {
                return NIL;
            } else {
                return cons(tree_fix$DOLLARinline(car(x)), tree_list_fix$DOLLARinline(cdr(x)));
            }
        }

        public static Acl2Value tree_list_list_fix$DOLLARinline(Acl2Value x) {
            if (atom(x) != Acl2Symbol.NIL) {
                return NIL;
            } else {
                return cons(tree_list_fix$DOLLARinline(car(x)), tree_list_list_fix$DOLLARinline(cdr(x)));
            }
        }

        public static Acl2Value tree_nonleaf(Acl2Value rulename$QMARK, Acl2Value branches) {
            rulename$QMARK = maybe_rulename_fix$DOLLARinline(rulename$QMARK);
            branches = tree_list_list_fix$DOLLARinline(branches);
            return cons(KEYWORD.$Q_NONLEAF, cons(rulename$QMARK, cons(branches, NIL)));
        }

        public static Acl2Value unary_minus(Acl2Value x1) {
            return ACL2.unary_minus(x1);
        }

        public static Acl2Value zp(Acl2Value x1) {
            return ACL2.zp(x1);
        }

        static final Acl2Symbol NIL = Acl2Symbol.NIL;

        static final Acl2Symbol T = Acl2Symbol.T;
    }

    private static final Acl2Character $C_$CROUND = Acl2Character.make(')');

    private static final Acl2Character $C_$CSQUARE = Acl2Character.make(']');

    private static final Acl2Character $C_$DASH = Acl2Character.make('-');

    private static final Acl2Character $C_$DOT = Acl2Character.make('.');

    private static final Acl2Character $C_$EQ = Acl2Character.make('=');

    private static final Acl2Character $C_$GT = Acl2Character.make('>');

    private static final Acl2Character $C_$LT = Acl2Character.make('<');

    private static final Acl2Character $C_$OROUND = Acl2Character.make('(');

    private static final Acl2Character $C_$OSQUARE = Acl2Character.make('[');

    private static final Acl2Character $C_$PCENT = Acl2Character.make('%');

    private static final Acl2Character $C_$SCOLON = Acl2Character.make(';');

    private static final Acl2Character $C_$SLASH = Acl2Character.make('/');

    private static final Acl2Character $C_$STAR = Acl2Character.make('*');

    private static final Acl2Character $C_0 = Acl2Character.make('0');

    private static final Acl2Character $C_1 = Acl2Character.make('1');

    private static final Acl2Character $C_A = Acl2Character.make('A');

    private static final Acl2Character $C_B = Acl2Character.make('B');

    private static final Acl2Character $C_C = Acl2Character.make('C');

    private static final Acl2Character $C_D = Acl2Character.make('D');

    private static final Acl2Character $C_E = Acl2Character.make('E');

    private static final Acl2Character $C_F = Acl2Character.make('F');

    private static final Acl2Character $C_b = Acl2Character.make('b');

    private static final Acl2Character $C_d = Acl2Character.make('d');

    private static final Acl2Character $C_i = Acl2Character.make('i');

    private static final Acl2Character $C_s = Acl2Character.make('s');

    private static final Acl2Character $C_x = Acl2Character.make('x');

    private static final Acl2Integer $N_0 = Acl2Integer.make(0);

    private static final Acl2Integer $N_1 = Acl2Integer.make(1);

    private static final Acl2Integer $N_10 = Acl2Integer.make(10);

    private static final Acl2Integer $N_122 = Acl2Integer.make(122);

    private static final Acl2Integer $N_126 = Acl2Integer.make(126);

    private static final Acl2Integer $N_13 = Acl2Integer.make(13);

    private static final Acl2Integer $N_2 = Acl2Integer.make(2);

    private static final Acl2Integer $N_32 = Acl2Integer.make(32);

    private static final Acl2Integer $N_33 = Acl2Integer.make(33);

    private static final Acl2Integer $N_34 = Acl2Integer.make(34);

    private static final Acl2Integer $N_35 = Acl2Integer.make(35);

    private static final Acl2Integer $N_48 = Acl2Integer.make(48);

    private static final Acl2Integer $N_57 = Acl2Integer.make(57);

    private static final Acl2Integer $N_61 = Acl2Integer.make(61);

    private static final Acl2Integer $N_63 = Acl2Integer.make(63);

    private static final Acl2Integer $N_65 = Acl2Integer.make(65);

    private static final Acl2Integer $N_9 = Acl2Integer.make(9);

    private static final Acl2Integer $N_90 = Acl2Integer.make(90);

    private static final Acl2Integer $N_97 = Acl2Integer.make(97);

    private static final Acl2Integer $N_minus1 = Acl2Integer.make(-1);

    private static final Acl2ConsPair $P_1 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("rulelist"));

    private static final Acl2ConsPair $P_10 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("htab"));

    private static final Acl2ConsPair $P_11 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("sp"));

    private static final Acl2ConsPair $P_12 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("c-wsp"));

    private static final Acl2ConsPair $P_13 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("rule"));

    private static final Acl2ConsPair $P_14 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("elements"));

    private static final Acl2ConsPair $P_15 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("alternation"));

    private static final Acl2ConsPair $P_16 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("concatenation"));

    private static final Acl2ConsPair $P_17 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("repetition"));

    private static final Acl2ConsPair $P_18 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("element"));

    private static final Acl2ConsPair $P_19 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("prose-val"));

    private static final Acl2ConsPair $P_2 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("c-nl"));

    private static final Acl2ConsPair $P_20 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("num-val"));

    private static final Acl2ConsPair $P_21 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("hex-val"));

    private static final Acl2ConsPair $P_22 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("hexdig"));

    private static final Acl2ConsPair $P_23 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("digit"));

    private static final Acl2ConsPair $P_24 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("dec-val"));

    private static final Acl2ConsPair $P_25 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("bin-val"));

    private static final Acl2ConsPair $P_26 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("bit"));

    private static final Acl2ConsPair $P_27 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("char-val"));

    private static final Acl2ConsPair $P_28 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("case-sensitive-string"));

    private static final Acl2ConsPair $P_29 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("quoted-string"));

    private static final Acl2ConsPair $P_3 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("crlf"));

    private static final Acl2ConsPair $P_30 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("dquote"));

    private static final Acl2ConsPair $P_31 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("case-insensitive-string"));

    private static final Acl2ConsPair $P_32 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("option"));

    private static final Acl2ConsPair $P_33 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("group"));

    private static final Acl2ConsPair $P_34 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("repeat"));

    private static final Acl2ConsPair $P_35 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("defined-as"));

    private static final Acl2ConsPair $P_36 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("rulename"));

    private static final Acl2ConsPair $P_37 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("alpha"));

    private static final Acl2ConsPair $P_4 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("lf"));

    private static final Acl2ConsPair $P_5 = (Acl2ConsPair) Acl2Value.makeList(Acl2String.make("ABNF Grammar Parser Error."));

    private static final Acl2ConsPair $P_6 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("cr"));

    private static final Acl2ConsPair $P_7 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("comment"));

    private static final Acl2ConsPair $P_8 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("vchar"));

    private static final Acl2ConsPair $P_9 = (Acl2ConsPair) Acl2Value.makeList(Acl2Symbol.make("KEYWORD", "RULENAME"), Acl2String.make("wsp"));

    private static final Acl2String $S_ = Acl2String.make("");

    public static final class MV_boolean_Acl2Value_Acl2Value {

        public boolean $0;

        public Acl2Value $1;

        public Acl2Value $2;

        private static final MV_boolean_Acl2Value_Acl2Value singleton = new MV_boolean_Acl2Value_Acl2Value();

        static MV_boolean_Acl2Value_Acl2Value make(boolean $0, Acl2Value $1, Acl2Value $2) {
            singleton.$0 = $0;
            singleton.$1 = $1;
            singleton.$2 = $2;
            return singleton;
        }
    }

    public static final class MV_Acl2Value_Acl2Value_Acl2Value {

        public Acl2Value $0;

        public Acl2Value $1;

        public Acl2Value $2;

        private static final MV_Acl2Value_Acl2Value_Acl2Value singleton = new MV_Acl2Value_Acl2Value_Acl2Value();

        static MV_Acl2Value_Acl2Value_Acl2Value make(Acl2Value $0, Acl2Value $1, Acl2Value $2) {
            singleton.$0 = $0;
            singleton.$1 = $1;
            singleton.$2 = $2;
            return singleton;
        }
    }
}
