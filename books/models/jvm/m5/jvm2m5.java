
/**
 * Converter from JVM class files to JVM M5 model.
 *
 * @author George M. Porter
 * @author J Strother Moore
 * @author Hanbing Liu
 * @author Dmitry Nadezhin
 */
// java jvm2m5 <output-dir> <.class files> <directories>
// it generates separate files for each .class file.
//
// Example:
// > cd models/jvm/m5
// > javac -cp $JAVA_HOME/lib/tools.jar:. *.java
// > java -cp $JAVA_HOME/lib/tools.jar:. jvm2m5 classes .
//
import com.sun.tools.classfile.AccessFlags;
import com.sun.tools.classfile.Attribute;
import com.sun.tools.classfile.ClassFile;
import com.sun.tools.classfile.Code_attribute;
import com.sun.tools.classfile.ConstantPool;
import com.sun.tools.classfile.ConstantPoolException;
import com.sun.tools.classfile.Field;
import com.sun.tools.classfile.Instruction;
import com.sun.tools.classfile.LineNumberTable_attribute;
import com.sun.tools.classfile.Method;
import java.io.File;
import java.io.FileWriter;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class jvm2m5 implements
        Instruction.KindVisitor<ConstantPool.CPInfo, Void>,
        ConstantPool.Visitor<Void, Boolean> {

    private static final String usage
            = "Usage: jvm2m5 <output directory> <file names>* [<directory names>*]\n";

    public static void main(String[] args) {

        System.err.println("JVM --> M5  An automatic M5 state generator.");
        if (args.length <= 1) {
            System.err.println(usage);
            System.exit(0);
        }

        String outputPath = args[0];
        String[] collectedFiles = collectFileNames(Arrays.copyOfRange(args, 1, args.length));
        for (String fn : collectedFiles) {
            try {
                processOneFile(fn, outputPath);
            } catch (java.lang.Exception e) {
                System.err.println("Could not open file " + fn + " " + e);
                System.exit(0);
            }
        }
    }

    private static String[] collectFileNames(String[] args) {
        List<String> files = new ArrayList<>();
        try {
            for (int i = 0; i < args.length; i++) {
                File cur = new File(args[i]);
                if (cur.isDirectory()) {
                    String[] nextlevel = cur.list();
                    Arrays.sort(nextlevel);
                    for (int j = 0; j < nextlevel.length; j++) {
                        nextlevel[j] = (cur.getPath() + "/" + nextlevel[j]);
                    }
                    String[] names = collectFileNames(nextlevel);
                    for (int j = 0; j < names.length; j++) {
                        files.add(names[j]);
                    }
                } else {
                    String curn = cur.getPath();
                    int e = curn.lastIndexOf('.');
                    if (e != -1) {
                        String suffix = curn.substring(e + 1);
                        if (suffix.equals("class")) {
                            files.add(curn);
                        }
                    }
                }
            }
        } catch (Exception e) {
            System.out.println("File reading error!");
        }
        return files.toArray(new String[files.size()]);
    }

    private static void processOneFile(String classfn, String pathn) {
        try {
            ClassFile cf = ClassFile.read(Paths.get(classfn));
            String classname = cf.getName().replace('/', '.');
            jvm2m5 printVisitor = new jvm2m5(cf);
            String fn = pathn + "/" + classname + ".lisp";
            System.out.println("Writing " + fn);
            FileWriter outfile = new FileWriter(fn);
            printVisitor.printClass();
            assert printVisitor.indent == 0;
            outfile.write(printVisitor.sb.toString());
            outfile.close();
        } catch (Exception e) {
            System.err.println(e);
            e.printStackTrace();
            System.exit(-1);
        }
    }

    final ClassFile cf;
    final ConstantPool cp;
    final StringBuilder sb = new StringBuilder();

    jvm2m5(ClassFile cf) throws ConstantPoolException {
        this.cf = cf;
        cp = cf.constant_pool;
    }

    int indent;
    int mark;
    private static final int CP_TAB = 56;
    private static final int CODE_TAB = 56;

    void indent(int delta) {
        indent += delta;
    }

    Void nl(String s) {
        sb.append('\n');
        for (int i = 0; i < indent; i++) {
            sb.append(' ');
        }
        mark = sb.length();
        sb.append(s);
        return null;
    }

    void comment(int pos, int num) {
        while (pos <= sb.length() - mark) {
            pos += 8;
        }
        int bc = mark + pos - sb.length();
        for (int j = 0; j < bc; j++) {
            sb.append(' ');
        }
        sb.append("; ").append(num);
    }

    //at the first stage, I won't dealing with the correct output format
    // like what should be quoted...
    /**
     * Returns a string representing this class (a <code>(make-class-decl ...)
     * </code>).
     *
     * @return	A String containing the <code>(make-class-decl ...)</code> that
     * specifies this class in M5.
     */
    public String printClass() throws ConstantPoolException {
        sb.append("; Automatically generated by jvm2m5");
        nl("");
        nl("(in-package \"M5\")");
        nl("(include-book \"models/jvm/m5/m5\" :dir :system)");
        nl("");
        nl("(defconst *" + cf.getName().replace('/', '.') + "*");
        indent(4);
        String name = cf.getName();
        String supername = cf.super_class != 0 ? cf.getSuperclassName() : null;
        nl("(make-class-decl");
        nl(" \"" + name + "\"");
        if (supername != null) {
            nl(" '(\"" + supername + "\")");
        } else {
            nl(" ()");
        }

        nl(" '(");
        indent(2);
        for (Field f : cf.fields) {
            if (!f.access_flags.is(AccessFlags.ACC_STATIC)) {
                String fname = f.getName(cp);
                String fdesc = f.descriptor.getValue(cp);
                nl("\"" + fname + ":" + fdesc + "\"");
            }
        }
        sb.append(")");
        indent(-2);

        nl(" '(");
        indent(2);
        for (Field f : cf.fields) {
            if (f.access_flags.is(AccessFlags.ACC_STATIC)) {
                String fname = f.getName(cp);
                String fdesc = f.descriptor.getValue(cp);
                nl("\"" + fname + ":" + fdesc + "\"");
            }
        }
        sb.append(")");
        indent(-2);

        nl(" '(nil");
        indent(3);
        int ind = 1;
        for (ConstantPool.CPInfo info : cp.entries()) {
            info.accept(this, true);
            comment(CP_TAB, ind);
            ind += info.size();
            for (int i = 1; i < info.size(); i++) {
                nl("nil");
            }
        }
        indent(-3);
        nl("  )");

        nl(" (list");
        indent(2);
        for (Method m : cf.methods) {
            printMethod(m);
        }
        sb.append(")");
        indent(-2);
        nl(" '(ref -1)))");
        indent(-4);
        return sb.toString();
    }

    public void printMethod(Method method) throws ConstantPoolException {
        String name = method.getName(cp);
        String desc = method.descriptor.getValue(cp);
        Code_attribute cai = (Code_attribute) method.attributes.get(Attribute.Code);

        nl("");
        sb.append("'(\"")
                .append(name)
                .append(":")
                .append(desc)
                .append("\"")
                .append(' ')
                .append((method.access_flags.is(AccessFlags.ACC_SYNCHRONIZED) ? "t" : "nil"));
        indent(2);

        if (cai != null) {
            LineNumberTable_attribute lnt
                    = (LineNumberTable_attribute) cai.attributes.get(Attribute.LineNumberTable);
            int li = 0; // index in linenumber table
            // get the parsed code part
            for (Instruction instr : cai.getInstructions()) {
                if (lnt != null && li < lnt.line_number_table.length && lnt.line_number_table[li].start_pc == instr.getPC()) {
                    nl("; " + "line_number #" + lnt.line_number_table[li].line_number);
                    li++;
                }
                nl('(' + instr.getMnemonic());
                ConstantPool.CPInfo info = instr.accept(this, null);
                sb.append(")");
                comment(CODE_TAB, instr.getPC());
                if (info != null) {
                    sb.append(' ');
                    info.accept(this, false);
                }
            }
        } else {
            if (method.access_flags.is(AccessFlags.ACC_NATIVE)) {
                nl("; native method");
            }
        }
        indent(-2);
        nl(" )");
    }

    // Instruction.KindVisitor<String, Void> methods
    @Override
    public ConstantPool.CPInfo visitNoOperands(Instruction instr, Void p) {
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitArrayType(Instruction instr, Instruction.TypeKind tk, Void p) {
        sb.append(" T_").append(tk.name.toUpperCase());
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitBranch(Instruction instr, int offset, Void p) {
        sb.append(' ').append(offset);
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitConstantPoolRef(Instruction instr, int index, Void p) {
        try {
            sb.append(' ').append(index);
            return cp.get(index);
        } catch (ConstantPoolException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ConstantPool.CPInfo visitConstantPoolRefAndValue(Instruction instr, int index, int value, Void p) {
        try {
            sb.append(' ').append(index).append(' ').append(value);
            return cp.get(index);
        } catch (ConstantPoolException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ConstantPool.CPInfo visitLocal(Instruction instr, int index, Void p) {
        sb.append(' ').append(index);
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitLocalAndValue(Instruction instr, int index, int value, Void p) {
        sb.append(' ').append(index).append(' ').append(value);
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitLookupSwitch(Instruction instr, int default_, int npairs, int[] matches, int[] offsets, Void p) {
        sb.append(" (lookupswitchinfo ")
                .append(default_) // the default target
                .append(' ')
                .append(npairs) // the pair count
                .append(" (");
        for (int i = 0; i < npairs; i++) {
            sb.append('(')
                    .append(matches[i])
                    .append(" . ")
                    .append(offsets[i])
                    .append(") ");
        }
        sb.setCharAt(sb.length() - 1, ')');
        sb.append(")");
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitTableSwitch(Instruction instr, int default_, int low, int high, int[] offsets, Void p) {
        sb.append(" (tableswitchinfo ")
                .append(default_) // the default target
                .append(" (")
                .append(low)
                .append(" . ")
                .append(high)
                .append(") (");
        for (int i = 0; i < high - low + 1; i++) {
            sb.append(offsets[i])
                    .append(' ');
        }
        sb.setCharAt(sb.length() - 1, ')');
        sb.append(")");
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitValue(Instruction instr, int value, Void p) {
        sb.append(' ').append(value);
        return null;
    }

    @Override
    public ConstantPool.CPInfo visitUnknown(Instruction instr, Void p) {
        sb.append(' ').append(instr.getOpcode());
        return null;
    }

    // ConstantPool.Visitor<String, Boolean> methods
    @Override
    public Void visitClass(ConstantPool.CONSTANT_Class_info c, Boolean inConstantPool) {
        try {
            String name = c.getName();
            if (inConstantPool) {
                return nl("(class (ref -1) \"" + c.getName() + "\")");
            }
            sb.append("class " + name.replace('/', '.'));
            return null;
        } catch (ConstantPoolException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Void visitDouble(ConstantPool.CONSTANT_Double_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(double #x"
                    + padLeft(Long.toHexString(Double.doubleToRawLongBits(c.value)), 16)
                    + ") ; " + Double.toHexString(c.value) + " " + c.value);
        }
        sb.append(c.value).append("d");
        return null;
    }

    @Override
    public Void visitFieldref(ConstantPool.CONSTANT_Fieldref_info c, Boolean inConstantPool) {
        try {
            String className = c.getClassName();
            ConstantPool.CONSTANT_NameAndType_info infoNameAndType = c.getNameAndTypeInfo();
            String name = infoNameAndType.getName();
            String desc = infoNameAndType.getType();
            if (inConstantPool) {
                int size = desc.equals("D") || desc.equals("J") ? 2 : 1;
                return nl("(fieldref \"" + className + "\" \"" + name + ":" + desc + "\" " + size + ")");

            }
            sb.append(className.replace('/', '.') + "." + name + ":" + desc);
            return null;
//            return " \"" + className + "\" \"" + name + ":" + desc + "\"";
        } catch (ConstantPoolException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Void visitFloat(ConstantPool.CONSTANT_Float_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(float #x"
                    + padLeft(Integer.toHexString(Float.floatToRawIntBits(c.value)), 8)
                    + ") ; " + Float.toHexString(c.value) + " " + c.value);
        }
        sb.append(c.value).append("f");
        return null;
    }

    @Override
    public Void visitInteger(ConstantPool.CONSTANT_Integer_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(integer " + c.value + ")");
        }
        sb.append(c.value);
        return null;
    }

    @Override
    public Void visitInterfaceMethodref(ConstantPool.CONSTANT_InterfaceMethodref_info c, Boolean inConstantPool) {
        try {
            String className = c.getClassName();
            ConstantPool.CONSTANT_NameAndType_info infoNameAndType = c.getNameAndTypeInfo();
            String name = infoNameAndType.getName();
            String desc = infoNameAndType.getType();
            if (inConstantPool) {
                String[] ss = splitMethodDesc(desc);
                int paramCount = ss.length - 1;
                for (int i = 1; i < ss.length; i++) {
                    if (ss[i].equals("D") || ss[i].equals("J")) {
                        paramCount++;
                    }
                }
                return nl("(interface-methodref \"" + className + "\" \"" + name + ":" + desc + "\" " + paramCount + ")");
            }
            sb.append(className.replace('/', '.') + "." + name + ":" + desc);
            return null;
        } catch (ConstantPoolException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Void visitInvokeDynamic(ConstantPool.CONSTANT_InvokeDynamic_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(invoke-dynamic)");
        }
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visitLong(ConstantPool.CONSTANT_Long_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(long " + c.value + ")");
        }
        sb.append(c.value).append("f");
        return null;
    }

    @Override
    public Void visitNameAndType(ConstantPool.CONSTANT_NameAndType_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            try {
                String name = c.getName();
                String desc = c.getType();
                return nl("(name-and-type \"" + name + ":" + desc + "\")");
            } catch (ConstantPoolException e) {
                return nl("\"" + e.getMessage() + "\"");
            }
        }
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visitMethodref(ConstantPool.CONSTANT_Methodref_info c, Boolean inConstantPool) {
        try {
            String className = c.getClassName();
            ConstantPool.CONSTANT_NameAndType_info infoNameAndType = c.getNameAndTypeInfo();
            String name = infoNameAndType.getName();
            String desc = infoNameAndType.getType();
            if (inConstantPool) {
                String[] ss = splitMethodDesc(desc);
                int paramCount = ss.length - 1;
                for (int i = 1; i < ss.length; i++) {
                    if (ss[i].equals("D") || ss[i].equals("J")) {
                        paramCount++;
                    }
                }
                return nl("(methodref \"" + className + "\" \"" + name + ":" + desc + "\" " + paramCount + ")");
            }
            sb.append(className.replace('/', '.') + "." + name + ":" + desc);
            return null;
        } catch (ConstantPoolException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Void visitMethodHandle(ConstantPool.CONSTANT_MethodHandle_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(method-handle)");
        }
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visitMethodType(ConstantPool.CONSTANT_MethodType_info c, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(method-type)");
        }
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visitString(ConstantPool.CONSTANT_String_info c, Boolean inConstantPool) {
        try {
            String value = c.getString();
            if (inConstantPool) {
                nl("(string (ref -1) ; \"");
                appendString(sb, value);
                sb.append("\"");
                nl("  ");
                for (int j = 0; j < value.length(); j++) {
                    sb.append(" ").append((int) value.charAt(j));
                }
                sb.append(")");
                return null;
            }
            sb.append("\"");
            appendString(sb, value);
            sb.append("\"");
            return null;
        } catch (ConstantPoolException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Void visitUtf8(ConstantPool.CONSTANT_Utf8_info cnstnt, Boolean inConstantPool) {
        if (inConstantPool) {
            return nl("(utf8)");
        }
        throw new UnsupportedOperationException("Not supported yet.");
    }

    private static String[] splitMethodDesc(String desc) {
        List<String> ls = new ArrayList<>();
        int ind = desc.indexOf(')');
        assert desc.charAt(0) == '(' && ind > 0;
        ls.add(desc.substring(ind + 1));
        desc = desc.substring(1, ind);
        while (!desc.isEmpty()) {
            int i = 0;
            while (desc.charAt(i) == '[') {
                i++;
            }
            if (desc.charAt(i) == 'L') {
                i = desc.indexOf(';') + 1;
            } else {
                i++;
            }
            ls.add(desc.substring(0, i));
            desc = desc.substring(i);
        }
        return ls.toArray(new String[ls.size()]);
    }

    private static void appendString(StringBuilder sb, String value) {
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
                case '\b':
                    sb.append("\\b");
                    break;
                case '\t':
                    sb.append("\\t");
                    break;
                case '\n':
                    sb.append("\\n");
                    break;
                case '\f':
                    sb.append("\\f");
                    break;
                case '\r':
                    sb.append("\\r");
                    break;
                case '"':
                    sb.append("\\\"");
                    break;
                case '\'':
                    // Compatibility with the bug in CFParse
                    sb.append("\\'");
                    break;
                case '\\':
                    sb.append("\\\\");
                    break;
                default:
                    if (c >= ' ' && c <= '~') {
                        sb.append(c);
                    } else {
                        sb.append("\\u").append(padLeft(Integer.toHexString(c), 4));
                    }
            }
        }
    }

    private static String padLeft(String s, int w) {
        while (s.length() < w) {
            s = '0' + s;
        }
        return s;
    }
}
