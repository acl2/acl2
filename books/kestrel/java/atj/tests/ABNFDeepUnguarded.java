import edu.kestrel.acl2.aij.*;

public final class ABNFDeepUnguarded {

    static {
        ABNFDeepUnguardedEnvironment.build();
    }

    public static void initialize() {
    }

    public static Acl2Value call(Acl2Symbol function, Acl2Value[] arguments) throws Acl2UndefinedPackageException {
        return Acl2NamedFunction.make(function).call(arguments);
    }
}
