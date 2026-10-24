// Test where the parameter is an object.

public class ClassTest {
    public int value() {
        return 42;
    }

    public static boolean testValue(ClassTest x) {
        return x == null || x.value() == 42;
    }
}
