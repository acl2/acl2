// minimal program that shows canonicalization of Self in both type location and expression location

// From https://developer.aleo.org/developer/language/circuits
// Added a param and a return to main.
// Changed initial value of Foo's a from 0 to 8.

function main(a: u32) -> u32 {
    let f = Foo::new(); // new is a static function.
    return a - f.a;
}

circuit Foo {
    a: u32,

    // Instantiates a new Foo circuit with a = 0u32.
    function new() -> Self { // Self resolves to circuit type Foo
        return Self { a: 8u32 };
    }
}
