{
    { let a, b }
    {
        function eq(x, y) -> z {}
        for { let a } eq(a, a) { a := a } {
            let b := a
        }
    }
}
// ====
// dialect: yul
// ----
// step: disambiguator
//
// {
//     { let a, b }
//     {
//         function eq(x, y) -> z
//         { }
//         for { let a_1 } eq(a_1, a_1) { a_1 := a_1 }
//         { let b_2 := a_1 }
//     }
// }
