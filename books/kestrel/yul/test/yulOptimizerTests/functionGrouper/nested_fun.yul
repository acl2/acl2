{
    let a
    function f() {
        let b
        function g() {
            let c
        }
        let d
    }
}
// ====
// dialect: yul
// ----
// step: functionGrouper
//
// {
//     { let a }
//     function f()
//     {
//         let b
//         function g()
//         { let c }
//         let d
//     }
// }
