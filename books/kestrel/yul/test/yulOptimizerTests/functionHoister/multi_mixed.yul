{
    let a
    function f() { let b }
    let c
    function g() { let d }
    let e
}
// ====
// dialect: yul
// ----
// step: functionHoister
//
// {
//     let a
//     let c
//     let e
//     function f()
//     { let b }
//     function g()
//     { let d }
// }
