{
    let a
    function f() {}
}
// ====
// dialect: yul
// ----
// step: functionHoister
//
// {
//     let a
//     function f()
//     { }
// }
