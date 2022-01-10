{ let a { } function f() -> x { let b := 4 {} for {} f() {} {} } }
// ====
// dialect: yul
// ----
// step: functionGrouper
//
// {
//     {
//         let a
//         { }
//     }
//     function f() -> x
//     {
//         let b := 4
//         { }
//         for { } f() { }
//         { }
//     }
// }
