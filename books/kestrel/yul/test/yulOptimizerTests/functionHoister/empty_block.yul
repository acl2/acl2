{
    let a
    { }
    function f() -> x {
        let b := 4
        { }
        for {} f() {} {}
    }
}
// ====
// dialect: yul
// ----
// step: functionHoister
//
// {
//     let a
//     function f() -> x
//     {
//         let b := 4
//         for { } f() { }
//         { }
//     }
// }
