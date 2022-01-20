{
	let a function f() {}
}
// ====
// dialect: yul
// ----
// step: functionGrouper
//
// {
//     { let a }
//     function f()
//     { }
// }
