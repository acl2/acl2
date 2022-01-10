{ { let a let a_1 } { let a } }
// ====
// dialect: yul
// ----
// step: disambiguator
//
// {
//     {
//         let a
//         let a_1
//     }
//     { let a_2 }
// }
