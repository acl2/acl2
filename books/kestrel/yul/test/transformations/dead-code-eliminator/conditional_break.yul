{
    let a := 20
    for {
    }
    mylt(a, 40)
    {
        a := myadd(a, 2)
    }
    {
        a := a
        if mylt(a, 0)
        { break }
    }
    function mylt(a, b) -> c { }
    function myadd(a, b) -> c { }
}

// ----
// step: deadCodeEliminator
//
// {
//     let a := 20
//     for { } mylt(a, 40) { a := myadd(a, 2) }
//     {
//         a := a
//         if mylt(a, 0) { break }
//     }
//     function mylt(a, b) -> c { }
//     function myadd(a,b) -> c { }
// }
