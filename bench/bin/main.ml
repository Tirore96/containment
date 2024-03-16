open Bench.Testsuite
open Bench.Slowtest
let () = 
         let _ = test1 () in
         let _ = test1' () in

         let _ = test2 () in
         let _ = test2' () in

         let _ = test3 () in
         let _ = test3' () in

         let _ = test4 () in
         let _ = test4' () in

         let _ = test5 () in
         let _ = test5' () in

         let _ = test6 () in
         let _ = test6' () in

         let _ = test7 () in
         let _ = test7' () in

         let _ = test8 () in
         let _ = test8' () in
(**      let _ = slowtest () in *)
         ()

