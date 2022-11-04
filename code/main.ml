open Eval
let prog =
             Sass  (Z.of_int 1, ABin (
                        Acst (Z.of_int 5)
                        , Mul
                        , Acst (Z.of_int 10)))
let prog' = Sseq (
             Sass  (Z.of_int 1, ABin (
                        Acst (Z.of_int 5)
                        , Mul
                        , Acst (Z.of_int 10)))
             , Sass (Z.of_int 2 , ABin (
                         Acst (Z.of_int 5)
                       , Add
                       , Avar (Z.of_int 3))))
let res = eval_prog prog
let () = List.iter (fun (k,v) -> Format.printf "%d, %d\n" (Z.to_int k) (Z.to_int v)) res
let () = List.iter (fun (k,v) -> Format.printf "%d, %d\n" (Z.to_int k) (Z.to_int v)) sigma.lst
let res' = eval_prog prog'
