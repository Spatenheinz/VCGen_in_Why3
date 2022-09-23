type t = int

let fresh =
  let c = ref 0 in
  fun () -> incr c; !c

let to_string v =
  "v"^string_of_int v

let compare v1 v2 =
  v2 - v1
