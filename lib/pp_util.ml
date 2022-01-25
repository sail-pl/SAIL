
let pp_print_pair (pp_a : Format.formatter -> 'a -> unit)
(pp_b : Format.formatter -> 'b -> unit) (pf : Format.formatter)
((x, v) : 'a * 'b) : unit =
Format.fprintf pf "(%a:%a)" pp_a x pp_b v

let pp_print_option (pp_a : Format.formatter -> 'a -> unit) (pf : Format.formatter)
(x : 'a option) : unit =
match x with None -> Format.fprintf pf "_" | Some x -> pp_a pf x
