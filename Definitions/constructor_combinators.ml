type comb = B | K | C | W | Apply of comb * comb 

let composite_combinators = [
    ('I', Apply (W, K));
    ('S', Apply (
        Apply (B, Apply (B, W)),
        Apply (Apply (B, B), C)
    ))
]

let comb_list_to_comb (cl : comb list) : comb = 
    match cl with 
    | [] -> Apply (W, K)
    | h :: t -> List.fold_left (fun (acc : comb) (item : comb) -> Apply (acc, item)) h t

let print_bool b = if b then print_string "true" else print_string "false" 

let composite_combinator_char c =
    List.fold_left (fun acc item -> 
        if acc <> None then acc else 
            if fst item == c then Some (snd item) else None
    ) None composite_combinators 

let rec str_to_expr_list (s : string) : comb list =
    (* let explode s = List.init (String.length s) (String.get s) in
    let rec s2el_helper (c : char list) : comb list =
        match c with 
        | [] -> []
        | h :: t -> match h with 
            | 'B' -> B :: (s2el_helper t)
            | 'C' -> C :: (s2el_helper t)
            | 'K' -> K :: (s2el_helper t)
            | 'W' -> W :: (s2el_helper t)
            | '(' -> comb_list_to_comb (s2el_helper t) :: (s2el_helper t)
            | ')' -> s2el_helper t
            | _ -> [Apply (W, K)] in
    s2el_helper (explode s)  *)
    if String.length s == 0 then [] else
        let rs = s in (* string_rev s in *)
        let rs0 = String.get rs 0 in
        let rs' = String.sub rs 1 (String.length rs - 1) in
        match rs0 with
        | 'B' -> B :: (str_to_expr_list rs')
        | 'C' -> C :: (str_to_expr_list rs')
        | 'K' -> K :: (str_to_expr_list rs')
        | 'W' -> W :: (str_to_expr_list rs')
        | c -> match composite_combinator_char c with
            | None -> str_to_expr_list rs'
            | Some x -> x :: (str_to_expr_list rs') 

let expr_list_to_str e = 
    let rec _h e =
        match e with
        | [] -> ""
        | h :: t -> (match h with 
            | B -> "B"
            | C -> "C"
            | K -> "K"
            | W -> "W"
            | Apply (a, b) -> "(" ^ (_h [a]) ^ (_h [b]) ^ ")"
        ) ^ (_h t) in
    (_h e) ^ "\n" 

let print_expr (e : comb) = print_string (expr_list_to_str [e]) ;;

let in_range n l = n >= 0 && n < List.length l 

let safe_nth l n = if in_range n l then Some (List.nth l n) else None 

(* let rec comb_range (e : comb list) min max: comb option list =
    if in_range min e && in_range max e && min <= max then 
        (safe_nth e min) :: (comb_range e (min + 1) max)
    else []  *)

let rec remove_nones (l : 'a option list) : 'a list = 
    match l with
    | [] -> []
    | h :: t -> match h with 
        | Some x -> x :: remove_nones t 
        | _ -> remove_nones t 

let extract_comb (x : comb option) : comb =
    match x with
    | Some a -> a
    | None -> Apply (W, K)

let comb_opt_to_str (x : comb option) : string = 
    match x with 
    | Some a -> let s = expr_list_to_str [a] in 
                String.sub (s) 0 (String.length s - 1)
    | None -> "_" 

let rec list_without_first_n (l : 'a list) (n : int) : 'a list =
    if n <= 0 then l else 
        match l with 
        | [] -> []
        | h :: t -> list_without_first_n t (n - 1) 

let debug : bool = false
let rec reduce (e : comb list) : comb list =
    match e with [] -> [] | h :: t ->
        let x = safe_nth t 0 in let y = safe_nth t 1 in let z = safe_nth t 2 in
        let t_without_xy = list_without_first_n t 2 in 
        let t_without_xyz = list_without_first_n t 3 in 
        let () = (if debug then 
            let () = print_string ("e: " ^ expr_list_to_str e) in
            let () = print_string ("h: " ^ expr_list_to_str [h]) in
            let () = print_string ("t: " ^ expr_list_to_str t) in 
            let () = print_string ("x, y, z: " ^ (comb_opt_to_str x) ^ ", " ^ (comb_opt_to_str y) ^ ", " ^ (comb_opt_to_str z) ^ "\n") in
            print_string ("--------------\n")
        else ()) in
    match h with 
    | B -> if x = None || y = None || z = None then 
                e
            else
                reduce ([Apply (extract_comb x, Apply (extract_comb y, extract_comb z))] @ t_without_xyz)
    | C -> if x = None || y = None || z = None then 
                e
            else
                reduce ([extract_comb x; extract_comb z; extract_comb y] @ t_without_xyz)
    | K -> if x = None || y = None then 
                e
            else
                reduce ([extract_comb x] @ t_without_xy)
    | W -> if x = None || y = None then 
                e
            else
                reduce ([extract_comb x; extract_comb y; extract_comb y] @ t_without_xy)
    | Apply (a, b) -> reduce (reduce [a; b] @ t) ;;

let () = assert (expr_list_to_str (reduce (str_to_expr_list "BCKWBCBWBK")) = "BW(BK)\n") ;;
let () = assert (expr_list_to_str (reduce (str_to_expr_list "BKBKBK")) = "BKK\n") ;;
let () = assert (expr_list_to_str (reduce [Apply (B, K); Apply (B, K); Apply (B, K)]) = "K((BK)(BK))\n") ;;

print_string (
    expr_list_to_str (reduce (str_to_expr_list "SKSKSK"))
) ;;

print_string (
    expr_list_to_str (reduce (str_to_expr_list "S"))
)
