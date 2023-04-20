let cB x y z = x (y z) ;;
let cC x y z = x z y ;;
let cK x y = x ;;
let cW x y = x y y;;

let cI x = cW cK x ;;
let cS x y z = cB (cB cW) (cB cB cC) x y z ;;

type church_num = { f : 'a. ('a -> 'a) -> 'a -> 'a } ;;

let zero (x : 'a -> 'a) : church_num = cK cI ;; (* cK cI (fun (x : int) : int -> x) ;; *)
let succ x : church_num = cS (cS (cK cS)cK) x ;;

(* let one = cS (cS (cK cS) cK) (cK cI) ;; *)
(* let s0 = succ zero ;; *)

let print_bool b = if b then print_int 1 else print_int 0 ;;

let church_to_int (n : church_num) =
    (n (fun x -> x + 1) 0) ;;

let test : church_num = succ zero ;;
let test2 : church_num = succ test ;;

print_int (church_to_int test);;
