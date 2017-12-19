type variable = string;;
type symbol = string;;

type term = V of variable | Node of symbol * term list;;
type arity = int;;

type signature = (symbol * arity) list;;

let rec member x s1 = match s1 with []-> false

		| y::ys -> if (x = y) then true else member x ys;;


let rec map f lst = match lst with []->[]
		
		| x::xs -> f(x)::(map f xs);;


let rec filter f lst = match lst with []-> []

		| x::xs -> if f(x) then x::(filter f xs) else filter f xs;;


let rec fold f e lst = match lst with []-> e
		
		| x::xs -> fold f (f e x) xs;;


let and_1 a b = a && b;;


let add a b = a+b;;


let union s1 s2 = let rec union1 s1 s2 s3 = match s1 with []-> s3

		|x::xs-> if member x s2 then union1 xs s2 s3 else union1 xs s2 (x::s3) in union1 s1 s2 s2;;


let rec member x s1 = match s1 with []-> false

		|y::ys -> if (x = y) then true else member x ys;;


exception UnequalLists;;
let rec zip s1 s2 = match s1,s2 with ([],[])-> []
		
		| ([],_) -> raise UnequalLists
		
		| (_,[])-> raise UnequalLists
		
		| (x::xs, y::ys)->(x,y)::(zip xs ys);;


let rec check_sig_help s syb_list= match s with [] -> true

		| (x,y)::xs -> if (y>=0) && (not (member x syb_list)) then (check_sig_help xs (x::syb_list)) else false;;


let check_sig (s:signature) = check_sig_help s [];;


exception SymbolNotFound;;
let rec find_arity s sym = match s with []-> raise SymbolNotFound

		| (x,y)::xs -> if x = sym then y else find_arity xs sym;;


let rec wfterm1 s t = if check_sig s then match t with V(x)-> true

		| Node(sym,term_list) -> if (find_arity s sym) = List.length(term_list) then fold and_1 true (map (wfterm1 s) term_list) else false

	else false;;


let wfterm t s = wfterm1 s t;;


let rec ht t = match t with V(x) -> 0

		| Node(sym, term_list)-> 1 + fold max 0 (map ht term_list);;


let rec size t = match t with V(x) -> 1

		| Node(sym,term_list)->1 + fold add 0 (map size term_list);;


let rec vars t : (variable list) = match t with V(x) -> [x]

		| Node(sym,term_list) -> fold union [] (map vars term_list);;


type substitution = (variable * term) list;;


type substitution_composition = substitution list;;


let rec find_sub x s = match s with []-> V(x)

		| (y,z)::ys-> if x = y then z else find_sub x ys;;


let rec substitute s t = match t with V(x) -> find_sub x s
		
		| Node(sym,term_list) -> Node(sym,(map (substitute s) term_list));;


let rec subst (t:term) (sc:substitution_composition) = match sc with []-> t

		| x::scs -> subst (substitute x t) scs;;


let rec subst1 t s = subst s t;;


exception NonUnifiable;;
let rec mgu_comp term_list1 term_list2 = match term_list1,term_list2 with ([],[])-> []

		|(t1::[], t2::[])->begin
			
			match (t1,t2) with (V(x),V(y)) -> if x = y then [] else [[(x,t2)]]

					| (V(x),_)-> if member x (vars t2) then raise NonUnifiable else [[(x,t2)]]

					| (_,V(y))-> if member y (vars t1) then raise NonUnifiable else [[(y,t1)]]

					| ((Node(x,term_list1)),(Node(y,term_list2)))-> if x = y then mgu_comp term_list1 term_list2
													else raise NonUnifiable
		end

		|(x::xs,y::ys)-> let sigma = mgu_comp [x] [y] in List.append sigma (mgu_comp (map (subst1 sigma) xs) (map (subst1 sigma) ys))

		| _-> raise NonUnifiable;;



let mgu t1 t2 = mgu_comp [t1] [t2];;

(*Testing*)
let term1 = Node("2",[V("P")]);;
let term2 = Node("*",[V("X"); Node("+",[term1;term1])]);;
let term3 = V("Y");;
let term4 = (Node("g",[V "X";Node("*",[term2;V "X"])]));;
let term5 = (Node("g",[V "Z";Node("*",[V "X";V "Z"])]));;
let term6 = (Node("g",[V "Z";Node("g",[V "X";V "Z"])]));;
mgu term4 term5;;
let sub1 = [["P",V("R")]];;
let sub2 = [["Y",Node("g",[V("Z");V("X")])]];;
let sub3 = [["X",V("Y")];["Y",Node("2",[])]];;
let sub4 = [["Y",V("Z")];["X",Node("*",[V("Y");V("Y")];;
let sub5 = [["Z",Node("g",[V("X");Node("*",[V("Y");Node("*",[V("X");V("Y")])])])];["Y",V("N")];["X",V("M")]];;
let sub6 = [["Y",V("N")];["X",V("M")];["Z",Node("g",[V("X");Node("*",[V("Y");Node("*",[V("X");V("Y")])])])]];;
let sub7 = [["X",V("I")]];;
let sub8 = [["Y",V("J")]];;

subst term1 sub1;;
