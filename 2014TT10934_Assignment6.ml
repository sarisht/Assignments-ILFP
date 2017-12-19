type variable = string;;
type constant = string;;
type predicate = string;;

type term = V of variable|Node of predicate * term list;;

type atomic_formula = P of predicate * term list;;
type clause = Fact of atomic_formula | Rule of atomic_formula * atomic_formula list;;
type goal = atomic_formula list;;
type program = clause list;;

(*
	append([],X,X)
	append(X|Xs, Y, X|Z) :- append(Xs,Y,Z)

	converts to :
		[Fact(Pred("append",[C("empty"), V('X'),V('X')])); Rule(Pred("append",[Node ("|",[V "x"; V "xs"]);V "y";V "z"]),[Pred ("append",[V "xs";V"y";V"z"])] )]

 append ([1,2,3], [4,5], V"a")
 append ()

 *)

 let rec member x s1 = match s1 with []-> false

		| y::ys -> if (x = y) then true else member x ys;;


let rec map f lst = match lst with []->[]
		
		| x::xs -> f(x)::(map f xs);;


let rec filter f lst = match lst with []-> []

		| x::xs -> if f(x) then x::(filter f xs) else filter f xs;;


let rec fold f e lst = match lst with []-> e
		
		| x::xs -> fold f (f e x) xs;;


let rec union s1 s2 = match s1 with []-> s2

		|x::xs-> if member x s2 then union xs s2 else x::union xs s2;;


let rec difference s1 s2 = match s1 with
		
		[]-> []
		
		|x::xs-> if member x s2 then difference xs s2 else x::difference xs s2;;


exception UnequalLists;;
let rec zip s1 s2 = match s1,s2 with ([],[])-> []
		
		| ([],_) -> raise UnequalLists
		
		| (_,[])-> raise UnequalLists
		
		| (x::xs, y::ys)->(x,y)::(zip xs ys);;


let rec vars t  = match t with V(x) -> [x]

		| Node(sym,term_list) -> fold union [] (map vars term_list);;


type substitution = (variable * term) list;;


type substitution_composition = substitution list;;


let rec find_sub x s = match s with []-> V(x)

		| (y,z)::ys-> if x = y then z else find_sub x ys;;


let rec substitute s t = match t with V(x) -> find_sub x s
		
		| Node(sym,term_list) -> Node(sym,(map (substitute s) term_list));;


let rec subst t sc = match sc with []-> t

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


let rec mgu_atomic af1 af2 = match af1,af2 with P(a,t1), P(b,t2)-> if a = b then mgu_comp t1 t2 else raise NonUnifiable;;


let is_unifiable term1 term2 = try 
		
			let _ = mgu_atomic term1 term2 in true 
		
		with NonUnifiable -> false;;


let rec is_unifiable_list term term_list = match term_list with []-> false

		| x::xs-> if is_unifiable x term then true else is_unifiable_list term xs;;


let rec extract_atomic t = match t with Fact(x)-> x| Rule(x,_)-> x;;


let rec mgu_l list1 t = let y = extract_atomic t in match list1 with []-> raise NonUnifiable

		| x::xs -> if is_unifiable x y then mgu_atomic x y else mgu_l xs t;;


let rec substafl g sc = match g with [] -> []

		| P(a,b)::xs -> P(a,(map (subst1 sc) b))::(substafl xs sc);;

(*type variable = string;;
type constant = string;;
type predicate = string;;

type term = V of variable|Node of predicate * term list;;

type atomic_formula = P of predicate * term list;;
type clause = Fact of atomic_formula | Rule of atomic_formula * atomic_formula list;;
type goal = atomic_formula list;;
type program = clause list;;


	append([],X,X)
	append(X|Xs, Y, X|Z) :- append(Xs,Y,Z)

	converts to :
		[Fact(Node("append",[C("empty"), V('X'),V('X')])); Rule(Node("append",[Node ("|",[V "X"; V "xs"]);V "y";Node V "z"]),[Node ("append",[V "xs";V"y";V"z"])] )]

 append ([1,2,3], [4,5], V"a")
 append ()

 *)

exception CantbeResolved;;
(*Removing self loop cases in which head repeats inside body; such clauses are useless since they remain of the same size or increase*)
let rec isresolveable goal p = match p with 

		Rule(h,b) -> is_unifiable_list h goal

		| Fact(h) -> is_unifiable_list h goal;;


let rec func1 g = match g with []-> []

		| (P(a,b))::xs -> List.append (fold union [] (map vars b)) (func1 xs);;



let rec change_variables g i = let variables = func1 g in 

								let rec kai v i = match v with []->[]| x::xs-> (x,V(String.concat "-" ([x;string_of_int(i)])))::(kai xs i) in 

									((kai variables i),i+1);;


let rec improve sc = match sc with []->[]

		|x::xs-> begin
			
			match x with []-> improve xs

			|(a,b)::ys-> (a,(subst1 (ys::xs) b))::improve(ys::xs)

		end;;


let rec resolve g c sc1 i = let goal = substafl g sc1 in 

							match c with 

		Rule(h,b) -> let h1::_ = substafl [h] [(improve sc1)] in let b1 = substafl b [(improve sc1)] in let gg = (difference (union goal b1) [h1]) in let (sc,k) = change_variables gg i in 

								((substafl gg [sc]),k)

		| Fact(h) ->  let h1::_  = substafl [h] [(improve sc1)] in let gg = (difference goal [h1])in let (sc,k) = change_variables gg i in (substafl gg [sc]),k;;




let rec func2 s g = let variables = func1 g in match s with []-> []

		|(a,b)::xs -> if member a variables then (a,b)::(func2 xs g) else (func2 xs g);;


let rec func sc g = match sc with []-> []

		|x::xs -> union (func2 x g) (func xs g);;


let rec print_term t = match t with V(x) -> let () = print_string(", ") in let() =print_string(x) in false 

		|Node(x,y)-> let () = print_string("Node of (")in let() = print_string(x) in let () = print_string(", [") in let _ = map print_term (List.rev(y)) in let ()= print_string("])") in false;;


let rec print_substcomp sc = match sc with []-> false

		|x::xs-> begin
			
			match x with []-> print_substcomp xs

					| (v,t)::ys -> let () = print_string(v) in let () = print_string(" : ") in let _ = print_term(t) in let () = print_string(", ") in print_substcomp (ys::xs)

		end;;


let f n =

     	let () = print_string ".......type 1 to continue: " in
     
    	let i = read_int () in 
       
       		if i = n then true else false;;





let rec resolve_stack_h goal1 g p q sc i = if goal1 = [] then let x = sc in let _ = print_substcomp x in let i = f 1 in not i

		else match p with 

		[]->false

		| y::ys-> if (isresolveable goal1 y) then 

					let gf,_ = (change_variables goal1 i) in 

					let goal = substafl goal1 [gf] in 

					let sc1 = [improve (union sc (mgu_l goal y))] in

						let gg,k = resolve goal y (mgu_l goal y) i in 

						if resolve_stack_h gg g q q sc1 k then true 
					
						else resolve_stack_h goal1 g ys q sc i
				
				else resolve_stack_h goal1 g ys q sc i;;


let resolve_stack g p = if resolve_stack_h g g p p [] 0 then print_string("true") else print_string("false");;

let p = [Fact(P("append",[Node("empty",[]);V("X");V("X")])); Rule(P("append",[Node ("|",[V "X"; V "XS"]);V "Y";Node ("|",[V "X"; V "Z"])]),[P("append",[V "XS";V"Y";V"Z"])] )];;

let g1 = [P("append",[Node("empty",[]);Node ("|",[V "x1"; V "xs1"]);V("y1")])];;

let g2 = [P("append",[Node("|",[Node ("1",[]); Node ("|",[Node("2",[]);Node("empty",[])])]);Node ("|",[Node("3",[]);Node("empty",[])]);Node("|",[Node ("1",[]); Node ("|",[Node ("2",[]); Node ("|",[Node("3",[]);Node("empty",[])])])])])];;

let g3 = [P("append",[V("x1");Node ("|",[Node("3",[]);Node("empty",[])]);Node("|",[Node ("1",[]); Node ("|",[Node ("2",[]); Node ("|",[Node("3",[]);Node("empty",[])])])])])];;

let g4 = [P("append", [V("x1");V("x2");Node("|",[Node ("1",[]); Node ("|",[Node ("2",[]); Node ("|",[Node("3",[]);Node("empty",[])])])])])];;

let program1 = [Fact(P("append",[Node("empty",[]);V("X");V("X")])); Rule(P("append",[Node ("|",[V "X"; V "XS"]);V "Y";Node ("|",[V "X"; V "Z"])]),[P("append",[V "XS";V"Y";V"Z"])] )];;

let query1_1 = [P("append",[Node ("|",[Node("1",[]);Node("empty",[])]);Node ("|",[Node ("2",[]); Node ("|",[Node("3",[]);Node("empty",[])])]);Node ("|",[Node ("1",[]); Node ("|",[Node("3",[]);Node("empty",[])])])])];;

let query1_2 = [P("append",[Node("|",[Node ("1",[]); Node ("|",[Node("2",[]);Node("empty",[])])]);Node ("|",[Node ("2",[]); Node ("|",[Node("3",[]);Node("empty",[])])]);V("x")])];;

resolve_stack query1_2 program1;;
