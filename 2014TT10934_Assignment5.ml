type atomic_formula = P of string;;
type head = atomic_formula;;
type body = atomic_formula list;;
type clause = Fact of head| Rule of head * body;;
type program = clause list;;

let rec member x s1= match s1 with
		
		[]-> false
		
		|y::ys -> if (x = y) then true else member x ys;;


let union s1 s2 = let rec union1 s1 s2 s3 = match s1 with
		
		[]-> s3
		
		| x::xs-> if member x s2 then union1 xs s2 s3 else union1 xs s2 (x::s3) in union1 s1 s2 s2;;


let difference s1 s2 = let rec difference1 s1 s2 s3 = match s1 with
		
		[]-> s3
		
		|x::xs-> if member x s2 then difference1 xs s2 s3 else difference1 xs s2 (x::s3) in difference1 s1 s2 [];;


exception CantbeResolved;;
(*Removing self loop cases in which head repeats inside body; such clauses are useless since they remain of the same size or increase*)
let rec isresolveable goal (p:clause) = match p with 

		Rule(h,b) -> if (member h b) then false else member h goal

		| Fact(h) -> member h goal;;


let rec resolve goal (p:clause) = match p with 

		Rule(h,b) -> difference (union goal b) [h]

		| Fact(h) -> difference goal [h];;


let rec resolve_stack_h goal (p:program) q = if goal = [] then true else match p with 

		[]-> false

		| y::ys-> if (isresolveable goal y) then 
						if resolve_stack_h (resolve goal y) q q then 
							true 
						else resolve_stack_h goal ys q
				else resolve_stack_h goal ys q;;


let resolve_stack g p = resolve_stack_h g p p;;


resolve_stack [P("1");P("2")] [Fact(P("1"));Fact(P("3"));Fact(P("4"));Rule(P("2"), [P("3");P("4")])];;


let rec resolve_queue_h goal (p:program) q queue = if goal = [] then true else match p with 

		[]-> begin
			match queue with
			| [] -> false
			| (a,b)::xs -> resolve_queue_h a b q xs
		end

		| y::ys -> if (isresolveable goal y) then 
						if resolve goal y = [] then 
							true 
						else
							resolve_queue_h goal ys q (List.append queue [(resolve goal y),q])
				else resolve_queue_h goal ys q queue;;

let resolve_queue goal p= resolve_queue_h goal p p [];;

resolve_queue [P("1");P("2")] [Fact(P("1"));Fact(P("3"));Fact(P("4"));Rule(P("2"), [P("3");P("4")])];;
resolve_queue [P("1");P("2")] [Rule(P("1"), [P("3")]);Rule(P("3"), [P("1")]);Fact(P("1"));Fact(P("2"))];;
resolve_stack [P("1");P("2")] [Rule(P("1"), [P("3")]);Rule(P("3"), [P("1")]);Fact(P("1"));Fact(P("2"))];;








