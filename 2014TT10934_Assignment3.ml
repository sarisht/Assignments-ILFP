(*Basic Type defined as required in the code*)
type prop = P of string | T | F

	    | Not of prop | And of prop * prop

    	| Or of prop * prop | Implies of prop * prop;;

type 'a set = 'a list;;

type sequent = prop set * prop;;

type prooftree  = Ass of sequent | TI of sequent | FE of sequent

        | ImpI of prooftree * sequent | ImpE of prooftree * prooftree * sequent 

        | AndI of prooftree * prooftree * sequent | AndEleft of prooftree * sequent | AndEright of prooftree * sequent 

        | OrIleft of prooftree * sequent | OrIright of prooftree * sequent | OrE of prooftree * prooftree * prooftree * sequent 

        | NotClass of  prooftree * sequent |  NotIntu of prooftree * sequent ;;

(*Previous Assignment functions needed*)

let rec member x s1 = match s1 with []-> false

		|y::ys -> if (x = y) then true else member x ys;;


let union s1 s2 = let rec union1 s1 s2 s3 = match s1 with []-> s3

		|x::xs-> if member x s2 then union1 xs s2 s3 else union1 xs s2 (x::s3) in union1 s1 s2 s2;;


let difference s1 s2 = let rec difference1 s1 s2 s3= match s1 with []-> s3

		|x::xs-> if member x s2 then difference1 xs s2 s3 else difference1 xs s2 (x::s3) in difference1 s1 s2 [];;


let rec subset s1 s2 = match s1 with [] -> true
		
		|x::xs -> if member x s2 then subset xs s2 else false;;


let equalset s1 s2 = (subset s1 s2) && (subset s2 s1);;


let rec nnf p = match p with

		P(x)-> P(x)

		|T  -> T

		|F  -> F

		|Implies(p1,p2)-> Or((nnf (Not p1)),(nnf p2))

		|Not(Or(p1,p2))-> And((nnf (Not p1)), (nnf (Not p2)))

		|Not(And(p1,p2))-> Or((nnf (Not p1)), (nnf (Not p2)))

		|Not(Implies(p1,p2))-> And (nnf p1, nnf (Not p2))

		|Not(Not(p1))-> nnf p1

		|Not(T)-> F

		|Not(F)-> T

		|Not(p1)-> Not(nnf p1)

		|And(p1,p2)-> And((nnf p1), (nnf p2))

		|Or(p1,p2)-> Or((nnf p1), (nnf p2));;



let rec cnf_prop p = match nnf p with

		P(x)-> P(x)

		|T  -> T

		|F  -> F

		|Not(p1)-> Not(p1)

		|And(p1,p2)-> And((cnf_prop p1), (cnf_prop p2))

		|Or(And(p1,p2),p3)-> And((cnf_prop (Or(p1,p3))), (cnf_prop (Or(p2,p3))))

		|Or(p1,And(p2,p3))-> And((cnf_prop (Or(p1,p2))), (cnf_prop (Or(p1,p3))))

		|Or(p1,p2)-> if ((cnf_prop p1) = p1) && ((cnf_prop p2) = p2) then p else cnf_prop(Or((cnf_prop p1), (cnf_prop p2)))

		|_-> p;;


let rec dnf_prop p = match nnf p with
		
		P(x)-> P(x)
		
		|T  -> T
		
		|F  -> F
		
		|Not(p1)-> Not(p1)
		
		|Or(p1,p2)-> Or((dnf_prop p1), (dnf_prop p2))
		
		|And(Or(p1,p2),p3)-> Or((dnf_prop (And(p1,p3))), (dnf_prop (And(p2,p3))))
		
		|And(p1,Or(p2,p3))-> Or((dnf_prop (And(p1,p2))), (dnf_prop (And(p1,p3))))
		
		|And(p1,p2)-> if ((dnf_prop p1) = p1) && ((dnf_prop p2) = p2) then p else dnf_prop(And((dnf_prop p1), (dnf_prop p2)))

		|_-> p;;


let rec make_help p b s l = match p with
	T-> if b then 
			if l = T then s 
			else make_help (cnf_prop l) true s T 
		else []

	|F-> if b then [] 
		else if l = T then s 
			else make_help (cnf_prop l) true s T

	|P(x) -> if member (p,not b) s then [] 
			else 
				if l = T then
					if member (p,b) s then s 
					else (p,b)::s 
				else 
					if member (p,b) s then make_help (cnf_prop l) true s T
					else make_help (cnf_prop l) true ((p,b)::s) T

	|Not(p1) -> make_help p1 (not b) s l 

	|Or(p1,p2) -> let k1 = make_help p1 b s l in 
				if b then if (k1 = []) then make_help p2 b s l else k1
				else if (k1 =[]) then [] else make_help p2 b (union s k1) l

	|And(p1,p2)-> let k1 = make_help p1 b s l in 
				if not b then if (k1 = []) then make_help p2 b s l else k1
				else if (k1 =[]) then [] else make_help p2 b (union s k1) l

	|Implies(p1,p2)-> [];;


let make p b l= if b then make_help (cnf_prop p) b [] l else make_help (dnf_prop p) b [] l;;


let entails p1 p2 = ((make p2 false p1) = []);;


let isEquivalent p1 p2 = (entails p1 p2) && (entails p2 p1);;

(*Helper Functions (To be converted to let in form if it is required in only 1 function*)

let sequentmatch p s1 = let (ps, x) = s1 in match p with Ass((ps1, y))-> if equalset ps ps1 then (x=y) else false

		| TI((ps1, y))-> if equalset ps ps1 then (x=y)else false

		| FE((ps1, y))-> if equalset ps ps1 then (x=y)else false

		| ImpI(p1,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| ImpE(p1,p2,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| AndI(p1,p2,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| AndEleft(p1,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| AndEright(p1,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| OrIleft(p1,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| OrIright(p1,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| OrE(p1,p2,p3,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| NotClass(p1,(ps1, y))-> if equalset ps ps1 then (x=y)else false

		| NotIntu(p1,(ps1, y))-> if equalset ps ps1 then (x=y) else false;;



let rec sequentext p = match p with Ass(s)-> s

		| TI(s)-> s

		| FE(s)-> s

		| ImpI(p1,s)-> s

		| ImpE(p1,p2,s)-> s

		| AndI(p1,p2,s)-> s

		| AndEleft(p1,s)-> s

		| AndEright(p1,s)-> s

		| OrIleft(p1,s)-> s

		| OrIright(p1,s)-> s

		| OrE(p1,p2,p3,s)-> s

		| NotClass(p1,s)-> s

		| NotIntu(p1,s)-> s;;


(*Required Functions*)

let rec ht p = match p with Ass(s)-> 1

		| TI(s)-> 1

		| FE(s)-> 1

		| ImpI(p1,s)-> 1 + ht p1

		| ImpE(p1,p2,s)-> 1 + max (ht p1) (ht p2)

		| AndI(p1,p2,s)-> 1 + max (ht p1) (ht p2)

		| AndEleft(p1,s)-> 1 + ht p1

		| AndEright(p1,s)-> 1 + ht p1

		| OrIleft(p1,s)-> 1 + ht p1

		| OrIright(p1,s)-> 1 + ht p1

		| OrE(p1,p2,p3,s)-> 1+ max (max (ht p1) (ht p2)) (ht p3)

		| NotClass(p1,s)-> 1 + ht p1

		| NotIntu(p1,s)-> 1 + ht p1;;


let rec size p = match p with Ass(s)-> 1

		| TI(s)-> 1

		| FE(s)-> 1

		| ImpI(p1,s)-> 1 + size p1

		| ImpE(p1,p2,s)-> 1+ size p1 + size p2

		| AndI(p1,p2,s)-> 1+ size p1 + size p2

		| AndEleft(p1,s)-> 1 + size p1

		| AndEright(p1,s)-> 1 + size p1

		| OrIleft(p1,s)-> 1 + size p1

		| OrIright(p1,s)-> 1 + size p1

		| OrE(p1,p2,p3,s)-> 1+ size p1 + size p2 + size p3

		| NotClass(p1,s)-> 1 + size p1

		| NotIntu(p1,s)-> 1 + size p1;;


let rec wfprooftree p = match p with Ass((ps,s))-> member s ps

		| TI((ps,T))-> true

		| FE((ps,p))-> member F ps

		| ImpI(p1,(ps,(Implies(x,y))))-> if sequentmatch p1 ((x::ps), y) then wfprooftree p1 
										else false

		| ImpE(p1,p2,(ps,prop1)) -> let a,b = sequentext p1 in let c,d = sequentext p2 in 
										if b = (Implies(d,prop1))|| d = (Implies(b, prop1)) then
											if sequentmatch p1 (ps,b) && sequentmatch p2 (ps,d) then (wfprooftree p1) && (wfprooftree p2)
											else false
										else false

		| AndI(p1,p2,(ps,(And(x, y)))) -> if sequentmatch p1 (ps,x) && sequentmatch p2 (ps,y) then (wfprooftree p1) && (wfprooftree p2)
										else if sequentmatch p2 (ps,x) && sequentmatch p1 (ps,y) then (wfprooftree p1) && (wfprooftree p2)
										else false

		| AndEleft(p1,(ps,prop1))-> let a,b = sequentext p1 in
										begin
											match b with (And (k, _)) -> if k = prop1 then if sequentmatch p1 (ps,b) then (wfprooftree p1) else false
																		else false
														|_-> false
										end
		| AndEright(p1,(ps,prop1)) -> let a,b = sequentext p1 in
										begin
											match b with (And (_,k)) -> if k = prop1 then if sequentmatch p1 (ps,b) then (wfprooftree p1) else false
																		else false
														|_-> false
										end

		| OrIleft(p1,(ps,(Or(x,y)))) -> if sequentmatch p1 (ps,x) then wfprooftree p1 else false

		| OrIright(p1,(ps,(Or(x,y)))) -> if sequentmatch p1 (ps,y) then wfprooftree p1 else false

		| OrE(p1,p2,p3,(ps,prop1)) -> let a,b = sequentext p1 in let c,d = sequentext p2 in let e,f = sequentext p3 in
										if b != prop1 then 
											if f = d && f = prop1 && sequentmatch p1 (ps,b) then 
												begin
													match b with (Or(g, h))-> if sequentmatch p2 (g::ps,prop1) && sequentmatch p3 (h::ps,prop1) then (wfprooftree p3) && (wfprooftree p2) &&(wfprooftree p1)
																				else if sequentmatch p3 (g::ps,prop1) && sequentmatch p2 (h::ps,prop1) then (wfprooftree p3) && (wfprooftree p2) &&(wfprooftree p1)
																				else false

																|_-> false
												end
											else false
										else if d!= prop1 then 
											if b = f && b = prop1 && sequentmatch p2 (ps,d) then 
												begin
													match d with (Or(g, h))-> if sequentmatch p3 (g::ps,prop1) && sequentmatch p1 (h::ps,prop1) then (wfprooftree p3) && (wfprooftree p2) &&(wfprooftree p1)
																				else if sequentmatch p1 (g::ps,prop1) && sequentmatch p3 (h::ps,prop1) then (wfprooftree p3) && (wfprooftree p2) &&(wfprooftree p1)
																				else false
																				
																|_-> false
												end
											else false
										else if f != prop1 then 
											if b = d && b = prop1 && sequentmatch p3 (ps,f) then 
												begin
													match f with (Or(g, h))-> if sequentmatch p2 (g::ps,prop1) && sequentmatch p1 (h::ps,prop1) then (wfprooftree p3) && (wfprooftree p2) &&(wfprooftree p1)
																				else if sequentmatch p1 (g::ps,prop1) && sequentmatch p2 (h::ps,prop1) then (wfprooftree p3) && (wfprooftree p2) &&(wfprooftree p1)
																				else false
																				
																|_-> false
												end
											else false
										else false
					
		| NotClass(p1,(ps,prop1)) -> let a,b = sequentext p1 in
										if b = F then
											if sequentmatch p1 ((Not(prop1))::ps,F) then (wfprooftree p1) else false
										else false

		| NotIntu(p1,(ps,prop1)) -> if sequentmatch p1 (ps,F) then (wfprooftree p1) else false

		| _ -> false;;

exception InvalidProofTree;;
let rec pad (pt:prooftree) (ass: prop set) = match pt with Ass((ps,s))-> Ass(((union ps ass),s))

		| TI((ps,T))-> TI(((union ps ass),T))

		| FE((ps,p))-> FE(((union ps ass),p))

		| ImpI(p1,(ps,s))-> ImpI((pad p1 ass),((union ps ass),s))

		| ImpE(p1,p2,(ps,s)) -> ImpE((pad p1 ass),(pad p2 ass),((union ps ass),s))

		| AndI(p1,p2,(ps,s)) -> AndI((pad p1 ass),(pad p2 ass),((union ps ass),s))

		| AndEleft(p1,(ps,s))-> AndEleft((pad p1 ass),((union ps ass),s))

		| AndEright(p1,(ps,s)) -> AndEright((pad p1 ass),((union ps ass),s))

		| OrIleft(p1,(ps,s)) -> OrIleft((pad p1 ass),((union ps ass),s))

		| OrIright(p1,(ps,s)) -> OrIright((pad p1 ass),((union ps ass),s))

		| OrE(p1,p2,p3,(ps,s)) -> OrE((pad p1 ass),(pad p2 ass),(pad p3 ass),((union ps ass),s))
					
		| NotClass(p1,(ps,s)) -> NotClass((pad p1 ass),((union ps ass),s))

		| NotIntu(p1,(ps,s)) -> NotIntu((pad p1 ass),((union ps ass),s))

		| _-> raise InvalidProofTree;;


let pare_1 pf = let rec pare_help (pt:prooftree) req = match pt with Ass((ps,s))->if member s req then Ass((req,s)) else Ass((s::req,s))
		
		| TI((ps,T))-> TI((req,T))

		| FE((ps,p))-> if member F req then FE((req,p)) else FE((F::req,p))

		| ImpI(p1,(ps,(Implies(x,y))))-> if member x req then ImpI((pare_help p1 req), (req, (Implies(x,y)))) else ImpI((pare_help p1 (x::req)), (req, (Implies(x,y))))

		| ImpE(p1,p2,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in let (a2,b2) = sequentext (pare_help p2 req) in ImpE((pad (pare_help p1 req) a2),(pad (pare_help p2 req) a1),((union a1 a2), prop1))

		| AndI(p1,p2,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in let (a2,b2) = sequentext (pare_help p2 req) in AndI((pad (pare_help p1 req) a2),(pad (pare_help p2 req) a1),((union a1 a2), prop1))

		| AndEleft(p1,(ps,prop1))-> let (a1,b1) = sequentext (pare_help p1 req) in AndEleft((pare_help p1 req),(a1, prop1))

		| AndEright(p1,(ps,prop1)) ->  let (a1,b1) = sequentext (pare_help p1 req) in AndEright((pare_help p1 req),(a1, prop1))

		| OrIleft(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in OrIleft((pare_help p1 req),(a1, prop1))

		| OrIright(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in OrIright((pare_help p1 req),(a1, prop1))

		| OrE(p1,p2,p3,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in let (a2,b2) = sequentext (pare_help p2 req) in let (a3,b3) = sequentext (pare_help p3 req) in 
													OrE((pad (pare_help p1 req) (union a2 a3)),(pad (pare_help p2 req) (union a1 a3)),(pad (pare_help p3 req) (union a1 a2)),((union (union a1 a2) a3), prop1))

		| NotClass(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in NotClass((pare_help p1 req),(a1, prop1))

		| NotIntu(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in NotIntu((pare_help p1 req),(a1, prop1))

		| _ -> raise InvalidProofTree in

		pare_help pf [];;


let rec pare_2 pt = match pt with Ass((ps,s))->if member s req then Ass((req,s)) else Ass((s::req,s))
		
		| TI((ps,T))-> TI((req,T))

		| FE((ps,p))-> if member F req then FE((req,p)) else FE((F::req,p))

		| ImpI(p1,(ps,(Implies(x,y))))-> let ps1,s1 = sequentext (pare_2 p1) in ImpI((pare_2 p1), (ps1,(Implies(x,y))))

		| ImpE(p1,p2,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in let (a2,b2) = sequentext (pare_help p2 req) in ImpE((pad (pare_help p1 req) a2),(pad (pare_help p2 req) a1),((union a1 a2), prop1))

		| AndI(p1,p2,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in let (a2,b2) = sequentext (pare_help p2 req) in AndI((pad (pare_help p1 req) a2),(pad (pare_help p2 req) a1),((union a1 a2), prop1))

		| AndEleft(p1,(ps,prop1))-> let (a1,b1) = sequentext (pare_help p1 req) in AndEleft((pare_help p1 req),(a1, prop1))

		| AndEright(p1,(ps,prop1)) ->  let (a1,b1) = sequentext (pare_help p1 req) in AndEright((pare_help p1 req),(a1, prop1))

		| OrIleft(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in OrIleft((pare_help p1 req),(a1, prop1))

		| OrIright(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in OrIright((pare_help p1 req),(a1, prop1))

		| OrE(p1,p2,p3,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in let (a2,b2) = sequentext (pare_help p2 req) in let (a3,b3) = sequentext (pare_help p3 req) in 
													OrE((pad (pare_help p1 req) (union a2 a3)),(pad (pare_help p2 req) (union a1 a3)),(pad (pare_help p3 req) (union a1 a2)),((union (union a1 a2) a3), prop1))

		| NotClass(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in NotClass((pare_help p1 req),(a1, prop1))

		| NotIntu(p1,(ps,prop1)) -> let (a1,b1) = sequentext (pare_help p1 req) in NotIntu((pare_help p1 req),(a1, prop1))

		| _ -> raise InvalidProofTree in

		pare_help pf [];;


let rec graft_help pt1 pt2 = let g,h = sequentext pt2 in match pt1 with Ass((ps,s))-> if s=h then pt2 else pt1

		| TI((ps,T))-> TI(((union (difference ps [h]) g),T))

		| FE((ps,p))-> FE(((union (difference ps [h]) g),p))

		| ImpI(p1,(ps,s))-> ImpI((graft_help p1 pt2),((union (difference ps [h]) g),s))

		| ImpE(p1,p2,(ps,s)) -> ImpE((graft_help p1 pt2),(graft_help p2 pt2),((union (difference ps [h]) g),s))

		| AndI(p1,p2,(ps,s)) -> AndI((graft_help p1 pt2),(graft_help p2 pt2),((union (difference ps [h]) g),s))

		| AndEleft(p1,(ps,s))-> AndEleft((graft_help p1 pt2),((union (difference ps [h]) g),s))

		| AndEright(p1,(ps,s)) -> AndEright((graft_help p1 pt2),((union (difference ps [h]) g),s))

		| OrIleft(p1,(ps,s)) -> OrIleft((graft_help p1 pt2),((union (difference ps [h]) g),s))

		| OrIright(p1,(ps,s)) -> OrIright((graft_help p1 pt2),((union (difference ps [h]) g),s))

		| OrE(p1,p2,p3,(ps,s)) -> OrE((graft_help p1 pt2),(graft_help p2 pt2),(graft_help p3 pt2),((union (difference ps [h]) g),s))
					
		| NotClass(p1,(ps,s)) -> NotClass((graft_help p1 pt2),((union (difference ps [h]) g),s))

		| NotIntu(p1,(ps,s)) -> NotIntu((graft_help p1 pt2),((union (difference ps [h]) g),s))

		| _-> raise InvalidProofTree;;


let rec graft (pt:prooftree) (pts:prooftree set) = match pts with []-> pt

		|x::xs -> graft (graft_help pt x) xs;;


let rec normalise (pt:prooftree) = match pt with Ass((ps,s))-> pt

		| TI((ps,T))-> pt

		| FE((ps,p))-> pt

		| ImpI(p1,p) -> ImpI((normalise p1), p) 

		| ImpE(ImpI(p1,(ps2,s2)),p2,(ps1,s1)) -> let ps3,s3 = sequentext p2 in if sequentmatch p1 ((union ps1 [s3]),s1) then graft_help p1 p2 else ImpE((normalise (ImpI(p1,(ps2,s2)))),(normalise p2),(ps1,s1))

		| ImpE(p1,ImpI(p2,(ps2,s2)),(ps1,s1)) -> let ps3,s3 = sequentext p1 in if sequentmatch p2 ((union ps1 [s3]),s1) then graft_help p2 p1 else ImpE((normalise p1),(normalise (ImpI(p2,(ps2,s2)))),(ps1,s1))

		| ImpE(p1,p2,p)-> ImpE((normalise p1), (normalise p2), p)

		| AndI(p1,p2,(ps,s)) -> AndI((normalise p1),(normalise p2), (ps,s))

		| AndEleft((AndI(p1,p2,(ps2,s2))),(ps1,s1))-> if sequentext(p1) = (ps1,s1) then normalise p1 else AndEleft((normalise (AndI(p1,p2,(ps2,s2)))),(ps1,s1))

		| AndEleft(p1,(ps,s))-> AndEleft((normalise p1),(ps,s))

		| AndEright((AndI(p1,p2,(ps2,s2))),(ps1,s1))-> if sequentext(p2) = (ps1,s1) then normalise p2 else AndEright((normalise (AndI(p1,p2,(ps2,s2)))),(ps1,s1)) 

		| AndEright(p1,(ps,s))-> AndEright((normalise p1),(ps,s))

		| OrIleft(p1,(ps,s)) -> OrIleft((normalise p1),(ps,s))

		| OrIright(p1,(ps,s)) -> OrIright((normalise p1),(ps,s))

		| OrE(OrIleft(p1,(ps1,s1)),p2,p3,(ps,s)) -> let (ps2,s2) = sequentext(p2) in let (ps3,s3) = sequentext(p3) in 
															if ((member s1 ps2) && (sequentmatch p2 (s1::ps1,s))) then normalise (graft_help p2 p1)
															else if  ((member s1 ps3) && (sequentmatch p3 (s1::ps1,s))) then normalise (graft_help p3 p1)
															else OrE((normalise (OrIleft(p1,(ps1,s1)))),(normalise p2),(normalise p3),(ps,s))

		| OrE(p2,OrIleft(p1,(ps1,s1)),p3,(ps,s)) ->let (ps2,s2) = sequentext(p2) in let (ps3,s3) = sequentext(p3) in 
															if ((member s1 ps2) && (sequentmatch p2 (s1::ps1,s))) then normalise (graft_help p2 p1)
															else if  ((member s1 ps3) && (sequentmatch p3 (s1::ps1,s))) then normalise (graft_help p3 p1)
															else OrE((normalise p2),(normalise (OrIleft(p1,(ps1,s1)))),(normalise p3),(ps,s))

		| OrE(p2,p3,OrIleft(p1,(ps1,s1)),(ps,s)) -> let (ps2,s2) = sequentext(p2) in let (ps3,s3) = sequentext(p3) in 
															if ((member s1 ps2) && (sequentmatch p2 (s1::ps1,s))) then normalise (graft_help p2 p1)
															else if  ((member s1 ps3) && (sequentmatch p3 (s1::ps1,s))) then normalise (graft_help p3 p1)
															else OrE((normalise p2),(normalise p3),(normalise (OrIleft(p1,(ps1,s1)))),(ps,s))

		| OrE(OrIright(p1,(ps1,s1)),p2,p3,(ps,s)) -> let (ps2,s2) = sequentext(p2) in let (ps3,s3) = sequentext(p3) in 
															if ((member s1 ps2) && (sequentmatch p2 (s1::ps1,s))) then normalise (graft_help p2 p1)
															else if  ((member s1 ps3) && (sequentmatch p3 (s1::ps1,s))) then normalise (graft_help p3 p1)
															else OrE((normalise (OrIright(p1,(ps1,s1)))),(normalise p2),(normalise p3),(ps,s))

		| OrE(p2,OrIright(p1,(ps1,s1)),p3,(ps,s)) ->let (ps2,s2) = sequentext(p2) in let (ps3,s3) = sequentext(p3) in 
															if ((member s1 ps2) && (sequentmatch p2 (s1::ps1,s))) then normalise (graft_help p2 p1)
															else if  ((member s1 ps3) && (sequentmatch p3 (s1::ps1,s))) then normalise (graft_help p3 p1)
															else OrE((normalise p2),(normalise (OrIright(p1,(ps1,s1)))),(normalise p3),(ps,s))

		| OrE(p2,p3,OrIright(p1,(ps1,s1)),(ps,s)) -> let (ps2,s2) = sequentext(p2) in let (ps3,s3) = sequentext(p3) in 
															if ((member s1 ps2) && (sequentmatch p2 (s1::ps1,s))) then normalise (graft_help p2 p1)
															else if  ((member s1 ps3) && (sequentmatch p3 (s1::ps1,s))) then normalise (graft_help p3 p1)
															else OrE((normalise p2),(normalise p3),(normalise (OrIright(p1,(ps1,s1)))),(ps,s))

		| OrE(p1,p2,p3,(ps,s)) -> OrE((normalise p1),(normalise p2),(normalise p3),(ps,s))
					
		| NotClass(p1,(ps,s)) -> NotClass((normalise p1), (ps,s))

		| NotIntu(p1,(ps,s)) ->  NotIntu((normalise p1), (ps,s))

		| _ -> raise InvalidProofTree;;


let pare pt = pare_1 pt;;


(*GIVEN TEST CASES*)
let gamma = [P "p2";P "p1";P "p3"];;
let gamma2 = [And (P "p",P "q");Or (P "p2",P "q2")];;

let test_tree1 = Ass (gamma ,P "p1") ;;
let test_tree2 = Ass (gamma ,P "p2") ;;
let test_tree3 = AndI (test_tree1,test_tree2,(gamma,(And (P "p1",P "p2"))));;
let test_tree4 = AndEleft (test_tree3,(gamma,P "p2"));;

let test_fE    = FE (F::gamma,P "p1");;


let test_tree5 = Ass (gamma2,And (P "p",P "q")) ;;
let test_tree6 = ImpI (test_tree5,([Or (P "p2",P "q2")],Implies (And (P "p",P "q"),And (P "p",P "q"))));;
let gamma3 = [P "a"; P "b"];;
let tq1 = Ass (gamma3,P "a");;
let tq2 = Ass (gamma3,P "b");;
let q1 = AndI (tq1, tq2, (gamma3,(And (P "a",P "b"))));;
let q2 = OrIleft (tq2, (gamma3,(Or(P "b",P "c"))));;

let delta1 = [And (P "a",P "b")];;
let tp1 = Ass (delta1,(And (P "a",P "b")));;
let p = AndEleft (tp1,(delta1, (P "a")));;

let tree_nor = AndEleft (q1,(gamma3,P "a"));;

wfprooftree test_tree4;;
wfprooftree test_fE;;
pad test_tree4 [P "p3";P "p4"];;
pare test_tree6;;
graft p [q1;q2];;
normalise tree_nor;;


let p1 = (Not(And((P("1")),(P("2")))));;
let p2 = (And((P "1"),(P "2")));;
let p3 = (Or((P "3"),(P "4")));;
let p4 = (Or((And((P "1"),(P "2"))),(Or((P "3"),(P "4")))));;
let p5 = (Not(And((Or(((And((P "1"),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;
let p6 = (Implies((And((Implies((P "1"),(P "2"))),(P "1"))),(P "2")));;
let p7 = (And((Not(Implies((P("1")),(P("2"))))),(Implies((Or((Not(And((P("3")),(And((Or((P("2")),(T))),(F)))))),(Implies((P("4")),(P("5")))))),(And((P("6")),(Or((P("7")),(P("8"))))))))));;



let g = [p3;(Implies(p3,p2));p4;And(p5,p7);Or(p3,p6);p7;F];;
let ps = [p3;(Implies(p3,p2));p4;And(p5,p7);Or(p3,p6);p7;F];;
wfprooftree (Ass(ps,p4));;(*Assumption*)
wfprooftree (ImpE((Ass(g, (Implies(p3,p2)))),(Ass(ps,p3)),(ps,p2)));;(*Implies elimination*)
wfprooftree (AndI((Ass(ps,p4)),(Ass(ps,p3)),(g,(And(p3,p4)))));;(*And Introduction *)
wfprooftree (AndEleft((Ass(ps,And(p5,p7))),(ps,p5)));;
wfprooftree (AndEright((Ass(ps,And(p5,p7))),(ps,p7)));;
wfprooftree (OrIright((Ass(ps,p4)),(ps,Or(p1,p4))));;
wfprooftree (OrIleft((Ass(ps,p3)),(ps,Or(p3,p1))));;
wfprooftree (OrE((Ass(p6::ps,p7)),(Ass(p3::ps,p7)),(Ass(ps,Or(p3,p6))),(ps,p7)));;
wfprooftree (NotClass((Ass((Not(p1))::g, F)),(ps,p1)));;

pad tree_nor [P "1";T];;

pare test_tree5;;




















