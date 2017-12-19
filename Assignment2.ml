type prop = P of string | T | F

    | Not of prop | And of prop * prop

    | Or of prop * prop | Implies of prop * prop;;

 (*Defined class prop as told in the assignment*)


(*Assignment 2*)

(*height function tells us the height of the operator tree. It is a recursive addition with maximum height of two branches created in and, or & implies case *)
let rec height p = match p with
T->0|F->0|P(x)->0
|Not(p1) -> 1 + height p1
|And(p1,p2)-> 1 + max (height p1) (height p2)
|Or(p1,p2) -> 1 + max (height p1) (height p2)
|Implies(p1,p2)-> 1 + max (height p1) (height p2);;

(*Size function tells us the number of nodes in the operator tree. It is recursive addition with sum of both branches taken in cases of and, or & implies*)
let rec size p = match p with 
T->1|F->1|P(x)->1
|Not(p1) -> 1 + size p1
|And(p1,p2)-> 1 + (size p1) + (size p2)
|Or(p1,p2) -> 1 + (size p1) + (size p2)
|Implies(p1,p2)-> 1 + (size p1) + (size p2);;

(*Set function member and union retaken from previous assignment(Assignment1)*)
let rec member x s1= match s1 with
[]-> false
|y::ys -> if (x = y) then true else member x ys;;

let union s1 s2 = let rec union1 s1 s2 s3 = match s1 with
[]-> s3
|x::xs-> if member x s2 then union1 xs s2 s3 else union1 xs s2 (x::s3) in union1 s1 s2 s2;;

(*Returns a list of propositional primitives(T,F,p of i) that occur in a proposition *)
let rec letters p = match p with
T->[]|F->[]
|P(x)-> [p]
|Not(p1) -> letters p1
|And(p1,p2)-> union (letters p1) (letters p2)
|Or(p1,p2)->union (letters p1) (letters p2)
|Implies(p1,p2)->union (letters p1) (letters p2);;

(*Defines the truth value of p w.r.t. a given function rho*)
let rec truth p rho = match p with
T->true
|F->false
|P(n)->rho n
|Not(p1)-> not (truth p1 rho)
|And(p1,p2)-> (truth p1 rho) && (truth p2 rho)
|Or(p1,p2)-> (truth p1 rho) || (truth p2 rho)
|Implies(p1,p2)-> if (truth p1 rho) then (truth p2 rho) else true;;)

(*Converts a proposition to its non negative form*)
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

(*  Testing nnf function
nnf (Not(And((P("1")),(P("2")))));;
nnf (And((P "1"),(P "2")));;
nnf (Or((P "3"),(P "4")));;
nnf (Or(((And((P "1"),(P "2")))),((Or((P "3"),(P "4"))))));;
nnf (Not(And((Or(((And((P "1"),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;*)

(*Converts a proposition to conjunction of disjunction proposition*)
let rec cnf_prop p = match nnf p with
P(x)-> P(x)
|T  -> T
|F  -> F
|Not(p1)-> Not(p1)
|And(p1,p2)-> And((cnf_prop p1), (cnf_prop p2))
|Or(And(p1,p2),p3)-> And((cnf_prop (Or(p1,p3))), (cnf_prop (Or(p2,p3))))
|Or(p1,And(p2,p3))-> And((cnf_prop (Or(p1,p2))), (cnf_prop (Or(p1,p3))))
|Or(p1,p2)-> if ((cnf_prop p1) = p1) && ((cnf_prop p2) = p2) then p else cnf_prop(Or((cnf_prop p1), (cnf_prop p2)));;

(*Converts a cnf form proposition to a set of set of propositions (conjunction of disjunction of sets*)
let rec cnf p = match cnf_prop p with 
And(p1,p2)-> union (cnf p1) (cnf p2)
|Or(p1,p2)-> let x::xs = cnf p1 in let y::ys = cnf p2 in [union x y]
|_->[[p]];;

(*cnf_prop (Not(And((Or(((And((Implies((P "1"),(P "3"))),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;
cnf (Not(And((Or(((And((Implies((P "1"),(P "3"))),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;*)

(*Converts a proposition into its disjunctive normal form which is disjunction of conjunctions of propositions*)
let rec dnf_prop p = match nnf p with
P(x)-> P(x)
|T  -> T
|F  -> F
|Not(p1)-> Not(p1)
|Or(p1,p2)-> Or((dnf_prop p1), (dnf_prop p2))
|And(Or(p1,p2),p3)-> Or((dnf_prop (And(p1,p3))), (dnf_prop (And(p2,p3))))
|And(p1,Or(p2,p3))-> Or((dnf_prop (And(p1,p2))), (dnf_prop (And(p1,p3))))
|And(p1,p2)-> if ((dnf_prop p1) = p1) && ((dnf_prop p2) = p2) then p else dnf_prop(And((dnf_prop p1), (dnf_prop p2)));;

(*Converts dnf proposition to set of seta*)
let rec dnf p = match dnf_prop p with 
Or(p1,p2)-> union (dnf p1) (dnf p2)
|And(p1,p2)-> let x::xs = dnf p1 in let y::ys = dnf p2 in [union x y]
|_->[[p]];;

(*dnf_prop (Not(And((Or(((And((Implies((P "1"),(P "3"))),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;
dnf (Not(And((Or(((And((Implies((P "1"),(P "3"))),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;
dnf (And((P "1"),Not((P "1"))));;
dnf (Implies((And((Implies((P "1"),(P "2"))),(P "1"))),(P "2")));;
cnf (Implies((And((Implies((P "1"),(P "2"))),(P "1"))),(P "2")));;*)

(*make gives a possible path to make p true or false as given in argument b if the 4th argument l is T
If l is not T then after making p true given the same set of propositional requirements we try to make l true
This can be extended to a set of proposition entails p by changing l to a list of propositions, popping their head and releasing answer when it is empty*)
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

(*make ((Not(And((Or(((And((Implies((P "1"),(P "3"))),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))))) true T;;
make ((And((Or((P "1"),(P "2"))),(And((Not(P "1")),(Not(P "2"))))))) true T;;*)

(*If there is no way of making a proposition false, then the proposition is always true*)
let isTautology p = (make p false T) = [];;

(*isTautology (Implies((And((Implies((P "1"),(P "2"))),(P "1"))),(P "2")));;
isTautology (Not(And((Or((P "1"),(P "2"))),(And((Not(P "1")),(Not(P "2")))))));;*)

(*If there is no way of making proposition true, then it is a contradiction*)
let isContradiction p = (make p true T) = [];;

(*If the proposition is not always false then there is a way of making it true*)
let isSatisfiable p = not (isContradiction p);;

(*isSatisfiable (Not(And((Or(((And((Implies((P "1"),(P "3"))),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;
isSatisfiable (And((Or((P "1"),(P "2"))),(And((Not(P "1")),(Not(P "2"))))));;*)

(*try to make p2 false and then if there is a way then make p1 true with the same conditions*)
let entails p1 p2 = ((make p2 false p1) = []);;

(*entails (And((P "1"),P("2"))) (And((P "1"),P("2")));;*)

(*if p1 entails p2 and p2 entails p1 then they are equivalent*)
let isEquivalent p1 p2 = (entails p1 p2) && (entails p2 p1);;

(*Some random rho functions for verification*)
let rho1 p = match p with
"1" -> false
|"2"-> false
|"3" -> true
|"4"-> false
|"5" -> true
|"6"-> true
|"7" -> true
|"8"-> true
|_->true;;

let rho2 p = match p with
"1" -> true
|"2"-> false
|"3" -> true
|"4"-> false
|"5" -> true
|"6"-> false
|"7" -> true
|"8"-> false
|_->true;;

let rho3 p = match p with
"1" -> true
|"2"-> true
|"3" -> true
|"4"-> true
|"5" -> false
|"6"-> false
|"7" -> false
|"8"-> false
|_->true;;

let rho4 p = match p with
"1" -> false
|"2"-> false
|"3" -> true
|"4"-> true
|"5" -> false
|"6"-> false
|"7" -> true
|"8"-> true
|_->true;;

let rho5 p = match p with
"1" -> false
|"2"-> true
|"3" -> false
|"4"-> false
|"5" -> false
|"6"-> true
|"7" -> true
|"8"-> true
|_->true;;

let rho6 p = match p with
"1" -> true
|"2"-> true
|"3" -> true
|"4"-> false
|"5" -> false
|"6"-> false
|"7" -> true
|"8"-> false
|_->true;;

let p1 = (Not(And((P("1")),(P("2")))));;
let p2 = (And((P "1"),(P "2")));;
let p3 = (Or((P "3"),(P "4")));;
let p4 = (Or((And((P "1"),(P "2"))),(Or((P "3"),(P "4")))));;
let p5 = (Not(And((Or(((And((P "1"),(P "2")))),((Or((P "3"),(P "4")))))),(P "5"))));;
let p6 = (Implies((And((Implies((P "1"),(P "2"))),(P "1"))),(P "2")));;
let p7 = (And((Not(Implies((P("1")),(P("2"))))),(Implies((Or((Not(And((P("3")),(And((Or((P("2")),(T))),(F)))))),(Implies((P("4")),(P("5")))))),(And((P("6")),(Or((P("7")),(P("8"))))))))));;

"nnf, cnf, dnf Test Cases"
"case 1";;

isEquivalent p1 (nnf p1);;
isEquivalent p1 (cnf_prop p1);;
isEquivalent p1 (dnf_prop p1);;

"case 1.1";;

truth p1 rho1;;
truth (nnf p1) rho1;;
truth (cnf_prop p1) rho1;;
truth (dnf_prop p1) rho1;;

"case 1.2";;

truth p1 rho3;;
truth (nnf p1) rho3;;
truth (cnf_prop p1) rho3;;
truth (dnf_prop p1) rho3;;

"case 1.3";;

truth p1 rho5;;
truth (nnf p1) rho5;;
truth (cnf_prop p1) rho5;;
truth (dnf_prop p1) rho5;;

"case 1.4";;

truth p1 rho2;;
truth (nnf p1) rho2;;
truth (cnf_prop p1) rho2;;
truth (dnf_prop p1) rho2;;

"case 1.5";;

truth p1 rho4;;
truth (nnf p1) rho4;;
truth (cnf_prop p1) rho4;;
truth (dnf_prop p1) rho4;;

"case 1.6";;

truth p1 rho6;;
truth (nnf p1) rho6;;
truth (cnf_prop p1) rho6;;
truth (dnf_prop p1) rho6;;

"case 2";;

isEquivalent p2 (nnf p2);;
isEquivalent p2 (cnf_prop p2);;
isEquivalent p2 (dnf_prop p2);;

"case 2.1";;

truth p2 rho2;;
truth (nnf p2) rho2;;
truth (cnf_prop p2) rho2;;
truth (dnf_prop p2) rho2;;

"case 2.2";;

truth p2 rho4;;
truth (nnf p2) rho4;;
truth (cnf_prop p2) rho4;;
truth (dnf_prop p2) rho4;;

"case 2.3";;

truth p2 rho6;;
truth (nnf p2) rho6;;
truth (cnf_prop p2) rho6;;
truth (dnf_prop p2) rho6;;


"case 2.4";;

truth p1 rho1;;
truth (nnf p1) rho1;;
truth (cnf_prop p1) rho1;;
truth (dnf_prop p1) rho1;;

"case 2.5";;

truth p1 rho3;;
truth (nnf p1) rho3;;
truth (cnf_prop p1) rho3;;
truth (dnf_prop p1) rho3;;

"case 2.6";;

truth p1 rho5;;
truth (nnf p1) rho5;;
truth (cnf_prop p1) rho5;;
truth (dnf_prop p1) rho5;;

"case 3";;

isEquivalent p3 (nnf p3);;
isEquivalent p3 (cnf_prop p3);;
isEquivalent p3 (dnf_prop p3);;

"case 3.1";;

truth p3 rho1;;
truth (nnf p3) rho1;;
truth (cnf_prop p3) rho1;;
truth (dnf_prop p3) rho1;;

"case 3.2";;

truth p3 rho3;;
truth (nnf p3) rho3;;
truth (cnf_prop p3) rho3;;
truth (dnf_prop p3) rho3;;

"case 3.3";;

truth p3 rho5;;
truth (nnf p3) rho5;;
truth (cnf_prop p3) rho5;;
truth (dnf_prop p3) rho5;;

"case 3.4";;

truth p3 rho2;;
truth (nnf p3) rho2;;
truth (cnf_prop p3) rho2;;
truth (dnf_prop p3) rho2;;

"case 3.5";;

truth p3 rho4;;
truth (nnf p3) rho4;;
truth (cnf_prop p3) rho4;;
truth (dnf_prop p3) rho4;;

"case 3.6";;

truth p3 rho6;;
truth (nnf p3) rho6;;
truth (cnf_prop p3) rho6;;
truth (dnf_prop p3) rho6;;

"case 4";;

isEquivalent p4 (nnf p4);;
isEquivalent p4 (cnf_prop p4);;
isEquivalent p4 (dnf_prop p4);;

"case 4.1";;

truth p4 rho1;;
truth (nnf p4) rho1;;
truth (cnf_prop p4) rho1;;
truth (dnf_prop p4) rho1;;

"case 4.2";;

truth p4 rho3;;
truth (nnf p4) rho3;;
truth (cnf_prop p4) rho3;;
truth (dnf_prop p4) rho3;;

"case 4.3";;

truth p4 rho5;;
truth (nnf p4) rho5;;
truth (cnf_prop p4) rho5;;
truth (dnf_prop p4) rho5;;

"case 4.4";;

truth p4 rho2;;
truth (nnf p4) rho2;;
truth (cnf_prop p4) rho2;;
truth (dnf_prop p4) rho2;;

"case 4.5";;

truth p4 rho4;;
truth (nnf p4) rho4;;
truth (cnf_prop p4) rho4;;
truth (dnf_prop p4) rho4;;

"case 4.6";;

truth p4 rho6;;
truth (nnf p4) rho6;;
truth (cnf_prop p4) rho6;;
truth (dnf_prop p4) rho6;;

"case 5";;

isEquivalent p5 (nnf p5);;
isEquivalent p5 (cnf_prop p5);;
isEquivalent p5 (dnf_prop p5);;

"case 5.1";;

truth p5 rho1;;
truth (nnf p5) rho1;;
truth (cnf_prop p5) rho1;;
truth (dnf_prop p5) rho1;;

"case 5.2";;

truth p5 rho3;;
truth (nnf p5) rho3;;
truth (cnf_prop p5) rho3;;
truth (dnf_prop p5) rho3;;

"case 5.3";;

truth p5 rho5;;
truth (nnf p5) rho5;;
truth (cnf_prop p5) rho5;;
truth (dnf_prop p5) rho5;;

"case 5.4";;

truth p5 rho2;;
truth (nnf p5) rho2;;
truth (cnf_prop p5) rho2;;
truth (dnf_prop p5) rho2;;

"case 5.5";;

truth p5 rho4;;
truth (nnf p5) rho4;;
truth (cnf_prop p5) rho4;;
truth (dnf_prop p5) rho4;;

"case 5.6";;

truth p5 rho6;;
truth (nnf p5) rho6;;
truth (cnf_prop p5) rho6;;
truth (dnf_prop p5) rho6;;

"case 6";;

isEquivalent p6 (nnf p6);;
isEquivalent p6 (cnf_prop p6);;
isEquivalent p6 (dnf_prop p6);;

"case 6.1";;

truth p6 rho1;;
truth (nnf p6) rho1;;
truth (cnf_prop p6) rho1;;
truth (dnf_prop p6) rho1;;

"case 6.2";;

truth p6 rho3;;
truth (nnf p6) rho3;;
truth (cnf_prop p6) rho3;;
truth (dnf_prop p6) rho3;;

"case 6.3";;

truth p6 rho5;;
truth (nnf p6) rho5;;
truth (cnf_prop p6) rho5;;
truth (dnf_prop p6) rho5;;

"case 6.4";;

truth p6 rho2;;
truth (nnf p6) rho2;;
truth (cnf_prop p6) rho2;;
truth (dnf_prop p6) rho2;;

"case 6.5";;

truth p6 rho4;;
truth (nnf p6) rho4;;
truth (cnf_prop p6) rho4;;
truth (dnf_prop p6) rho4;;

"case 6.6";;

truth p6 rho6;;
truth (nnf p6) rho6;;
truth (cnf_prop p6) rho6;;
truth (dnf_prop p6) rho6;;

"case 7";;

isEquivalent p7 (nnf p7);;
isEquivalent p7 (cnf_prop p7);;
isEquivalent p7 (dnf_prop p7);;

"case 7.1";;

truth p7 rho1;;
truth (nnf p7) rho1;;
truth (cnf_prop p7) rho1;;
truth (dnf_prop p7) rho1;;

"case 7.2";;

truth p7 rho3;;
truth (nnf p7) rho3;;
truth (cnf_prop p7) rho3;;
truth (dnf_prop p7) rho3;;

"case 7.3";;

truth p7 rho5;;
truth (nnf p7) rho5;;
truth (cnf_prop p7) rho5;;
truth (dnf_prop p7) rho5;;

"case 7.4";;

truth p7 rho2;;
truth (nnf p7) rho2;;
truth (cnf_prop p7) rho2;;
truth (dnf_prop p7) rho2;;

"case 7.5";;

truth p7 rho4;;
truth (nnf p7) rho4;;
truth (cnf_prop p7) rho4;;
truth (dnf_prop p7) rho4;;

"case 7.6";;

truth p7 rho6;;
truth (nnf p7) rho6;;
truth (cnf_prop p7) rho6;;
truth (dnf_prop p7) rho6;;

"Tautology of cnf, dnf, nnf tests";;

isTautology (Implies (p1, (cnf_prop p1)));;
isTautology (Implies (p1, (nnf p1)));;
isTautology (Implies (p1, (dnf_prop p1)));;

isTautology (Implies (p2, (cnf_prop p2)));;
isTautology (Implies (p2, (nnf p2)));;
isTautology (Implies (p2, (dnf_prop p2)));;

isTautology (Implies (p3, (cnf_prop p3)));;
isTautology (Implies (p3, (nnf p3)));;
isTautology (Implies (p3, (dnf_prop p3)));;

isTautology (Implies (p4, (cnf_prop p4)));;
isTautology (Implies (p4, (nnf p4)));;
isTautology (Implies (p4, (dnf_prop p4)));;

isTautology (Implies (p5, (cnf_prop p5)));;
isTautology (Implies (p5, (nnf p5)));;
isTautology (Implies (p5, (dnf_prop p5)));;

isTautology (Implies (p6, (cnf_prop p6)));;
isTautology (Implies (p6, (nnf p6)));;
isTautology (Implies (p6, (dnf_prop p6)));;

isTautology (Implies (p7, (cnf_prop p7)));;
isTautology (Implies (p7, (nnf p7)));;
isTautology (Implies (p7, (dnf_prop p7)));;

(*"Proof of if entails p1 p2 then isTautology (Implies p1 p2)";;
entails p1 p2 = (make p2 false p1 = [])
=> there is no way of making p2 false and p1 true at the same time.
=> if p1 is false then Implies p1 p2 is true, we are done
   if p1 is true, p2 cannot be false and is thus true, we are done.
   Thus if entails p1 p2 then Implies p1 p2 is always true=> Tautology 
*)






























