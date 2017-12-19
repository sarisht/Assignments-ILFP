(*ASSIGNMENT 1.a- SET RESPRESENTATION BY LIST*)

(*---------------BASIC FUNCTIONS THAT MAY GET USED----------------------*)
let rec map f lst = match lst with
[]->[]
|x::xs -> f(x)::(map f xs);;

let rec filter f lst = match lst with 
[]-> []
|x::xs -> if f(x) then x::(filter f xs) else filter f xs;;

let rec fold f e lst = match lst with 
[]-> []
|x::xs -> fold f (f e x) xs;;

exception UnequalLists;;
let rec zip s1 s2 = match s1,s2 with
([],[])-> []
|([],_) -> raise UnequalLists
|(_,[])-> raise UnequalLists
|(x::xs, y::ys)->(x,y)::(zip xs ys);;

(*Representational invariant: list without duplicates*)
module A1 = struct
let emptyset = [];;
(* Since the set has no elements, thus no element is repeated *)

let rec member x s1= match s1 with
[]-> false
|y::ys -> if (x = y) then true else member x ys;;
(* Searches through the set to find whether an element is contained in it *)

let cardinality s1= let rec cardinality1 s1 k = match s1 with 
[]->k
|x::xs-> cardinality1 xs (1+k) in cardinality1 s1 0
(* if set is not empty then add 1 to the set traverersed so far number(k) and run again without the first element of the set. If set is empty then return k *)
(* This is a tail recursive function *)

let union s1 s2 = let rec union1 s1 s2 s3 = match s1 with
[]-> s3
|x::xs-> if member x s2 then union1 xs s2 s3 else union1 xs s2 (x::s3) in union1 s1 s2 s2;;
(* Terminal case: if s1 is emptyset ->  s3 which by invariant property has no repeat elements *)
(* Base Case: s3 is initialized as s2 which is a set and thus invariant property holds *)
(* Induction Hypothesis -> for s1 of cardinality k, the invariant property of s3 holds *)
(* Proof: For s1 of cardinality k+1: s1 can be represented as first element(x) followed by another set(xs). 
xs is a set since if there are no repetitions in a set then there are no repetions in its subset(set s1, subset xs). 
If the first element is in s2 then invariant of s3 holds by induction hyp.(cardinality(xs) = cardinality(s1)-1 = k) 
If the first element is not in s2 then s3 = x::s3 is a set with no repetitions beacause x is not in s2 and is not repeated in s1 and thus could not have been in s3
and thus invariant of union xs s2 x::s3 holds by induction hypothesis *)
(* This is a tail recursive function *)

let intersection s1 s2 = let rec intersection1 s1 s2 s3= match s1 with
[]-> s3
|x::xs-> if member x s2 then intersection1 xs s2 (x::s3) else intersection1 xs s2 s3 in intersection1 s1 s2 emptyset;;
(* Terminal case: if s1 is emptyset ->  s3 which by invariant property has no repeat elements *)
(* Base case: s3 is initialized to emptyset for which invariant property holds *)
(* Induction Hypothesis -> for s1 of cardinality k, the invariant property of s3 holds *)
(* Proof: For s1 of cardinality k+1: s1 can be represented as first element(x) followed by another set(xs). 
xs is a set since if there are no repetitions in a set then there are no repetions in its subset(set s1, subset xs). 
If the first element is in s2 then invariant of x::s3 holds as we looped over elements of s1 which are not repeated and thus no element is repeated.
If the first element is not in s2 then s3 remains a set with its invariance intact.  *)
(* This is a tail recursive function *)

let difference s1 s2 = let rec difference1 s1 s2 s3= match s1 with
[]-> s3
|x::xs-> if member x s2 then difference1 xs s2 s3 else difference1 xs s2 (x::s3) in difference1 s1 s2 emptyset;;
(* New Invariant: s3 is always a set.
Base case: for s1 = emptyset we return s3 which is initialized as emptyset which is a set
Induction Hyp: if s3 is a set then for all s1 with cardinality(s1) = k, difference s1 s2 s3 is a set
Proof: For s1 of cardinality k+1, s1 can be represented as x(first element) followed by xs(set without the first element). 
Note that cardinality of xs is k and it is a set as it is a subset of s1 which is a set.
if x is a member of s2 then difference xs s2 s3 is a set by induction hyp.
if x is not a member of s2, then x::s3 is a set as s3 is always a subset of s1(Contains only elements of s1) and x is not repeated in s1(By Invariance)
Thus difference xs s2 x::s3 would be a set by ind. hyp.  *)

let rec product s1 s2 = let tuple x y = (x,y) in match s1 with 
[] -> emptyset
|x::xs -> union (map (tuple x) s2) (product xs s2);;
(* Base case: if s1 is emptyset then we return emptyset which is a set 
Induction Hyp. : for s1 of card k, product s1 s2 is a set 
Proof: for s1 of cardinality k+1, s1 can be represented as x(first element) followed by xs(set without the first element).
Note that cardinality of xs is k and it is a set as it is a subset of s1 which is a set.
Since s2 is a set, a set of tuples with first element as x and second element from s2 is another set (No Repetitions on s2).
This implies map (tuple x) s2 is a set. Product xs s2 is a set with induction hypothesis. Union of two sets is a set *)

let rec power a = let preappend x lst = x::lst in match a with
[]->[emptyset]
|x::xs -> let p = (power xs) in union (map (preappend x) p) p;;
(* Base Case: if a is emptyset then we return a set containing emptyset which is the only element in this set and thus can't be repeated *)
(* Induction Hypothesis: for a of cardinality k, power a is a set *)
(* Proof: for a of cardinality k+1, s1 can be represented as x(first element) followed by xs(set without the first element).
Note that cardinality of xs is k and it is a set as it is a subset of s1 which is a set. 
power xs returns all the subsets which do not contain x as x is not repeated in s1 so is not in xs. 
appending x to each subset in power xs gives us all subsets which contains x.
Union of two sets is a set and thus power a is a set *)

let rec subset s1 s2 = match s1 with 
[] -> true
|x::xs -> if member x s2 then subset xs s2 else false;;
(* Returns true if s1 is a subset of s2*)

let equalset s1 s2 = (subset s1 s2) && (subset s2 s1);;
(* For equality s1 and s2 need to be subsets of each other *)

end;;

(*       LAWS          *)
(* 1. member x emptyset   =    false *)
(* member x emptyset tries to match emptyset with emptyset in which it is successful and returns false *)

(* 2. cardinality emptyset =    0 *)
(* cardinality will try call cardinality1 emptyset 0 which would try to match emptyset with emptyset which is successful and returns the second parameter which is 0 *)

(* 3. member x s1 implies member x (union s1 s2) *)
(* if member x s1 returns false then above statement is true.
if member x s1 then at some point during traversal of s1 we will have x at the head.
Now if member x s2 then x is contained in s3 (which is returned when s1 is emptyset) which contains all elements of s2 (initialized as s2) else 
if not member x s2 then x is appended to s3 to make a new set which replaces the s3 parameter in the tail recursive union1 function and 
thus x is always a member of union s1 s2 if it is a member of s1 *)

(* 4. member x (intersection s1 s2) implies member x s1 *)
(* if member x intersectcion s1 s2 is false then the above statement is true
else if member x (intersection s1 s2) then x appears in intersection s1 s2 which contains elements from set s1 which exist in s2 and
thus x has to appear in s1 as well as s2 only then intersection would contain them
(for s1 it is at head at some point of traversal, for s2 it has to member x s2 to get appended to the answer variable s3). *)

(* 5. equalset (intersection s1 s2)  (intersection s2 s1) *)
(* subset (intersection s1 s2) (intersection s2 s1): if x is a member of intersection of s1 s2 then 
x has to be at the head at some point in traversal of s1 and member x s2 has to be true.
implies that x has to be member of s1 and should exist at head during traversal of s2 (by defination of member function)
which implies x is a member of intersection s2 s1

subset (intersection s2 s1) (intersection s1 s2:): if x is a member of intersection of s2 s1 then 
x has to be at the head at some point in traversal of s2 and member x s1 has to be true.
implies that x has to be member of s2 and should exist at head during traversal of s1 (by defination of member function)
which implies x is a member of intersection s1 s2 *)

(* 6. cardinality (product s1 s2) = cardinality s1 * cardinality s2 *)
(* product [] s2 returns emptyset whose cardinality is 0 = cardinality of [] * cardinality of s2, thus true *)
(* product s1 s2 traverses over s1 with head as x and tail as xs. 
A set of tuple with with first element as x and second element from the set s2 will have cardinality = cardinality of s2
product s1 s2 is written as union of above set and product xs s2
since x1 does not belong to the set xs thus no other tuple in product xs s2 will have x as the first element and thus 
cardinality product s1 s2 = cardinality tuple set + cardinality product xs s2 = cardinality s2 +cardinality product xs s2.
Now this step will be repeated cardinality s1 times so as to finish all elements in set s1 to return emptyset and thus 
cardinality product s1 s2 = cardinality s2 +cardinality s2+...cardinality s1 times = cardinality s1 *cardinlity s2*)

(*ASSIGNMENT 1.b- SET RESPRESENTATION BY CHARACTERISTIC FUNCTION*)
module A2 = struct
let emptyset x = false;;
(* emptyset contains no element => it is false for any choice of x
if there is no x such that emptyset x returns true => there is no element in set denoted by emptyset *)

let member x f = f x;;
(* By definition of characteristic function, if f(x) = True iff x belongs to set denoted by f *)

let union f1 f2 x = (f1 x) || (f2 x);;
(* union f1 f2 is a characteristic function. if x belongs to union of 2 sets then either it belongs to first set or second set or both. 
Implies one of f1 x and f2 x has to be true=> f1 x ||f2 x is true => union f1 f2 x is true
if union f1 f2 x is true =>  f1x ||f2 x is true => atleast one of f1 x, f2 x is true => x belongs to set denoted by f1 or f2 => it exists in their union *)

let intersection f1 f2 x = (f1 x) && (f2 x);;
(* x exists in intersection of sets represented by f1 and f2 then it exists in both those sets. Since f1 and f2 are characteristic functions f1 x = true and f2 x = true => f1 x && f2 x = true => intersection f1 f2 x = true
if intersection f1 f2 x = true then f1 x = true and f2 x = true => x is a member of both sets represented by f1 and f2 => x exists in the intersection of both those sets 
=> intersection f1 f2 function denotes the intersection of f1 and f2 *)

let difference f1 f2 x = (f1 x) && not (f2 x);;
(* x exists in difference of sets represented by f1 and f2 then it exists in set represented by f1 but not in the set denoted by f2. 
Since f1 and f2 are characteristic functions f1 x = true and f2 x = false => f1 x && not f2 x = true => difference f1 f2 x = true
if difference f1 f2 x = true then f1 x = true and f2 x = false => x is a member of set represented by f1 but not in the set denoted by f2=> x exists in the difference(s1 s2) of both those sets 
=> difference f1 f2 function denotes the difference of f1 and f2 *)

let product f1 f2 (x,y) = (f1 x) && (f2 y);;
(* if(x,y) exists in the product of set represented by f1 and f2 => x is a member of set f1, y is a member of set f2
f1 x = true and f2 y = true => product f1 f2 (x,y) = true 
if product f1 f2 (x,y) is true => f1 x = true, f2 y = true => x exists in set f1 and y exists in set f2 => (x,y) exists in the cartesian product of f1 and f2 *)

end;;
(*-----TEST CASE---------*)
(*let f1 x = if x=1||x=2||x=3 then true else false;;
let f2 x = if x=4||x=2||x=3 then true else false;;

let s1 = [1;2;3];;
let s2 = [4;3;2];;

A2.product f1 f2 (1,4);;
A2.product f1 f2 (1,8);;
A2.difference f1 f2 1;;
A2.difference f1 f2 2;;
A2.difference f1 f2 4;;
A2.intersection f1 f2 1;;
A2.intersection f1 f2 3;;
A2.intersection f1 f2 4;;
A2.intersection f1 f2 87;;
A2.union f1 f2 1;;
A2.union f1 f2 2;;
A2.union f1 f2 4;;
A2.union f1 f2 12;;
A2.member 1 f1;;
A2.member 4 f1;;



A1.product s1 s2;;
A1.difference s1 s2;;
A1.intersection s1 s2;;
A1.union s1 s2;;
A1.member 1 s1;;
A1.member 4 s1;;
A1.power s1;;
A1.equalset s1 s1;;
A1.equalset s1 s2;;
A1.subset s1 [1;2;3;4;5];;
A1.subset s1 s2;;
A1.cardinality s1;;
A1.emptyset;;
*)


