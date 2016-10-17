Chapter 2-
	0. Overview
		Prove a language equation (or subset) involving the regular operators union, cat, and star (as in Theorems 2.6, 2.8, or 2.9).
		
		Overall this entire chapter is to prepare for these type of proofs. Either way it's good to understand our fundamentals.
	1. Given characters existing in some Sigma, construct a definition of our set of strings over Sigma. (Sigma*)
		Answer By Rule Induction-
			___________________Empty
			epsilon elem Sigma*
			
			a elem Sigma   b elem Sigma
			____________________________Cons
			a:b elem Sigma*
		
			Reasoning-
				It is possible for a string to be empty, this provides us a proper base case where "" == epsilon.
				Using Haskell terminology provides us a great model for building up complicated strings.
				Because we can only use what's in sigma (and epsilon itself is by default in Sigma*) we can recursively build a string from elements of sigma.
				Thus are strings are the Haskell equivlaent of a1:...:an:""
				
		Answer By Structural Definition(more concise form)-
			epsilon elem Sigma*
			a:b elem Sigma* iff a elem Sigma ^ b elem Sigma
	2. Construct a Definition for String Length (unary operator |v|)-
		|epsilon| = 0			LenEmpty
		|a:b| = 1 + |b|			LenCons
		Reasoning-
			It is reasonable to assume that the empty string has a length of 0, additionally a comes from sigma which can be treated as 1 length strings.
			By providing the recursive case the length will eventually be determined as each single character will be analyzed until we reach the end...
			a1:...:an:[] 	1
			a2:...:an:[]	1+1
			...
			an:[]			1+...+1
			[]				1+...+1+0
	3. Construct a Definition for String Concatenation (binary operator x.y)-
		epsilon.a = a					CatEmpty
		a.b = c:d.b , where c:d = a		CatCons
		Reasoning-
			Concatenation is a binary operation that operates on two strings. 
			Concatenation demands that a certain order is maintained so it may be best to look at the recursive case first so as to get an idea of the structure.
			Our operation a.b in actuality is a1.a2. ... .an.[].b
			Character to String concatenation can be expressed with our operator :
			We can isolate it like so.
			a1:(a2. ... .an.[]).b
			So we can simply represent the left side with our string operator(introducing new variables for the pieces) c:d
			This gives us a.b = c:d.b , where c:d = a	
			
			Looking at this we can see where this will eventually end..
			[].b
			Which gives us intuition in how to build our base case.
			epsilon.a = a
			
			This tells it to bypass epsilon and append the rest of the string.
	4. Prove |a.b| = |a| + |b| for all b in Sigma*-
		My Solution-
			for all a,b in Sigma* let a,b be arbitrary.
			Base Case, Empty
					epsilon.b = b							by CatEmpty 
					Show |b| = 0 + |b|						by LenEmpty
						 |b| = |b|
			Inductive Case,	Cons
					Show |a.b| = |a| + |b|
						let a = a1:...:ai:[] , b = b1:...:bj:[] by Cons 
						a.b = a1:...:ai:b 						by CatCons
						
						|a1:...:ai:b|   = i+|b| 				by Inductive Derivation through LenCons
						Show i = |a|
						|a| = i	+ |epsilon| = i		 			by Inductive Derivation through LenCons and LenEmpty
						
						|a.b| = |a| + |b|
						Q.E.D.
						
			Reasoning-
				The base case is simple, we can easily reduce a concatenation of epsilon and b to just b. 
				Because the length of epsilon is 0 it trivially proves itself.
				
				For the inductive case I unraveled the definition by cons.
				We can assume that both Len and Cat are already true, so an inductive derivation should return our expected result.
				Because we have an ordered indexed list of elements we should return 1 * the number of elements traversed; in this case some arbitary value i.
				This gives us the form |a.b| = i + |b|, so we only need to show that i is in fact the length of a.
				a has one extra element which is epsilon, but by LenEmpty this gives us 0, which means that we still have i.
			
		Wilson's Solution-
			By induction on b for all b in epsilon...
			Case Empty, where b = epsilon
				|epsilon.b| = |b|		by CatEmpty
				|epsilon.b| = 0 + |b| = |epsilon| + |b|
			Case Cons, where a elem Sigma and c elem Sigma*
				Show |(a:c).b| = |a:c| + |b|
				|(a:c).b| = |a:(c:b)|		by CatCons
				|(a:c).b| = 1 + |c.b| 		by LenCons
				1 + |c.b| = 1 + |c| + |b|	by IH
				1 + |c| + |b| = |a:c| + |b|	by LenCons
				
				|(a:c).b| = |a:c| + |b|
				Q.E.D.
				
			Reasoning-
				Wilson and my base cases are nearly identical so you can look for an explanation there.
				
				A key difference in the inductive step is that because Wilson was already working with an element of Sigma he didn't need to break in the same way as my solution.
				The goal is to show |(a:c).b| = |a:c| + |b| where a:c takes the place of a in |a.b| = |a| + |b|.
				
				Taking CatCons inductive derivation to its logical conclusion leads to |a:(c:b)|.
				
				Taking a single step of LenCons gives us 1 + |c.b|	, (Show 1)
				Wilson follows the remaining steps of LenCons and unravels it, though a bit more abstractly than my similar step. , (Assume n, IH)
				1 + |c| + |b|
				
				From this a step backwards can be taken to put our a back onto |c| which gives us |a:c| + |b| 
	5. Prove identity of concatenation a.epislon = a for all a in Sigma*-
		My Solution-
			By induction on a...
				Case Empty, where a = []
					[].[] = [] by CatEmpty
				Case Cons, where a = a:b
					show (a:b).[] = a:b
						(a:b).[] = a:(b1:..:bn:[].[]) 	by CatCons and Cons
						a:b1:..:bn:([].[]) 				by IH
						a:b1:..:bn:[] = a:b				by CatEmpty		
				Q.E.D.
			Reasoning-
				The base case is proved trivially by our definition.
				
				For the inductive case I unrolled a into (a:b)
				By further Unravelling with Cons and using CatCons we can pull out the a. (First Step)
				We follow it to it's logical conclusion by repeatadly using CatCons (Assume N, IH)
				This generates our base case and shows that all that remains was our string a:b
		Wilson's Solution-
			Wilson proved both associativity and identity together, so his solution will be in 6.
	6. Prove associativity of concatenation a.(b.c) = (a.b).c for all a,b,c in Sigma*-
		My Solution-
			for all a,b,c in sigma*
			Case Empty
				a.([].c) = (a.[]).c by Indentity of Concatenation
			Case Cons where a = <ap>:[], b = <bp>:[], c = <cp>:[]   ,  and <v1..vn> are a vector of Sigma elements
				Show (<ap>:[]).((<bp>:[]).(<cp>:[])) = ((<ap>:[]).(<bp>:[])).(<cp>:[])
				Deriving Left Side as x
					(<ap>:[]).((<bp>:[]).(<cp>:[])) = (<ap>:[]).(<bp>:<cp>:[])	 by CatCons  
					(<ap>:[]).(<bp>:<cp>:[]) = <ap>:<bp>:<cp>:[]		 		 by CatCons
				Deriving Right Side as y
					((<ap>:[]).(<bp>:[])).(<cp>:[]) = (<ap>:<bp>:[]).(<cp>:[])	 by CatCons
					(<ap>:<bp>:[]).(<cp>:[]) = <ap>:<bp>:<cp>:[] = y			 by CatCons
				x = y
				Q.E.D.
		Reasoning-
			In my base case I used my previous proof to demonstrate the empty case.
			An aside...
				In actuality ([].b).c = [].(b.c) would have been valid and wouldn't have required the Identity, but it seemed like a good point to demonstrate
				how previous proved lemmas can help solve a problem. Specifically because they can already be assumed true.
			
			In the inductive case I unravelled a,b,c with Cons into a more abstract representation of the series of values in sigma followed by our epsilon([])
			Because Cons can be assumed to be correct we can follow our derivations on our left and side because we simply need to prove that they're the same.
			
			Each side easily collapses into a solution using CatCons and they are indeed equal.
			
		Wilson's Solution-
			By induction over a...
			Case Empty, a = []
				[].[] = [] by CatEmpty
				for all b,c elem Sigma*
					[].(b.c) = b.c by CatEmpty
					([].b).c = b.c by CatEmpty
			Case Cons, (a:ap).(b.c), where a = (a:ap)
				a:((ap).(b.c)) 			by CatCons
				a:(ap.b).c 				by IH
				(a(ap.b)).c 			by CatCons
				((a:ap).b).c 			by CatCons 
		Reasoning-
			The base case demonstrates the associativity with epsilon, although I could've sworn it was supposed to prove indentity as well...
			[].(b.c) = b.c is identity, but it feels like there are steps missing.
			
			For the Cons case what Wilson does is absolutely beautiful.
			He start with the form (a:ap).(b.c) having substituted a for a:ap
			He uses 1 step of cat cons (Show 1)
			Then completes the concatenation according to our assumption (IH)
			
			tl;dr it seems as if the parenthesis themselves were munipulated.
			I'm not sure if I would be able to come up with this solution on an exam.
	7. Construct a Definition for concatenation between two languages L1 and L2-
		L1.L2 = {s1.s2 | s1 elem L1, s2 elem L2}				CatLan
		
		Note-
			What is used in the definition is 'set builder notation'
			{ r | p1, ... , pn}
			r is a resultant item of a list. In this example we are constructing a set of strings,  s1.s2 
			p1, ... , pn are predicates. These describe the set being built.
			In this example we are defining where the elements are coming from. (s1 elem L1, s2 elem L2)
			
			If we wanted to we could restrict the set in some way ie: s1 /= [], s2 /= [] would exclude epsilon from both Languages being drawn from.
			
			In Haskell set builder notation translates directly into list comprehensions.
			[StrCat s1 s2 | s1 <- L1, s2 <-L2] is the direct translation into haskell.
			
			As an additional example if we included the no epsilon predicate we would have...
			[StrCat s1 s2 | s1 <- L1, s2 <-L2, s1 /= [], s2 /= []]
			or
			[StrCat s1 s2 | s1 <- L1, s2 <-L2, s1 /= "", s2 /= ""]
	8. Write a Haskell function to verify that string s is in the language L1.L2 that is to say 
	s elem L1.L2 iff Exists s1,s2 such that s1 elem L1 ^ s2 elem L2 ^ s = s1.s2 -
		verify :: String -> Language -> Language
		verify s L1 L2 = [cat s1 s2 | s1 <- L1, s2 <- L2, s == cat s1 s2] /= []
		
		Reasoning-
			s elem L1.L2 iff Exists s1,s2 such that s1 elem L1 ^ s2 elem L2 ^ s = s1.s2
			can be rewritten to
			s elem L1.L2 iff {s1.s2 | s1 elem L1, s2 elem L2, s = s1.s2} /= []  			-- I'll now be using [] to represent the empty language set.
																							-- from now on epsilon will be represented as ""
			That is to say that if we can find even 1 successful way to concatenate our language strings to form our input string then s is an element of L1.L2.
	9. Prove the various properties of language concatenation-
		9a. [].L = L.[] = []		, Zero Property
			assume [].L = {s1.s2 | s1 elem [], s2 elem L} by CatLan
				for all s2 -> null.s2			
				CatCons does not support null
				By contradiction
					[].L = []
					L.[] = []
					[].L = L.[]
			Q.E.D.
			Reasoning-
				Because concatenation of languages is defined in set builder notation we just have to prove that no elements can be
				generated by the set builder. 
				This means that the construction of elements must fail for each construction.

				We make the assumption that we will actually build something with our set.
				When we reach the step of actually concatenating a string we run into a problem, our definition does not support this behavior.
				
				As such all constructions in the sets fail.			
		9b. [""].L = L.[""] = L			, Identity Property
				[""].L = {s1.s2 | s1 elem [""], s2 elem L} by CatLan
				L.[""] = {s1.s2 | s1 elem L, s2 elem [""]} by CatLan
				Simplified
					{s1.s2 | s1 = "", s2 elem L} = {s1.s2 | s1 elem L, s2 = ""}
					Derive Solution For {s1.s2 | s1 = "", s2 elem L}
							for all s2, "".s2 = s2 -> {s1.s2 | s1 = "", s2 elem L} = L	By CatCons
					Derive Solution For {s1.s2 | s1 elem L, s2 = ""}
							for all s1, s1."" = s1 -> {s1.s2 | s1 elem L, s2 = ""} = L	By CatCons
			Q.E.D.
			Reasoning-
				Utilizing our set builder notation we just had to prove that the accompanying [""] to our Language will have no effect on it.
				First I set up our definition then I simplified our pedicate. (a set with only one element can just be seen as that single element)
				Thankfully our string concatenation definition supports this behavior and elegantly tells us that nothing will change about the string.
				
				This implies a conclusion, that all we got back from the set was our L.
				This works in both directions.				
		9c. L1.(L2.L3) = (L1.L2).L3		, Associative Property
				Assume (L1,L2,L3) have i,j,k elements respectively.
				L1.(L2.L3) = {s1.s23 | s1 elem L1, s23 elem L2.L3} by CatLan
				(L1.L2).L3 = {s12.s3 | s12 elem L1.L2, s3 elem L3} by CatLan
					L2.L3 = {s2.s3 | s2 elem L2, s3 elem L3} = {s21s31,s21s32,...,s2js3k}	by CatLan
					L1.L2 = {s1.s2 | s1 elem L1, s2 elem L2} = {s11s21,s11s22,...,s1is2j}	by CatLan
					
					L1.(L2.L3) = {s1.s23 | s1 elem L1, s23 elem {s21s31,s21s32,...,s2js3k}}
							   = {s11s21s31,s11s21s32,...,s1is2js2k}
					(L1.L2).L3 = {s12.s3 | s12 elem {s11s21,s11s22,...,s1is2j} ,s3 elem L3}
							   = {s11s21s31,s11s21s32,...,s1is2js2k}
				Q.E.D.
			Reasoning-
				I couldn't figure out a more elegant solution, though Im sure it exists...
				So what I did is I built up our set builder until there were no more sets to build.
				From there I represented an abstract normalized representation of the set items
				From there the normalized lists will take the same structure.			
		9d. L1 subset L2 -> (L.L1 subset L.L2) ^ (L1.L subset L2.L) 
			Explaining the Problem in English-
				If L1 is a subset of L2 
				This implies that concatenating a language L onto both L1 . L2 will retain the subset relationship.
			The Solution-
				Show (L.L1 subset L.L2) ^ (L1.L subset L2.L) 
					
					L1 subset L2 -> L2 = L1 union Y where
					Let L be {L1,...,Li} ,L1 be {L11,...,L1j} , L2 be L1 union Y, Y be {Y1,...}
					
					Show (L.L1 intersect L.L2) = L.L1			by definition of subset
						L.L1 = {l.l1 | l elem L, l1 elem L1}	by CatLan
						{L1.L11,...,Li.L1j} 					by derivation through CatLan
						
						L.L2 = {l.l2 | l elem L, l2 elem L2}	by CatLan
						{L1.L11,...,Li.L1j,L1.Y1,...}			by derivation through CatLan
						
						L.L1 intersect L.L2 = {L1.L11,...,L1.L1n} = L.L1
						
					Show (L1.L intersect L2.L)  = L1.L			by definition of subset
						L1.L = {l1.l | l1 elem L1, l elem L}	by CatLan
						{L11.L1,...,L1j.L1i} 					by derivation through CatLan
						
						L2.L = {l2.l | l2 elem L2, l elem L}	by CatLan
						{L11.L1,...,L1j.L1i,Y1.L1,..} 			by derivation through CatLan
						
						L1.L intersect L2.L = {L11.L1,...,L1j.L1i} = L1.L				
				Q.E.D.
			Reasoning-
				Before starting here is the definition of a subset if you don't remember it...
					X subset Y <-> X intersect Y = X
				Additionally a useful property of subsets...
					X subset Y -> Y = X union Z
				We can combine these...
					X subset (X union Z) <-> X intersect (X union Z) = X
				The Left side is true by default so what remains to be used is...
					X intersect (X union Z) = X
				So all that needs to be proved is that each side is in fact the identity of X.
				
				Before that can be done the concatenation needs to be resolved. Do so with derivations with arbitrary lengths.
				
				Once completeed all that remains is performing the set intersection to show that we have indeed found the indentity. 
		9e. (L.(L1 union L2) = (L.L1) union (L.L2)) ^ ((L1 union L2).L = (L1.L) union (L2.L)) 
			In English-
				Concatenating an arbitrary language to the union of our two Languages will produce the same result as concatenating them separately and unioning them.
			Solution-
				Let L = {L1,...,Li}, L1 = {L11,...,L1j}, L2 = {L21,...,L2k}
				L1 union L2 = {L11,...,L1j,L21,...,L2k}
				Prove L.(L1 union L2) = (L.L1) union (L.L2)
					L.(L1 union L2) = {L1.L11,...,Li.L1j,L1.L21,...,Li.L2k} 	by CatLan
					L.L1 = {L1.L11,...,Li.L1j}									by CatLan
					L.L2 = {L1.L21,...,Li.L2k}									by CatLan
					L.L1 union L.L2 = L.(L1 union L2)
					
				Prove (L1 union L2).L = (L1.L) union (L2.L)
					(L1 union L2).L = {L11.L1,...,L1j.Li,L21,L1,...,L2k.Li}		by CatLan
					L1.L = {L11.L1,...,L1j.Li}									by CatLan
					L2.L = {L21,L1,...,L2k.Li}									by CatLan
					L1.L union L2.L = (L1 union L2).L
				Q.E.D.
			Reasoning-
				This one can be proved just by following the derivations.. It takes awhile.
		9f. (L.(L1 interset L2) subset (L.L1) intersect (L.L2)) ^ ((L1 intersect L2).L subset (L1.L intersect L2.L)), but not the reverse
			Solution-
				Let L = {L1,...,Li}, L1 = {L11,...,L1j}, L2 = {L11,...,L2k}, L1 intersect L2 = {x1,...,xn}
				Prove L.(L1 intsersect L2) subset (L.L1) intersect (L.L2)
					Show L.(L1 intsersect L2) intersect ((L.L1) intersect (L.L2)) = L.(L1 intsersect L2)
					L.({x1,...,xn}) intersect ((L.L1) intersect (L.L2)) = L.({x1,...,xn})
					{L1.x1,...,Li.xn} intersect ((L.L1) intersect (L.L2)) = {L1.x1,...,Li.xn} 								by CatLan
					{L1.x1,...,Li.xn} intersect ({L1.L11,...,Li.L1j} intersect {L1.L21,...,Li.L2k}) = {L1.x1,...,Li.xn} 	by CatLan
					-> for all i.j elem L.(L1 intersect L2), i.j elem L.L1 ^ i.j elem L.L2
					   for all j elem (L1 intersect L2), j elem L1 ^ j elem L2 						by CatLan  True by Definition of Intersection
					   for all i elem L 															by CatLan
					   i.j elem L.L1 ^ i.j elem L.L2 
				Prove ((L1 intersect L2).L subset (L1.L intersect L2.L))
					Do it the other way around...
				Prove "but not the reverse"
					assume the reverse holds true.
					((L.L1) intersect (L.L2)) subset L.(L1 interset L2) ^ ((L1.L intersect L2.L) subset (L1 intersect L2).L)
					by example....
						I can't come up with a good example... But if the reverse doesnt hold true then there should be some input that will return false and prove the property by contradiction.
			Reasoning-
				Oh boy this was a mess for me. 
				I start by giving some definition for my sets and following my derivations.
				I get stuck as I don't have a direct definition.
				{L1.x1,...,Li.xn} intersect ({L1.L11,...,Li.L1j} intersect {L1.L21,...,Li.L2k}) = {L1.x1,...,Li.xn}
				
				But in order for the identity to hold true each element of the left side has to be in BOTH sets which helps remove the nested intersection.
				for all i.j elem L.(L1 intersect L2), i.j elem L.L1 ^ i.j elem L.L2
				
				Thankfully we can follow our concatenation backwards to break this apart.
				1.     for all i elem L by CatLan
					This is trivially true. 
				2.     for all j elem (L1 intersect L2), j elem L1 ^ j elem L2
					And for this we have to prove that j is in both sets... but j is our elements x1,...,xn meaning...
					L1 intersect L2 = {x1,...,xn} which is the exact same as x1,...,xn elem L1 ^ x1,...,xn elem L2
					
				The otherwise can be similarily broken apart and solved in this way.
				
				"but not the reverse" is tricky though. Normally when confronted with these kinds of problems you should attempt a 'proof by contradiction'
				
				That is to say you instead assume that it is true and show that it is false. Typically these can be done with an example...
				Although I wasn't able to find that example.
				Wilson provides that example as L={a,aa}, L1 = {ab}, L2 = {b}
	10. Construct the Definition for Kleene Star-
		Inductive Definition-
			___________ StarEmpty
			[] elem L*
			
			a elem L		b elem L*
			_________________________StarCat
				  a.b elem L*
		Concise Definition-
			""  elem L*
			a.b elem L* iff a elem L ^ b elem L*
	11. Prove for any language L that L* = {""} union L.L*.
		By induction over a elem L*
			Case StarEmpty, a = ""
				True
			Case StarCat Let b and a be arbitrary in, (b.a)
				b elem L , a elem L* by StarCat
		Q.E.D.
		Reasoning-
			The structure defines the proof. Wilson's proof which im going to exclude this time also explores interesting properties of L*.
	12. Prove the various properties of kleene star-
		12a. []* = {""}-
			{""} union	{} elem L*		by StarCat
			{""} union	{}.{} elem L*	by StarCat
			{""} union	{} elem L*		by CatLan
			{""} elem L*				by StarEmpty
			Q.E.D.
			
			Reasoning-
				Demonstrate that derivations of StarCat go nowhere. All the remains is the one element.
		12b. {""}* = {""}-
			{""} union	{""} elem L*		by StarCat
			{""} union	{""}.{""} elem L*	by StarCat
			{""} union	{""} elem L*		by derivation through CatLan
			{""} elem L*					by StarEmpty
			Q.E.D.

			Reasoning-
				Similar to the []* proof. The key difference is that the going nowhere is found by running the derivation.
		12c. (Sigma)* = Sigma*-	
			let A,B {'',a,b,...T1,T2} = Sigma
				"" elem Sigma* 						by Empty
				a:b elem Sigma* 					by Cons
				Sigma* = {"",a,b,...,a:b,b:a,T1:T2}	by Cons
				
				Show ({'',a,b,...T1,T2})* = {"",a,b,...,a:b,b:a,...,T1:T2}
					Sigma*1 = {""} union	{'',a,b,...T1,T2}.{'',a,b,...T1,T2} elem L*		by StarCat
					{"",a,b,...,a:b,b:a,T1:T2}												by CatLan
					Q.E.D.
					Also...
						...	IH
						Sigma*n = {"",a,b,...,a:b,b:a,...,T1:T2,...}
						Sigma*1 = {"",a,b,...,a:b,b:a,...,T1:T2}
						Sigma*0 = {""}

						Sigma*1 subset Sigma*n -> L subset L*
					Also,
						Sigma   = {'',a,b,...T1,T2}
						Sigma*  = {"",a,b,...,a:b,b:a,...,T1:T2,...}
						
						Sigmap  = {'',a,b,...T1,T2,T3}
						Sigma*p = {"",a,b,...,a:b,b:a,...,T1:T2,T2:T3,...}
						
						Sigma subset Sigmap ^ Sigma* subset Sigmap*
			Reasoning-
				Sigma* will accept any number of self concatenations of the language. 
				Sigma is our alphabet so we need to show that a self concatenation will indeed lead to the same result as Cons of every possible element pair.
				
				Through our properties it comes out as so.
				The next thing to check would be every possible combination of every single combination, but we retain every possible L and L* which are always a subset of a later L*
				
				From this point on because there is only a limited amount of time for me to make this my proofs will be even more informal than usual. But I will provide my own intuitions for solving them.
		12d. L subset L*-
			Proven by 12c.
		12e. L1 subset L2 -> L1* subset L2*-
			Proven by 12c.
		12f. L*.L* subset L*-
			Show L*.L* intersect L* = L*.L*
				Using example Sigma = {'',a,b,...T1,T2}
				L*(N-1).L*(N-1) = L*N = {"",a,b,...,a:b,b:a,...,T1:T2,...}		
				L*N intesect L*N = L*(N-1) . L*(N-1)
			Reasoning-
				L*.L* is just running L* an additional time.
		12g. (L*)* subset L*-
			12f proves it by demonstrating repeated 12f
Chapter 3-
	0. Overview
		Given a regular expression and a string, does the string match the regular expression?
		Given a regular expression, list examples of strings that match it and strings that do not match it...
			If you know the first one, then you know this one.
		Define functions in Haskell by structural recursion on RE, as in Section 3.3 and Labs 6 and (what was) 7.
		Create a regular expression that matches a given set of strings (described in English), as in the Exercises at the end of Section 3.2.
	1. Provide the Structural Definition for Regular Languages-

		________Empty
		[] elem Sigma
		
		a elem Sigma
		_____________Letter
		{a} elem REG
		
		L1 elem REG    L2 elem REG
		___________________________Union
		L1 Union L2 elem REG
		
		L1 elem REG    L2 elem REG
		_________________________Cat
		L1.L2 elem REG
		
		L elem REG
		____________Star
		L* elem REG
	2. Provide a Haskell Function to verify if a Language with the same structure is in fact regular.
		isREG :: Language -> Bool
		isREG  Empty     = True
		isREG (Letter a) = elem a Sigma
		isREG (Union a b)= isREG a && isREG b
		isREG (Cat   a b)= isREG a && isREG b
		isREG (Star a)   = isREG a
	3. Finite Languages are Regular, are there infinite languages that are regular?
		Yes. L*
	4. Determine if the following infix Regular Expressions match the string.
		4a. (a+b)* "ababababababbbbbbbaaaaaaabaababababababababababbbbbbbaababbabababababababababababbaabbabaababababababababababab"
			Yes, (a+b) means meach either a or b, the * says 0 or more times. As a result it can match any combination of a or b.
		4b. (a*b*)*"ababababababbbbbbbaaaaaaabaababababababababababbbbbbbaababbabababababababababababbaabbabaababababababababababab"
			Yes, describes the same language as (a+b)*
		4c. (aa)*+(bb)* "aaaaaabbbb"
			Yes, this is the language of even number of a's followed by even number of b.
		4d. a*b* "ababababababababababababa"
			No, This is the language of 0 or more a followed by 0 or more b. 
		4e. (a+b)*a(a+b)* ""
			No, there is a lone a that need to match.
		4f. (a+b)*a(a+b)* "a"
			Yes, this is the language that matches anything, so long as it has atleast one a.
		4g. (((a*)*)*)* "aaaaaaaaaa"
			Yes, this describes the same language as a*, one way of thinking about it is that each level may run only a max of 1 time.
	5. Wilson's Example Problems, Construct Regular Expressions for each description...
		5a. all strings in which every a is followed by bb
			(abb+b*)*
		5b. all strings with an even number of a
			(b*ab*a)*
		5c. all strings with at least one a and at least one b
			((a+b)*a(a+b)*b(a+b)*) + ((a+b)*b(a+b)*a(a+b)*)
		5d. all strings with no instance of bbb
			(a+aba+abba)*
		5e. all strings with no instance of aba
			(a*bb*ba*)*
		5f. all strings with every instance of aa coming before every instance of bb
			(b+0)((ab)+(aabb))*(a+0)
			cheating a little bit by using epsilon to create optional values.
		5g. all strings with an even number of a and even number of b
			(aa+bb+abab+baba+a(bb)*a+b(aa)*b)*
	6. Define in Haskell the Following Recursive Predicates of Regular Expressions (3.3)...
	I'll do the first and last...
	
		isEmpty :: RE -> Bool
		isEmpty Empty = True
		isEmpty (Letter a) = False
		isEmpty (Union a b)= isEmpty a && isEmpty b
		isEmpty (Cat a b)  = isEmpty a || isEmpty b
		isEmpty (Star a)   = False
		
		
		....

		isInfinite :: RE -> Bool
		isInfinite Empty = False
		isInfinite (Letter a) = False
		isInfinite (Union a b)= isInfinite a || isInfinite b
		isInfinite (Cat a b)  = (isInfinite a && (not.isEmpty) b ) || (isInfinite b && (not.isEmpty) a )
		isInfinite (Star a)   = (not.empty) a && (not.unitary) a
Chapter 4-
	0. Overview
		Create an FSM that accepts a given set of strings (described in English), as in the Exercises in Section 3.2.
		
		Define functions in Haskell that return elements of type FSM a as in Lab 6: even_as, no_aaa, emptyFSM, letterFSM, stringFSM, ex1, etc., but nothing more complicated than that.
	1. Give a definition of an FSM in terms of the elements composing it-
		Q = Set of States
		s0= Starting State
		fs= Set of Final States
		delta=set of transition tuples. (q1,a,q2)
	2. Construct the definition of an FSM in Haskell-
		type FSM = ([Int],Int,[Int],[(Int,Char,Int)])
	3. Construct FSM diagram for the following languages and provide it using our haskell definition...
		I will put down the haskell equivalents
		3a. The language of even a and even b
			[[1,2,3,4],1,[1],[(1,'a',2),(1,'b',3),(2,'a',1),(2,'b',4),(3,'a',4),(3,'b',1),(4,'a',3),(4,'b',2)]]
		3b. The language of all strings with 0 or more a,b
			[[1],1,[1],[(1,'a',1),(1,'b',1)]]
		3c. The language of no strings
			[[1],1,[],[(1,'a',1),(1,'b',1)]]
Chapter 5-
	0. Overview
		Prove simple facts about the notions concerning FSMs (delta*, L(M), Lq(M)), usually by induction on the strings involved.
		
		Answer questions about the union, concatenation, or star constructions on FSMs. For example, given small machines M1and M2,
			draw the machine M1 union M2, M1.M2, or M*.
			given a particular state from one of these machines and a small input string, compute the state to which the machine transitions;
			identify whether or not a given state from one of these machine is a final state.
	1. Explain how we can structually represent FSMs so as to make them equivalent to Regular Languages-
		Construct machines that accompany the structure of regular languages.
		Empty Machine,	accepts nothing
		Letter Machine, accepts {a}
		Union Machine,  accepts L1 union L2
		Cat Machine,	accepts L1.L2
		Star Machine,	accepts L*
	2. Construct the Empty Machine and prove that it accepts exactly the empty language-
		[  1  ]
		\Sigma/
		
		Proof-			
			For all transition delta(1,i), i elem Sigma, delta(1,i) -> qs 1
	3. Construct the Letter machine and prove that it accepts exact the langage {a}, a elem Sigma-
			[1]->a->[[2]]
			!a\      / w
			   [  T  ]
		Proof-
				delta*(q,"") = q
			
				Exists w elem Sigma,w elem L(M(a)), delta*(1,w) elem {a}
				show Exists w elem Sigma delta*(1,w) elem {a}
					assuming a elem Sigma
					delta*(1,a:w) = delta*(delta(1,a),w), where w = ""
				Q.E.D.
		Reasoning- 
			the first line was a note so I would remember the empty property of delta*
			We must find that w is in sigma, L(M(a)), and that delta*(1,w) elem {a}
			
			that is to say that the edges we desire are in both in our language {a}, and that it can be derived from our machine.
			we can assume that are edges are in Sigma, otherwise our machine would be invalid no matter what.
			We can present a clear case where it supports the language.
			
			delta*(1,a:w) = delta*(delta(1,a),w), where w = ""			
	4. Construct the Definition of the Union Machine and prove that it accepts the language L1 union L2, test by constructing a union machine of two letter machines a,b -
		Q = Q1 X Q2
		s = {s1,s2}
		f = {(q1,q2), q1 elem F1 || q2 elem F2} = F1 x Q2 union F2 x Q1
		delta((q1,q2),a) = (delta1(q1,a),delta2(q2,a))

		m1 = {
			Q1=[1,2,3]
			s1=1
			F1=[2]
			delta=[(1,'a',2),(1,'b',3),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)]
		}
		m2 = {
			Q2=[1,2,3]
			s2=1
			F2=[2]
			delta=[(1,'a',3),(1,'b',2),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)]
		}
		
		Q = [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)]
		s = (1,1)
		f = [(1,2),(2,1),(2,2),(2,3),(3,2)]
		delta = [((1,1),'a',(2,3)),((1,1),'b',(3,2)),((2,3),'a',(3,3)),...] 
		
		Prove exists w, w elem M1, w elem M2, *delta((q1,q2),w) elem L1 union L2
			show *delta((q1,q2),w) elem L1 union L2
			assuming l elem sigma, l elem L1, l elem L2, w = "", q1 elem F1 || q2 elem F1 
				*delta((q1,q2),l:w) = (delta*1(delta(q1,l),w),delta*2(delta(q2,l),w))
			Q.E.D.
		Reasoning-
			We know that for the union language we can accept either or. Using our intuition we know that the union machine sort of 'splits of' and makes both
			choices simultaniously.
			
			We know some information that should be obvious.
			For example both transitions are in sigma and are essentially true by default for arbitrary w just by w being in sigma.

			But we also need to make sure it terminates correctly.
				*delta((q1,q2),l:w) = (delta*1(delta(q1,l),w),delta*2(delta(q2,l),w))
				where w is epislon and either of our states q1,q2 are in a final state.
	5. Construct a definition for the Concatenation Machine and construct a concatenation of the machines Letter a and Letter b (no proof)-
		Q={(q1,X2c)| q1 elem Q1, X2 subset Q2},	X2c = X2 Union {s2 | q1 elem F1}
		s=(s1,/)
		F={(q1,X2)													, (q1,X2) elem Q, X2 intersect F2}
		delta=((q1,X2),a) = (delta1(q1,a),deltahat2(X2,a))			, Pow(Q2) (><) Sigma -> Pow(Q2)
		
		In english-
			Our states are q1 and each subset of Q2. (q1,[]),(q1,[1]),...,(q1,[n]),(q1,[1,1])...
			HOWEVER ANYTIME q1 elem F1, then X2 = s2
			
			Start state is (s1,[])
			
			Our final states are... hard to explain.
			Essentially we follow our machine like we would in the union machine, but the second element is epsilon until we have reached a final state of 1.
			That transports us into the other machine.
		(Letter a).(Letter b)
		m1 = {
			Q1=[1,2,3]
			s1=1
			F1=[2]
			delta=[(1,'a',2),(1,'b',3),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)]
		}
		m2 = {
			Q2=[1,2,3]
			s2=1
			F2=[2]
			delta=[(1,'a',3),(1,'b',2),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)]
		}	
		for simplicity I'm only going to concern myself with reachable states in the machine. states of (q1,q2), len q2 > 1 will not be considered.
		m1.m2 = {
			Q=[(1,[]),(2,[1]),(3,[]),(1,[1]),(3,[1]),(1,[2]),3,[2],(1,[3]),(2,[3]),(3,[3])]
			Qreachable = [(1,[]),(2,[1]),(3,[]),(3,[2]),(1,[3]),(3,[3])]
			s=(1,[])
			f=[(2,[2]),(1,[2]),(3,[2])]
			freachable = [(3,[2])]
			delta=[((1,[]),'a',(2,[1])),((1,[]),'b',(3,[])),((3,[]),'a',(3,[])),((3,[]),'b',(3,[])),((2,[1]),'a',(3,[3])),((2,[1]),'b',(3,[2])),((3,[3]),'a',(3,[3])),((3,[3]),'b',(3,[3])),((3,[2]),'a',(3,[3])),((3,[2]),'b',(3,[3]))]
		}
		
		Hopefully I didn't make a mistake flying through.
		It seems it might be easier to understand what the machine 'does' and build up the deltas first when making it by hand. 
		
		like...
									/a,b\
		(1,[])->a->(2,[1])----->a->(3,[3])
		    |				\
			\-->b->(3,[] )	 \->b->((3,[2]))->a,b->(3,[3])
					\a,b/							
	6. Construct a definition for the Star Machine and construct the machine (Letter a)* (no proof)-
		Xc = X union {s1 | X intersect F1}
		Q = {Xc | X subset Q1}
		s = [/]
		F = {/} union {X | X elem Q, X intersect F1}
		delta(X,a) = {
			{delta1(s1,a)}c, if X = /
			deltahat1(X,a)c, else
		}
		
		m1 = {
			Q1 = [1,2,3]
			s1 = 1
			F1 = [2]
			delta = [(1,'a',2),(1,'b',3),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)]
		}
		
		m1*
		Q = [[],[1],[1,2],[3],[1,3],[1,2,3]]
		Qreachable = [[],[1,2],[1,3]]
		s = []
		F = [[],[1,2],[1,2,3]]
		Freachable = [[],[1,2]]
		delta = [([],'a',[1,2]),([],'b',[1,3]),([1,2],'a',[1,2]),([1,2],'b',[1,3]),([1,3],'b',[1,3]),([1,3],'b',[1,3])]
		
		Drawing it out might give a good intuition to how it interacts with the original machine.
		Note that it isn't optimal. Technically [1,2],[1,3] are all that are needed to accept the language.		
Chapter 6-
	0. Overview 
		Solve a small SPLE (at most 3-by-3) involving regular expressions.
			
		Construct an SPLE from a given FSM.
	1. Provide a definition for a PLE-
		X = (L1.X) union L2
		where X is a solution language
	2. Define a proper language-
		a language where |w| > 1 for every w in L
	3. Define Arden's Lemma-
		For any L1, L2
		L=(L1*).(L2) is the smallest solution to a SPLE
		if L and Lp are solutions then L subset Lp
		if L1 is proper then L is the unique solution.
	4. Prove Arden's Lemma-
		L1.(L1*.L2) union L2 = 
			(L1.L1*).L2 union L2 		by associativity of concatenation
			(L1.L1*).L2 union {""}.L2	by identity of concatenation
			(L1.L1* union {""}).L2 		by 2.6.5, (not sure of the name)
			(L1.L1*).L2					by property of star
			(L1*).L2					by property of star
			L1*.L2
	5. Explain how to create a SPLE(Updated)
		Demonstrated wtih wilsons example machine

			  /b\      /b\      /b\
			->[X]->a->[[Y]]->a->[Z]
				|\             |
				 |____a________|
				 
		
		We construct 1 equation for each node based on where the paths go.
		X = bX + aY
		Y = bY + aZ + 1
		Z = bZ + aX
		
		we add + 1 at the end of an equation if it's a final state. 
		
	6. Explain how to solve a SPLE(Updated)
		Continuing from example 5 I'll lable each of my steps..
		
		X = bX+aY
		Y = bY+aZ+1
		Z = bZ+aX

		X = b*+aY					by arden's lemma
		Y = b*(aZ+1)				by arden's lemma
		Z = aX+bZ					rearranging

		Z = aX+bZ
		Z = a(b*+aY)+bZ				by substitution
		Z = a(b*+a(b*(aZ+1)))+bZ	by substitution

		Z = a(b*a(b*(aZ+1)))+bZ		by arden's lemma and closure of star, b** -> b*
		Z = ab*ab*(aZ+1)+bZ			by associativity of concatenation.
		Z = ab*ab*aZ+ab*ab*+bZ		by the distributive property (ab*ab* distributed into aZ+1) 
		Z = ab*ab*aZ+bZ+ab*ab*		rearranging
		Z = (ab*ab*a+b)Z+ab*ab*		by distributive property (pulled out the Z from bZ and ab*ab*aZ)

		Z = (ab*ab*a+b)*ab*ab*				by arden's lemma, solved
		Y = b*(a(ab*ab*a+b)*ab*ab*+1) 		by substitution, solved
		X = b*+ab*(a(ab*ab*a+b)*ab*ab*+1) 	by substitution, solved
		
		Remember that we have a lot of our usual math tools here and combined with arden's lemma it can be solved algebraically.