#write m in Base n
base_conversion := function(m,n)
	local res;
	res:= [];
	while (m>=n) do
		Add(res,m mod n);
		m := Int(m/n);
	od;
	Add(res,m);
	return Reversed(res);
end;

#G is assumed to contain the inverses
Find_word_with_property:= function(G,prop,radius)
	local i, j, offset, word, element;
	offset := Size(G)^radius;
	for i in [0..Size(G)^radius-1] do
		word := base_conversion(offset + i,Size(G));
		word := List(word{[2..Size(word)]},x -> x+1);
		
		element := One(G[1]);
		for j in word do
			element := element*G[j];
		od;
		if prop(element) then
			return word;
		fi;
	od;
	return fail;
end;
				
Grig_element_as_word_over_G := function(e,G,Fam)
	local G_new,G_with_inverse,g,radius,result,translate_inverse;
	if Size(G) = 0 then
		return fail;
	fi;
	G_new := [];
	for g in G do
		if not g^-1 in G then
			Add(G_new,g^-1);
		fi;
	od;
	translate_inverse := function(t)
		if t > Size(G) then 
			return -1*Position(G,G_new[t-Size(G)]^-1);
		fi;
		return t;
	end;
	
	G_with_inverse := Concatenation(G,G_new);
	radius:=1;
	while(true) do
		Print("Check at radius: ",radius,".\n");
		result:=Find_word_with_property(G_with_inverse,g -> e=g,radius);
		if result <> fail then
			return AssocWordByLetterRep(Fam,List(result,translate_inverse));
		fi;
		radius := radius +1;
	od;
	
end;


alternating_a_form := function(w)
	local a,b,c,d,i,j,k,L,red_L,change,last,last_ind;
	#Given w as Word
	#use ![2] for easy acess of a word.
	
	#Just for my mind...
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	red_L:=List(LetterRepAssocWord(w),AbsInt);
	
	change := true;
	while (change) do
		change := false;
		last := 5; #not a possable generator
		last_ind := -1;
		for i in [1..Size(red_L)] do
			if IsBound(red_L[i]) then
				if red_L[i]=last then #all generators are of order two
					Unbind(red_L[i]);
					Unbind(red_L[last_ind]);
					last:=5;
					last_ind:=-1;
					change:= true;
				else 
					L := [b,c,d];
					if (not last in [a,5]) and red_L[i] in L then
						Remove(L,Position(L,last));
						Remove(L,Position(L,red_L[i]));
						red_L[last_ind] := L[1]; #bc=cb=d, bd=db=c, cd=dc=b
						last := L[1];
						Unbind(red_L[i]);
						change := true;
					else
						last:=red_L[i];
						last_ind:=i;
					fi;
				fi;
				
			fi;	
		od;
	od;
	#Fill the gaps
	L:= [];
	for k in red_L do
	 Add(L,k);
	od;
	return AssocWordByLetterRep(FamilyObj(w),L);
end;#
#Computes a unique representative coset element of w*L.
#The computed Element is of the form (a*d)^i*a^j ,i\in[0..3],j\in[0,1]
L_representant := function(w)
	local a,b,c,d,k,l,L,red_L,new_L,change,Fam;
	Fam := FamilyObj(w);
	w:=alternating_a_form(w);
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	change := true;
	while change do
		change := false;
		new_L := [];
		red_L:=List(LetterRepAssocWord(w),AbsInt);
		#Print("red_L: ",red_L,"\n");
		
		for l in red_L do
			if l = b then
				change := true;
			elif l = c then
				change := true;
				Add(new_L,d);
			else Add(new_L,l);
			fi;
		od;
		#Force the form unique beginning with a.
		w :=	alternating_a_form(AssocWordByLetterRep(Fam,new_L));
		if Length(w)>0 and Subword(w,1,1) = AssocWordByLetterRep(Fam,[d]) then
			w := AssocWordByLetterRep(Fam,[a,d,a,d,a,d,a])*w;
		fi;
		if Length(w)>7 then 
			w:=Subword(w,1,Length(w) mod 8);
		fi;
	od;
	return w;
end;
#####################################################################
#Given a word as LetterRepresentation
shorten_word := function(w) #Killl all instances of x,-x and 1,1 and 2,2, -1,-1,-2,-2
	local change, last_pos, l, new_w;
	change := true;
	last_pos := Size(w)+1;
	w[last_pos] := 0;
	while change do
		last_pos := Size(w);
		change := false;
		for l in [1..Size(w)-1] do 
			if IsBound(w[l]) then
				if w[l] = -1*(w[last_pos]) or (w[l]= w[last_pos] and w[l] in [-2,-1,1,2]) then
					change := true;
					Unbind(w[l]);
					Unbind(w[last_pos]);
					last_pos := Size(w);
				else
					last_pos := l;
				fi;
			fi;
		od;
	od;
	new_w:=[];
	for l in w do		
		Add(new_w,l);
	od;
	return new_w{[1..Size(new_w)-1]};
end;
#Precomputed list gen_conjugates[x][y] is x^y as word in L_gen
#where L_gen = [[b],[a,b,a],[b,a,d,a,b,a,d,a],[a,b,a,d,a,b,a,d]];
#and y in [b,c,d,a]
gen_conjugates := [[[1],[1],[1],[2]],
											[[1,2,1],[1,-4,2,1],[-4,2],[1]],
											[[1,3,1],[-3],[1,-3,1],[4]],
											[[1,4,1],[1,-4,1],[-4],[3]]];
#Given a word w over G as LetterRepresentation and an index gen of a generator of L.
#The Iterativ Method below is faster!
#compute_conjugates_rek := function(gen,w) #Computes the conjugator gen^w in generators of L
#	local par_Con, Con, x;
#	if Size(w) = 0 then
#		return [gen];
#	fi;
#	if gen<0 then
#		par_Con := List(Reversed(gen_conjugates[-1*gen][w[1]]),x->-1*x);
#	else
#		par_Con := gen_conjugates[gen][w[1]];
#	fi;	
#	if Size(w) = 1 then
#		return par_Con;
#	fi;
#	Con := [];
#	for x in par_Con do
#		Append(Con,compute_conjugates(x,w{[2..Size(w)]}));
#	od;
#	return Con;
#end;
#Given a word w over G as LetterRepresentation and an index gen of a generator of L.
compute_conjugates := function(gen,w) #Computes the conjugator gen^w in generators of L
	local Gen, x, g, L;
	Gen := [gen];
	for x in w do
		L:= [];
		for g in Gen do
			if g<0 then
				Append(L,List(Reversed(gen_conjugates[-1*g][x]),y->-1*y));
			else 
				Append(L,gen_conjugates[g][x]);
			fi;
		od;
		Gen := shorten_word(L);
	od;
	return Gen;
end;
#Given a word w over G as LetterRepresentation and a word v over L_Gen 
compute_conjugates_of_word := function(v,w)
	local con, x;
	con := [];
	for x in v do
		Append(con,compute_conjugates(x,w));
	od;
	return con;
end;

#Just for test issues...
	#L_gen_to_elm := function(w)
	#	local elm,x;
	#	elm:= [];
	#	for x in w do
	#		if x<0 then
	#			Append(elm,Reversed(L_gen[-1*x]));
	#		else
	#			Append(elm,L_gen[x]);
	#		fi;
	#	od;
	#	return elm;
	#end;

######################################################################
L_Decomposition := function(w)
	local a,b,c,d,l_elm,l_elm_compl,k,l,i,L,red_L,new_L,change,Fam,gen_conjugates;
	Fam := FamilyObj(w);
	w:=alternating_a_form(w);
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	l_elm := []; #Will contain tuples [v,w,...] meaning l = ...b^w·b^v
	#L_gen := [[b],[a,b,a],[b,a,d,a,b,a,d,a],[a,b,a,d,a,b,a,d]];
	change := true;
	while change do
		change := false;
		new_L := [];
		red_L:=List(LetterRepAssocWord(w),AbsInt);
		for i in Reversed([1..Size(red_L)]) do
			if red_L[i] = b then
				change := true;
				Add(l_elm,Reversed(new_L));
			elif red_L[i] = c then
				change := true;
				Add(l_elm,Reversed(new_L));
				Add(new_L,d);
			else 
				Add(new_L,red_L[i]);
			fi;
		od;
		new_L := Reversed(new_L);
		w :=	alternating_a_form(AssocWordByLetterRep(Fam,new_L));
	od;
	#Print("Computation of Rep. finished");
	l_elm_compl := [];
	for l in Reversed(l_elm) do
		Append(l_elm_compl,compute_conjugates(1,l));
	od;
	#Print("Before forced: ",w,"\n");
	#Force the form unique beginning with a.
	if Length(w)>7 then 
		w:=Subword(w,1,Length(w) mod 8);
	fi;
	if Length(w)>0 and Subword(w,1,1) = AssocWordByLetterRep(Fam,[d]) then
		w := Subword(AssocWordByLetterRep(Fam,[a,d,a,d,a,d,a,d]),1,8-Length(w));
	fi;
	
	return [w,shorten_word(l_elm_compl)];
end;


K_representant := function(w)
	local a,b,c,d,k,l,L,red_L,new_L,change,nb,b_exist;
	w:=alternating_a_form(w);
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	change := true;
	while change do
		change := false;
		new_L := [];
		red_L:=List(LetterRepAssocWord(w),AbsInt);
		#Print("red_L: ",red_L,"\n");
		
		nb := 0;
		for l in red_L do
			if l = b then
				nb := nb +1;
			elif l = c then
				nb := nb +1;
				Add(new_L,d);
			else 
				Add(new_L,l);
			fi;
		od;
		w :=	alternating_a_form(AssocWordByLetterRep(FamilyObj(w),new_L));
		if IsOddInt(nb) then
			w := AssocWordByLetterRep(FamilyObj(w),[b])*w;
			b_exist := true;
		else 
			b_exist := false;
		fi;
	od;
	#Print("Before forced: ",w,"\n");
	#Force the word to begin with a (after the possable b) to gain a unique form.	
	if b_exist then
		w := Subword(w,2,Length(w));
	fi;
	if Length(w)>7 then 
		w:=Subword(w,1,Length(w) mod 8);
	fi;
	if Length(w)>0 and Subword(w,1,1) = AssocWordByLetterRep(FamilyObj(w),[d]) then
		w := Subword(AssocWordByLetterRep(FamilyObj(w),[a,d,a,d,a,d,a,d]),1,8-Length(w));
	fi;
	if b_exist then
		w := AssocWordByLetterRep(FamilyObj(w),[b])*w;
	fi;
	return w;
end;
#Given a word w in L_gen computes a word res in [a,b,c,d] such that <w,1>=res in Grig.
state_to_grig := function(w)
	local Pre,Res,a,b,c,d,x;
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	#Precomputed set:
	Pre := [[a,d,a],[b,a,d,a,b],[c,b,a,d,a,b,a,c,a,b,a,d,a,b,a,c,a,c],[b,a,d,a,b,a,c,a,b,a,d,a,b,a,c,a]];
	Res := [];
	for x in w do
		if x<0 then
			Append(Res,Reversed(Pre[-1*x]));
		else
			Append(Res,Pre[x]);
		fi;
	od;
	return Res;
end;
GRIG_CON := function(g,h)
local a,b,c,d,Fam,FR_Fam,aw,dw,ae,be,ce,de,Alph,x_1,x_2,K_repr,K_repr_words,D,ConTup_a,Check,Merge_Ls,conjugators_grig_rek,Res,r;
################################       (Local) GLOBALS           ####################################
	a:= 4;
	b:= 1;
	c:= 2;
	d:= 3;
	Fam := FamilyObj(g![2]);
	FR_Fam:= g![1];
	aw :=AssocWordByLetterRep(Fam,[a]);  
	dw :=AssocWordByLetterRep(Fam,[d]);
	ae := FRElement(FR_Fam,AssocWordByLetterRep(Fam,[a]));
	be := FRElement(FR_Fam,AssocWordByLetterRep(Fam,[b]));
	ce := FRElement(FR_Fam,AssocWordByLetterRep(Fam,[c]));
	de := FRElement(FR_Fam,AssocWordByLetterRep(Fam,[d]));
	Alph:=Alphabet(g);
	x_1 := Alph[1];
	x_2 := Alph[2];

	#Precomputed K-representatives:
	#[[],a,ad,ada,adad,adada,adadada,adadada,b,ba,bad,bada,badad,badada,badadad,badadada]
	K_repr := [[],[a],[a,d],[a,d,a],[a,d,a,d],[a,d,a,d,a],[a,d,a,d,a,d],[a,d,a,d,a,d,a],[b],[b,a],[b,a,d],[b,a,d,a],[b,a,d,a,d],[b,a,d,a,d,a],[b,a,d,a,d,a,d],[b,a,d,a,d,a,d,a]];
	K_repr_words := List(K_repr,x->AssocWordByLetterRep(Fam,x));
	
	#Precomputed words, which decompose to the K_repr.: <K_repr[i]·l,f(K_repr[i])·l'> = D[i]·<l,l'>
	D:= List([[],[c],[c,a,c,a],[c,a,c,a,c],[c,a,c,a,c,a,c,a],[c,a,c,a,c,a,c,a,c],[c,a,c,a,c,a,c,a,c,a,c,a],[c,a,c,a,c,a,c,a,c,a,c,a,c],[a,d,a],[a,d,a,c],[a,d,a,c,a,c,a],[a,d,a,c,a,c,a,c],[a,d,a,c,a,c,a,c,a,c,a],[a,d,a,c,a,c,a,c,a,c,a,c],[a,d,a,c,a,c,a,c,a,c,a,c,a,c,a],[a,d,a,c,a,c,a,c,a,c,a,c,a,c,a,c]],x->AssocWordByLetterRep(Fam,x));
	#%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%   Helping Functions    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	#TeporaryChek functin:
	Check := function(s,g,h,C)
		local c;
		for c in C do
			if g^c <> h then
				Print("Error at ",s,"\n");
				Print("Error happened here: g=",g,", and h=",h,", and Conjugator c=",c," number: ",Position(C,c),"in ",C,"\n");
				return 32;
			fi;
		od;
		return 42;
	end;
	#Computes the conjugator tuple for the pair (g,a): 
	ConTup_a := function (g)
		local g1,g1_modL,l,Allowed_reps,Connected_conjs,con_at_1,con_word,con,Centr_a,Con_tuple;
		if IsOne(Activity(g)) then
			return [];
		fi;
		if not IsOne(State(g,1)*State(g,2)) then
			return [];
		fi;
		g1 := State(g,1);
		#L_gen := [[b],[a,b,a],[b,a,d,a,b,a,d,a],[a,b,a,d,a,b,a,d]];
		g1_modL:=L_Decomposition(g1![2]); #ARGH... ![2] nich so gut...
		l:=g1_modL[2];
		g1_modL:=LetterRepAssocWord(g1_modL[1]);
		#See Lemma lem:conjugators_of_a for Details
		Allowed_reps:= [[],[a,d],[a,d,a,d,a,d],[a,d,a,d]];
		if not g1_modL in Allowed_reps then
			return [];
		fi;
		#See Lemma lem:conjugators_of_a for the appix conjugator
		Connected_conjs := [[],[c],[a,c],[c,a,c]];
		con := Connected_conjs[Position(Allowed_reps,g1_modL)];
		#resulting conjugator is of the form <l^((g_1modL^-1)),1>·con
		con_at_1 := compute_conjugates_of_word(l,Reversed(g1_modL));
		con_word := state_to_grig(con_at_1);
		Append(con_word,con);
		Info(InfoFRCP,4,"Conjugator in gen_L: <",con_at_1,",1>",con,"\nConjugator in gen_Grig: ",con_word,"\n");
		#Determine Cosets of K in which the conjugator lies.
		#See Roskov CP Lemma3 for centralizer of a
		Centr_a := List([[],[a],[a,d,a,d],[a,d,a,d,a]],x -> AssocWordByLetterRep(Fam,Concatenation(con_word,x)));
		Con_tuple:= [];
		for con in Centr_a do
			Con_tuple[Position(K_repr,LetterRepAssocWord(K_representant(con)))] := FRElement(FR_Fam,con);
		od;	
		Check("ConTup_a",g,ae,Con_tuple);
		return Con_tuple;
	end;	
	#Finds all Elements <l1,l2> with <l1,l2> in Grig, for l1 in L1, l2 in L2 and return result as Conjugator tuple.
	Merge_Ls := function(L1,L2,with_action)
		local aw_w,aw_t,dw_w,res_Con,i,x;	
		aw_w := One(aw);
		aw_t := ();
		dw_w := One(dw);
		if with_action then
			aw_w := aw;
			aw_t := (x_1,x_2);
		fi;
		Info(InfoFRCP,4,"Computing ",g,",",h,"  Sub Conjugators: ",L1,"\n");
		Info(InfoFRCP,4,"Computing ",g,",",h,"  Sub Conjugators: ",L2,"\n");
		#See Lemma 6.16 for <g1,g2<in Grig,  <=> g1=v(a,d)l g2=v(d,a)l
		#So <K_repr[i],K_repr[j]> in Grig  <=> j in [17-x mod 16 +1, 25-x mod 16 +1]
		res_Con := [];
		for i in [1..16] do
			if IsBound(L1[i]) then
				#Find second entry:
				for x in [((17-i) mod 16) +1,((25-i) mod 16) +1] do
					if IsBound(L2[x]) then
						if x>8 then
							dw_w := dw;
						else
							dw_w := One(dw);
						fi;
						Info(InfoFRCP,4,"Computing ",g,",",h,"  Conjugator found:",i,",",x,"\n");
						#Info(InfoFRCP,3,"Computing ",g,",",h,"    Found Elm: ",dw_w*D[i],"\n");
						#Info(InfoFRCP,3,"Computing ",g,",",h,"    corresp. Rep: ",K_representant(dw_w*D[i]),"\n");
						#Info(InfoFRCP,3,"Computing ",g,",",h,"    Insert at position: ",Position(K_repr_words,K_representant(dw_w*D[i])),"\n");
						if L1[i]=FRElement(FR_Fam,K_repr_words[i]) and L2[x]=FRElement(FR_Fam,K_repr_words[x]) then
							res_Con[Position(K_repr_words,K_representant(dw_w*D[i]*aw_w))] := FRElement(FR_Fam,dw_w*D[i]*aw_w);
						else #Could always compute the words as generators, but seems uneccassary
							res_Con[Position(K_repr_words,K_representant(dw_w*D[i]*aw_w))] := FRElement([[[L1[i]],[L2[x]]]],[aw_t],[1]);
						fi;
					fi;
				od;
			fi;
		od;
		return res_Con;
	end;

	conjugators_grig_rek := function(g,h)
		local Centr_bc, Centr_d, L1, L1_temp, L2, res_Con, g1, h1, x ,y;
		Info(InfoFRCP,3,"Compute Conjugator for pair: ",g,",",h,".\n");
		if Activity(g) <> Activity(h) then
			return [];
		fi;
		#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-   g = identity   -#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-
		if IsOne(g) then
			if IsOne(h) then
				return List(K_repr,x -> FRElement(FR_Fam,AssocWordByLetterRep(Fam,x)));
			fi;
				return [];
		fi;
		#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-   g in a,b,c,d    -#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-
		if g in [be,ce] then
			if h=g then
				Centr_bc := [[],,,,,,,[a,d,a,d,a,d,a],[b],,,,,,,[b,a,d,a,d,a,d,a]];
				return List(Centr_bc,x -> FRElement(FR_Fam,AssocWordByLetterRep(Fam,x)));
			fi;
		fi;
		if g = de then
			if h=g then
				Centr_d := [[],,,[a,d,a],[a,d,a,d],,,[a,d,a,d,a,d,a],[b],,,[b,a,d,a],[b,a,d,a,d],,,[b,a,d,a,d,a,d,a]];
				return List(Centr_d,x -> FRElement(FR_Fam,AssocWordByLetterRep(Fam,x)));
			fi;
		fi;
		if g=ae then
			return List(ConTup_a(h),x->x^-1);
		fi;
		if g in [be,ce,de] then
			if h in [be,ce,de,One(h),ae] then
				return []; #As g=h already considered in an earlier case
			fi;
			#----------------------------------    |h|>1     ----------------------------------------------
			#Test for Conjugator with trivial Activity
			L1 := conjugators_grig_rek(State(g,x_1),State(h,x_1));
			if Size(L1) > 0 then
				L2 := conjugators_grig_rek(State(g,x_2),State(h,x_2));
				res_Con := Merge_Ls(L1,L2,false);
				if Size(res_Con) >0 then
					Check("h>1 trivial",g,h,res_Con);
					return res_Con;
				fi;
			fi;		

			#Test for Conjugator with non-trivial Activity
			L1 := conjugators_grig_rek(State(g,x_1),State(h,x_2));
			if Size(L1) = 0 then
				return [];
			fi;
			L2 := conjugators_grig_rek(State(g,x_2),State(h,x_1));
			Check("h>1 nontrivial",g,h,Merge_Ls(L1,L2,true));
			return Merge_Ls(L1,L2,true);
		fi;
		#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-    |g| > 1, act(g) = 1    -#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-
		if IsOne(Activity(g)) then
		#Test for Conjugator with trivial Activity
			L1 := conjugators_grig_rek(State(g,x_1),State(h,x_1));
			if Size(L1) > 0 then
				L2 := conjugators_grig_rek(State(g,x_2),State(h,x_2));
				res_Con := Merge_Ls(L1,L2,false);
				if Size(res_Con) >0 then
					Check("g>1, act = 1, trivial",g,h,res_Con);
					return res_Con;
				fi;
			fi;	
			#Test for Conjugator with non-trivial Activity
			L1 := conjugators_grig_rek(State(g,x_1),State(h,x_2));
			if Size(L1) = 0 then
				return [];
			fi;
			L2 := conjugators_grig_rek(State(g,x_2),State(h,x_1));
			Check("g>1, act = 1, non-trivial",g,h,Merge_Ls(L1,L2,true));
			return Merge_Ls(L1,L2,true);
		else
		#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-    |g| > 1, act(g) = (1,2)    -#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-
			#Test for Conjugator with trivial Activity
			g1 :=State(g,x_1)^-1;
			h1 :=State(h,x_1);
			g1 := K_representant(g1![2]);
			h1 := K_representant(h1![2]);
			L1 := conjugators_grig_rek(State(g,x_1)*State(g,x_2),State(h,x_1)*State(h,x_2));
			if Size(L1) > 0 then
				res_Con := [];
				for x in L1 do
					#Force that only <x,g1xh1> is checked. #Seems to be a bit too complicated, may be simplified.
					L1_temp := [];
					L1_temp[Position(L1,x)]:=x;
					L2 := [];
					L2[Position(K_repr_words,K_representant(K_representant(g1)*K_repr_words[Position(L1,x)]*K_representant(h1)))] := State(g,x_1)^-1*x*State(h,x_1);
					L2 :=Merge_Ls(L1_temp,L2,false);
					for y in L2 do
						res_Con[Position(L2,y)] := y;
					od;
				od;
				if Size(res_Con) >0 then
				  Check("g>1, act = (1,2), trivial",g,h,res_Con);
					return res_Con;
				fi;
			fi;
			#Test for Conjugator with non-trivial Activity
			L1 := conjugators_grig_rek(State(g,x_1)*State(g,x_2),State(h,x_2)*State(h,x_1));
			if Size(L1) = 0 then
				return [];
			fi;
			res_Con := [];
			for x in L1 do
				#Force that only <x,g1xh1> is checked.
				L1_temp := [];
				L1_temp[Position(L1,x)]:=x;
				L2 := [];
				L2[Position(K_repr_words,K_representant(K_representant(g1)*K_repr_words[Position(L1,x)]*K_representant(h1)))] := State(g,x_1)^-1*x*State(h,x_1);
				L2 :=Merge_Ls(L1_temp,L2,true);
				for y in L2 do
					res_Con[Position(L2,y)] := y;
				od;
			od;
			Check("g>1, act = (1,2), non-trivial",g,h,res_Con);
			return res_Con;
		fi;
	end;

	Res:= conjugators_grig_rek(g,h);
	Info(InfoFRCP,3,"Result of rekursive computation: ",Res,"\n");
	for r in Res do
		if g^r<>h then
		 Print("Fatal Error....\n");
		 Print("Problem at ",Position(Res,r),"\n");
		fi;		
	od;
	if Size(Res) = 0 then
		return fail;
	fi;
	return Representative(Res);
end;
calc_dr := function(g)
	local a,b,c,d,K_repr,D,dw,i,Fam,FR_Fam;
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	Fam:=FamilyObj(g![2]);
	FR_Fam := g![1];
	
	K_repr := List([[],[a],[a,d],[a,d,a],[a,d,a,d],[a,d,a,d,a],[a,d,a,d,a,d],[a,d,a,d,a,d,a],[b],[b,a],[b,a,d],[b,a,d,a],[b,a,d,a,d],[b,a,d,a,d,a],[b,a,d,a,d,a,d],[b,a,d,a,d,a,d,a]],x->AssocWordByLetterRep(Fam,x) );
		D:= List([[],[c],[c,a,c,a],[c,a,c,a,c],[c,a,c,a,c,a,c,a],[c,a,c,a,c,a,c,a,c],[c,a,c,a,c,a,c,a,c,a,c,a],[c,a,c,a,c,a,c,a,c,a,c,a,c],[a,d,a],[a,d,a,c],[a,d,a,c,a,c,a],[a,d,a,c,a,c,a,c],[a,d,a,c,a,c,a,c,a,c,a],[a,d,a,c,a,c,a,c,a,c,a,c],[a,d,a,c,a,c,a,c,a,c,a,c,a,c,a],[a,d,a,c,a,c,a,c,a,c,a,c,a,c,a,c]],x->AssocWordByLetterRep(Fam,x));
	dw :=AssocWordByLetterRep(Fam,[d]);
	for i in [1..16] do 
		Print(i," | ",((17-i) mod 16) +1,",",((25-i) mod 16) +1," | ",K_representant(D[i]),",",K_representant(dw*D[i])," = ",Position(K_repr,K_representant(D[i])),",",Position(K_repr,K_representant(dw*D[i])),"\n");
	od;
end;

















