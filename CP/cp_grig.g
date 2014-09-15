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
conjugate_to_a := function (g)
	local a,b,c,d,g1,g1_modL,l,Allowed_reps,Connected_conjs,con_at_1,con_word,con,Centr,Centr_con,Con_tuple,K_repr,Fam,FR_Fam;
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	if IsOne(Activity(g)) then
		return [];
	fi;
	if not IsOne(State(g,1)*State(g,2)) then
		return [];
	fi;
	g1 := State(g,1);
	#L_gen := [[b],[a,b,a],[b,a,d,a,b,a,d,a],[a,b,a,d,a,b,a,d]];
	g1_modL:=L_Decomposition(g1![2]); #ARGH... ![2] nich so gut...
	Fam := FamilyObj(g![2]);
	FR_Fam := g![1];
	l:=g1_modL[2];
	g1_modL:=LetterRepAssocWord(g1_modL[1]);
	#Print("g1_modL: ",g1_modL,"\n");
	#Print("l: ",l,"\n");
	Allowed_reps:= [[],[a,d],[a,d,a,d,a,d],[a,d,a,d]];
	if not g1_modL in Allowed_reps then
		return [];
	fi;
	#See Lemma 6.18 for the appix conjugator
	Connected_conjs := [[],[c],[a,c],[c,a,c]];
	con := Connected_conjs[Position(Allowed_reps,g1_modL)];

	con_at_1 := shorten_word(compute_conjugates_of_word(l,Reversed(g1_modL)));
	#Print("Conjugator in gen_L: <",con_at_1,",1>",con,"\n");
	con_word := state_to_grig(con_at_1);
	Append(con_word,con);
	#Print("Conjugator in gen_Grig: ",con_word,"\n");
	#Determine Cosets of K in which the conjugator lies.
	#See Roskov CP Lemma3 for centralizer of a
	Centr_con := List([[],[a],[a,d,a,d],[a,d,a,d,a]],x -> AssocWordByLetterRep(Fam,Concatenation(con_word,x)));
	#Enumeration of K_repr.:
	#[[],a,ad,ada,adad,adada,adadada,adadada,b,ba,bad,bada,badad,badada,badadad,badadada]
	K_repr := [[],[a],[a,d],[a,d,a],[a,d,a,d],[a,d,a,d,a],[a,d,a,d,a,d],[a,d,a,d,a,d,a],[b],[b,a],[b,a,d],[b,a,d,a],[b,a,d,a,d],[b,a,d,a,d,a],[b,a,d,a,d,a,d],[b,a,d,a,d,a,d,a]];
	Con_tuple:= [];
	for con in Centr_con do
		Con_tuple[Position(K_repr,LetterRepAssocWord(K_representant(con)))] := FRElement(FR_Fam,con);
	od;	
	#Some Final Test just to be shure....
	#Print(g,"\n");
	for con in Con_tuple do
		if g^con <> FRElement(FR_Fam,AssocWordByLetterRep(Fam,[a])) then
			Print("Ups.. das sollte nicht sein...\n");
		fi;
	od;
	return Con_tuple;
end;	





#Forget about this.... there is allot work to do left...
conjugators_grig_rek := function(g,h)
	local a,b,c,d,wg,wh,L1,L2,ae,be,ce,de,x_1,x_2,Alph;
	
	if (g=h) then
		return [One(g)];
	fi;
	if IsOne(g) then
		return []; #As h <> One
	fi;
	if Activity(g) <> Activity(h) then
		return [];
	fi;
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	ae := FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),[a]));
	be := FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),[b]));
	ce := FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),[c]));
	de := FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),[d]));
	Alph:=Alphabet(g);
	x_1 := Alph[1];
	x_2 := Alph[2];
	if (g=ae) then
		if (IsOne(State(h,x_1)*State(h,x_2))) then
				return [FRElement([[[State(h,x_1)],[]]],[()],[1])];
		else
				return [];
		fi;
	fi;
	if g in [be,ce,de] then
		if h in [be,ce,de] then
			return []; #As g<>h
		fi;
		L1 := conjugators_grig_rek(State(g,x_1),State(h,x_1));
		L2 := conjugators_grig_rek(State(g,x_2),State(h,x_2));
		if Size(L1) > 0 and Size(L2)>0 then
			return [FRElement([[[L1[1]],[L2[1]]]],[()],[1])];
		fi;
		L1 := conjugators_grig_rek(State(g,x_1),State(h,x_2));
		L2 := conjugators_grig_rek(State(g,x_2),State(h,x_1));
		if Size(L1) > 0 and Size(L2)>0 then
			return [FRElement([[[L1[1]],[L2[1]]]],[(x_1,x_2)],[1])];
		else
			return [];
		fi;
	fi;
	#So g is a word of length >1:
	if IsOne(Activity(g)) then
		L1 := conjugators_grig_rek(State(g,x_1),State(h,x_1));
		L2 := conjugators_grig_rek(State(g,x_2),State(h,x_2));
		if Size(L1) > 0 and Size(L2)>0 then
			return [FRElement([[[L1[1]],[L2[1]]]],[()],[1])];
		fi;
		L1 := conjugators_grig_rek(State(g,x_1),State(h,x_2));
		L2 := conjugators_grig_rek(State(g,x_2),State(h,x_1));
		if Size(L1) > 0 and Size(L2)>0 then
			return [FRElement([[[L1[1]],[L2[1]]]],[(x_1,x_2)],[1])];
		else
			return [];
		fi;
	else
		L1 := conjugators_grig_rek(State(g,x_1)*State(g,x_2),State(h,x_1)*State(h,x_2));
		if Size(L1) > 0 then
			return [FRElement([[[L1[1]],[State(g,x_1),L1[1],State(h,x_1)]]],[()],[1])];
		fi;
		L1 := conjugators_grig_rek(State(g,x_1)*State(g,x_2),State(h,x_2)*State(h,x_1));
		if Size(L1) > 0 then
			return [FRElement([[[L1[1]],[State(g,x_1),L1[1],State(h,x_2)]]],[(x_1,x_2)],[1])];
		else
			return [];
		fi;
	fi;
end;

