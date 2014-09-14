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
		result:=Check_Prop_on_words(G_with_inverse,g -> e=g,radius);
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
	red_L:=LetterRepAssocWord(w);
	
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
	return AssocWordByLetterRep(FamilyObj(w),red_L);
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
K_representant := function(w)
	local a,b,c,d,k,l,L,red_L,new_L,change,nb;
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
			else Add(new_L,l);
			fi;
		od;
		w :=	alternating_a_form(AssocWordByLetterRep(FamilyObj(w),new_L));
		if IsOddInt(nb) then
				w := AssocWordByLetterRep(FamilyObj(w),[b])*w;
		fi;
	od;
	return w;
end;
conjugate_to_a := function (g)
	local a,b,c,d,g1,g1_modL,Allowed_reps,Connected_conjs,con_con,con;
	a:=4;
	b:=1;
	c:=2;
	d:=3;
	if IsOne(Activity(g)) then
		return false;
	fi;
	if not IsOne(State(g,1)*State(g,2)) then
		return false;
	fi;
	g1 := State(g,1);
	g1_modL:=L_representant(g1![2]);
	Allowed_reps:= List([[],[a,d],[a,d,a,d,a,d],[a,d,a,d]],x -> AssocWordByLetterRep(FamilyObj(g![2]),x));
	Connected_conjs := List([[],[c],[a,c],[c,a,c]],x ->FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),x)));
	if not g1_modL in Allowed_reps then
		return false;
	fi;
	con_con := Connected_conjs[Position(Allowed_reps,g1_modL)];

	g1_modL := FRElement(g![1],g1_modL);

	con :=FRElement([[[g1*g1_modL^-1],[]]],[()],[1])*con_con;
	con := K_representant(Grig_element_as_word_over_G(con,List([[b],[c],[d],[a]],x ->FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),x))),Fam));
	return con;
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

