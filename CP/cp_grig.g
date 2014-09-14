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
end;
L_representant := function(w)
	local a,b,c,d,k,l,L,red_L,new_L,change;
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
		Print("red_L: ",red_L,"\n");
		
		for l in red_L do
			if l = b then
				change := true;
			elif l = c then
				change := true;
				Add(new_L,d);
			else Add(new_L,l);
			fi;
		od;
		w :=	alternating_a_form(AssocWordByLetterRep(FamilyObj(w),new_L));
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
		Print("red_L: ",red_L,"\n");
		
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
	Allowed_reps:= [AssocWordByLetterRep(FamilyObj(g![2]),[]),AssocWordByLetterRep(FamilyObj(g![2]),[a,d]),AssocWordByLetterRep(FamilyObj(g![2]),[d,a]),AssocWordByLetterRep(FamilyObj(g![2]),[a,d,a,d])];
	Connected_conjs := [One(g),FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),[c])),FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),[a,c])),FRElement(g![1],AssocWordByLetterRep(FamilyObj(g![2]),[c,a,c]))];
	if not g1_modL in Allowed_reps then
		return false;
	fi;
	con_con := Connected_conjs[Position(Allowed_reps,g1_modL)];
	Print("Position: ",Position(Allowed_reps,g1_modL),"\n");
	Print("Cnnected... :",Connected_conjs,"\n");
	Print("con_con: ",con_con,"\n");
	Print("g1_modL: ",g1_modL,"\n");
	Print("g1: ",g1,"\n");
	g1_modL := FRElement(g![1],g1_modL);
	Print("g1:modL_fr: ",g1_modL,"\n");
	con :=FRElement([[[g1*g1_modL^-1],[]]],[()],[1])*con_con;
	K_reprent
	return 
end;	

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

