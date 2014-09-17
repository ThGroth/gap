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

