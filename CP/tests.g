Te := FRElement(["a","b","c","k1","k2","k3"],[[[2],[2]],[[3],[4]],[[],[]],[[3],[5]],[[3],[6]],[[3],[4]]],[(),(),(1,2),(),(1,2),(1,2)],[1]);

#a := FRElement(["a","b","c"],[[[2],[1]],[[],[3]],[[],[]]],[(1,2),(),(1,2)],[1]);
#b := FRElement(["a","b","c"],[[[2],[1]],[[],[3]],[[],[]]],[(1,2),(),(1,2)],[2]);
#c := FRElement(["a","b","c"],[[[2],[1]],[[],[3]],[[],[]]],[(1,2),(),(1,2)],[3]);

suc := function(state,x)
	return  State(state^Size(IteratedOrbit(state,[x])),[x]);
end;

OSe := function(state,word)
	return State(state^Size(IteratedOrbit(state,word)),word);
end;

OS := function(a)
	local OS_list,i,OS_unvisited,OS_new,alphabet,elm,x,new;
	OS_list := [];
	OS_unvisited := [a];
	alphabet := Alphabet(a);
	while Length(OS_unvisited) > 0 do
		OS_new := [];
		for elm in OS_unvisited do
			for x in alphabet do
				new := suc(elm,x);
				if (not new in OS_list) and (not new in OS_unvisited) and (not new in OS_new) then
					Add(OS_new,new);
				fi;
			od;
			
		od; 
		Append(OS_list,OS_unvisited);
		OS_unvisited := OS_new;
	od;
	return OS_list;
	
	
end;

elmmult := function(L)
	local x,l;
	x := One(f);
	for l in L do
		x := x * l;
	od;
	return x;
end;
	
	
decompose := function(x,gen,genwords)
	local W,NewW,Wo,NewWo,w,a,found;
	W:=[[One(x)]];
	Wo := [["1"]];
	found := false;
	while not found do
		NewW := [];
		NewWo := [];
		for w in [1..Length(W)] do
			for a in [1..Length(gen)] do
				Add(NewW,Concatenation(W[w],[gen[a]]));
				Add(NewWo,Concatenation(Wo[w],[genwords[a]]));
				if elmmult(W[w]) = x then
					found := true;
					Print(NewWo[w]);
					break;
				fi;
			od;
			if found then
				break;
			fi;
		od;
		Wo := NewWo;
		W := NewW;
	od;	
end;

