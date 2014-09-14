
#Testelements

#Grig
b := FRElement(["b","c","d","a"],[[[4],[2]],[[4],[3]],[[],[1]],[[],[]]],[(),(),(),(1,2)],[1]);
c := State(b,2);
d := State(c,2);
a := State(b,1);


adding_machine := FRElement([[[],[1]]],[(1,2)],[1]);
finitary := FRElement(["fin"],[[[a],[]]],[(1,2)],[1]);
nonfin := FRElement(["nin"],[[[1],[a]]],[()],[1]); 

aut_inf_order := FRElement([[[1,1],[1]]],[(1,2)],[1]);#Be carefull this are not bounded...
afin := FRElement(["c","d","e","f","id",],[[[2],[4]],[[],[3]],[[],[3]],[[],[]],[[],[]]],[(1,2),(),(1,2),(1,2),()],[1]);
z := FRElement(["z"],[[[1],[1]]],[(1,2)],[1]);
degtwo := FRElement(["d2","d1"],[[[1],[2]],[[2],[]]],[(),(1,2)],[1]);

add_10 := FRElement([[[],[],[],[],[],[],[],[],[],[1]]],[(1,2,3,4,5,6,7,8,9,10)],[1]);
add_4 := FRElement(["a4"],[[[],[],[],[1]]],[(1,2,3,4)],[1]);
bounded_4 := FRElement(["b4","c4"],[[[],[],[],[2]],[[2],[],[],[]]],[(),(1,2,3,4)],[1]);

Elms := [[b,"b"],[c,"c"],[d,"d"],[a,"a"],[adding_machine,"adding_machine"],[finitary,"finitary"],[nonfin,"nonfin"],[add_10,"add_10"],[add_4,"add_4"],[bounded_4,"bounded_4"]];
#Groups
RAut_bin := FullSCGroup([1,2],IsFRElement);
FAut_bin := FullSCGroup([1,2],IsFiniteStateFRElement);
Poly0_bin := FullSCGroup([1,2],IsBoundedFRElement);
FINAut_bin := FullSCGroup([1,2],IsFinitaryFRElement);
RAut_4 := FullSCGroup([1,2,3,4],IsFRElement);
Grig := Group(States(b));

Groups := [[RAut_bin,"RAut_bin"],[FAut_bin,"FAut_bin"],[Poly0_bin,"Poly0_bin"],[FINAut_bin,"FINAut_bin"],[RAut_4,"RAut_4"]];


Test@ := function()
	local G,a,b,con;
#alle Elemente an allen Gruppen testen...
	Print("This may take some time....");
	for G in Groups do
		Print("Check Conjugacy in Group ",G[2],":\n\n");
		for a in Elms do
			for b in Elms do
				Print("IsConjugate(",a[2],",",b[2],"): ",IsConjugate(G[1],a[1],b[1]),"\n");
				Print("PrepresentativeActionOP(",a[2],",",b[2],"): ");
				con := RepresentativeActionOp(G[1],a[1],b[1]);
				if con = fail then 
					Print("fail\n");
				else
					if a[1]^con = b[1] then 
						Print("found ");
					else
						Print("Error false positive!!!!!!");
					fi;
					if FullSCFilter(G[1])(con) then
						Print("with nec. Property\n");
					else
						Print("Not in ",G[2],"!!!!!!\n");
					fi;
				fi;
			od;
		od;		
	od;
end;

