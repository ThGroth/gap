LoadPackage("fr");
Read("~Reps/git/gap/try/helping_functions.g");

FG_conjugating_elements := function (G,a,b)
	local L,g;
	L:= [];
	for g in G do
		if a^g=b then
			Add(L,g);
		fi;
	od;
	return L;
end;


Grig := FRGroup("f=<g,c>","g=<h,c>","h=<f,1>","c=<1,1>(1,2)");
AssignGeneratorVariables(Grig); 
CPI := function(x,y)
	local pi_x, pi_y;
	if not(IsFRElement(x) and IsFRElement(y)) then
		Print("# Not a valid argument for CPI");
		return [];
	fi;
	if Alphabet(x) <> Alphabet(y) then
		Print("# Not a valid argument for CPI, they must be defined on the same alphabet.");
		return [];
	fi;
	pi_x := PermList(DecompositionOfFRElement(x)[2]);
 	pi_y := PermList(DecompositionOfFRElement(y)[2]);
 	return FG_conjugating_elements(SymmetricGroup(Alphabet(x)),pi_x,pi_y);
 	
end;
OrbitSignalizer := function(a)
	if a=f then
		return [One(Grig),f,g,h,c];
	fi;
	if a=g then 
		return [One(Grig),f,g,h,c];
	fi; 
end;
PSI_Vertices := function(a,b)
	local OS_a, OS_b,V, c, d,CPI_cd, p, id;
	OS_a := OrbitSignalizer(a);	
	OS_b := OrbitSignalizer(b);
	V := [];
	id := 1;
	for c in OS_a do
		for d in OS_b do
			CPI_cd := CPI(c,d);
			for p in CPI_cd do
				Add(V,[c,d,p,id]);
				id := id+1;
			od;
		od;
	od;
	return V;						
end;
#Given v_1, v_2 looks for a vertex (v1,v2,pi,id) for some pi,id
Get_Some_Vertex := function(Vertices, vertex)
local v;
		for v in Vertices do
			if v[1]=vertex[1] and v[2] = vertex[2] then
				return v;
			fi;
		od;
		#		Print("Not found...");
		#		ViewObj(vertex);
		#		Print("\n");
		return 0;
end;
Get_Vertex_By_Id := function(Vertices, id)
local v;
		for v in Vertices do
			if v[4]=id then
				return v;
			fi;
		od;
		#		Print("Not found...");
		#		ViewObj(vertex);
		#		Print("\n");
		return 0;
end;
Find_Vertex_id:= function (Vertices,vertex)
	local v;
	if Length(vertex) = 3 then
		for v in Vertices do
			if v[1]=vertex[1] and v[2] = vertex[2] and v[3] = vertex[3] then
				return v[4];
			fi;
		od;
#		Print("Not found...");
#		ViewObj(vertex);
#		Print("\n");
		return 0;
	fi;
	if Length(vertex) = 2 then
		for v in Vertices do
			if v[1]=vertex[1] and v[2] = vertex[2] then
				return v[4];
			fi;
		od;
		#		Print("Not found...");
		#		ViewObj(vertex);
		#		Print("\n");
		return 0;
	fi;
	Print("Not a valid Vertex...");
	ViewObj(vertex);
	Print("\n");
	return 0;
end;
Conjugating_Graph := function(a,b)
	local Alph, Psi, e,Edges, v,v_id, c, d, pi, O, x, i, cprime, dprime, CPI_n, tau, change, del, found, all_found,new_v;
	Alph := Alphabet(a);
	Psi := PSI_Vertices(a,b);
	Edges:= []; #Edges in Form (id_v1, id_v2, label)
	for v in Psi do
		v_id := v[4];
		c := v[1];
		d := v[2];
		pi := v[3];
		O := Orbits(Group(c),Alph);
		x := map(O,Minimum);
		for i in [1..Length(O)] do
			cprime := State(c^Length(O[i]),x[i]);
			dprime := State(d^Length(O[i]),x[i]^pi);
			CPI_n := CPI(cprime,dprime);
			for tau in CPI_n do
				new_v := Find_Vertex_id(Psi,[cprime,dprime,tau]);
				if new_v <> 0 then
					Add(Edges,[v_id,new_v,x[i],c]);	
				else
					Print("Error the element is not in the vertex set!\n");
				fi;
			od;
		od;
	od;
	#Find Vertices with missing edges
	change:=true;
	while change do
		change := false;
		del := [];
		for v in Psi do
			v_id := v[4];
			O := Orbits(Group(v[1]),Alph);
			x := map(O,Minimum);
			found := [];
			for e in Edges do
				if e[1] = v_id then
					Add(found,e[3]);
				fi;
			od;
			all_found := true;
			for i in x do
				if not i in found then
					all_found := false;
					break;
				fi;
			od;
			if not all_found then
				Add(del,v);
				change:=true;
			fi;
		od;
		if change then
			#Delete this vertices
			for d in del do
				Remove(Psi,Position(Psi,d));
			od;
			#Delete all edges from or to this vertices
			for i in [1..Length(del)] do
				del[i] := del[i][4];
			od;
			for e in Immutable(Edges) do
				if e[1] in del or e[2] in del then
					Remove(Edges,Position(Edges,e));
				fi;
			od;
		fi;
	od;
	return [Psi,Edges];
end;
#Computes a new Graph out of V and E.
#The i-th vertex is [i,[c,d,pi],[suc_1, suc_2, ... suc_d],[wri_1,wri_2,..,wri_d]]
Vertices_To_Automaton := function(Vertices,Edges,start)
	local v, States, sons, e,O,Op,i, write;
	States := [];
	for v in Vertices do
		sons:= [];
		write := [];
		for e in Edges do
			if e[1] = v[4] then
				sons[e[3]]:=e[2];
				write[e[3]]:=e[3]^v[3]; #Use Action of the vertex
				
				Op:= Orbit(Group(v[1]),e[3]);
				O := List(Op);
				Sort(O);
				# O[1] = x1 = e[3]
				for i in [2..Length(O)] do
					sons[O[i]]:=e[2];
					#Calculate action
					
					write[O[i]] :=((O[i]^(State(v[1]^i,e[3])^(-1)))^v[3])^State(v[2]^i,e[3]^start[3]); 	
				od;
			fi;
		od;
		States[v[4]] := [v[4],v[1],v[2],v[3],sons,write];
	od;
	return States;
end;

Conjugate_FS := function(a,b)
	local Graph, Vertices,v,h,Aut;
	Print("Computing Conjugating Graph..\n");
	Graph := Conjugating_Graph(a,b);
	Print("Done\n");
	Vertices := Graph[1];
	if Vertices = [] or Find_Vertex_id(Vertices,[a,b]) = 0 then
		return false;
	fi;
		
	v := Get_Some_Vertex(Vertices,[a,b]);
	Aut := Vertices_To_Automaton(Vertices,Graph[2],v);
	
	for v in Aut do
	Print("State ",v[1],": \n");
	ViewObj(v);
	Print("\n\n");
	od;
	
	return Aut;
	
end;
