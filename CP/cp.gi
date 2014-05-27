InstallMethod(Conjugators,
	"Gives List of Conjugators out of given group for two objects in 'Permutation Group'",
	[ IsPermGroup, IsPerm, IsPerm],
  function(G, a, b )
 		local L,g;
		L:= [];
		for g in G do
			if a^g=b then
				Add(L,g);
			fi;
		od;
		return L;
  end
);

InstallMethod(IteratedOrbit,
	"Computes the Orbit of a word under <first>",
	[ IsFRElement, IsList],
  function(a, L )
		return Orbit(Group(a),L);
  end
);
InstallMethod(IteratedOrbit,
	"Computes the Orbit of the second argument under <first>",
	[ IsFRElement, IsInt],
  function(a, x )
		return Orbit(Group(a),x);
  end
);
InstallMethod(LevelPermConj,
	"Gives List of Conjugators of the action on the first level.",
	[IsFRElement, IsFRElement],
  function(x,y)
  	local pi_x, pi_y;
	if Alphabet(x) <> Alphabet(y) then
		Error("Not a valid argument, they must be defined on the same alphabet.");
		return [];
	fi;
	pi_x := PermList(DecompositionOfFRElement(x)[2]);
 	pi_y := PermList(DecompositionOfFRElement(y)[2]);
 	return Conjugators(SymmetricGroup(Alphabet(x)),pi_x,pi_y);
 	
  end
);

InstallMethod(OrbitSignalizer,
	"Returns the finite Orbit Signalizer for boundet Elements",
	[IsBoundedFRElement],
#  function(a)
#  	local a_states,C,N,Pot_OS,i,j,elm,elmdescr,OS,prefix;
#
#	a_states := States(a);
#	Add(a_states,One(a));
#	N := Size(a_states);
#	C := NormOfBoundedFRElement(a);
#
#	
#	OS := [];
#	for i in [0..N^C-1] do
#		elm := base_conversion(i,N);
#		prefix:= [];
#		for j in [1..C-Length(elm)] do
#			Add(prefix,0);
#		od;
#		elmdescr := Concatenation(prefix,elm);
#		elm := One(a);
#		for j in elmdescr do
#			elm := elm*a_states[j+1];
#		od;
#		#Test if elm in OS! TODO		
#		Add(OS,elm);#
#	od;
# 	return OS;	
#  end
function(a)
	local OS_list,i,OS_unvisited,OS_new,alphabet,elm,x,new,suc;
	suc := function(state,x)
		return  State(state^Size(IteratedOrbit(state,[x])),[x]);
	end;
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
end
);

 
RedispatchOnCondition(Conjugate_FS,true,[IsFRElement,IsFRElement],[IsBoundedFRElement,IsBoundedFRElement],0); 
InstallMethod(Conjugate_FS,
	"Checks if two bounded automorphisms are Conjugate in FAut",
	[ IsBoundedFRElement,IsBoundedFRElement],
  function(a,b)
 		local Graph, Vertices, v, h, Aut, PSI_Vertices, Get_Some_Vertex, Get_Vertex_By_Id, Find_Vertex_id, Conjugating_Graph, Vertices_To_Automaton;
 		PSI_Vertices := function(a,b)
			local OS_a, OS_b,V, c, d,CPI_cd, p, id;
			OS_a := OrbitSignalizer(a);	
			OS_b := OrbitSignalizer(b);
			V := [];
			id := 1;
			for c in OS_a do
				for d in OS_b do
					CPI_cd := LevelPermConj(c,d);
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
						Print("Not found...");
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
						Print("Not found...");
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
				Print("Not found...");
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
						Print("Not found...");
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
				x := List(O,Minimum);
				for i in [1..Length(O)] do
					cprime := State(c^Length(O[i]),x[i]);
					dprime := State(d^Length(O[i]),x[i]^pi);
					CPI_n := LevelPermConj(cprime,dprime);
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
		#	Print("\n\n Vertices:");
		#	for v in Psi do
		#		Print(v[4],", ");
		#	od;
		#	Print("\n\n Edges:");
		#	for v in Edges do
		#		Print([v[1],v[2],v[3]],", ");
		#	od;
			
			#Find Vertices with missing edges
			change:=true;
			while change do
				change := false;
				del := [];
				for v in Psi do
					v_id := v[4];
					O := Orbits(Group(v[1]),Alph);
					x := List(O,Minimum);
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
							#Print("At Vertex ",v[4]," no Edge ",i," was found. So remove it.\n");
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
		Vertices_To_Automaton := function(Vertices,Edges,start)
			local v, States,AutomStates, sons,s, e,O,Op,i, write, Transition, Outputs, newsons;
			States := [];
			AutomStates := [];
			for v in Vertices do
				sons:= [];
				write := [];
				for e in Edges do
					if e[1] = v[4] then
						sons[e[3]]:=e[2];
						write[e[3]]:=e[3]^v[3]; #Use Action of the vertex
				
						Op:= IteratedOrbit(v[1],e[3]);
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
				Add(AutomStates,v[4]);
				States[v[4]] := [v[4],v[1],v[2],v[3],sons,write];
			od;
			#Rename the States
			Transition := [];
			Outputs := [];
			for v in States do
				sons := v[5];
				newsons:= [];
				for s in sons do
					Add(newsons,[Position(AutomStates,s)]);
				od;
				Add(Transition,newsons);
				Add(Outputs,v[6]);
			od;
			start:=Position(AutomStates,start[4]);
						
			#return States;
			
			return FRElement(Transition,Outputs,[start]);
		end;

		Print("Computing Conjugating Graph..\n");
		Graph := Conjugating_Graph(a,b);
		Print("Done\n");
		Vertices := Graph[1];
		if Vertices = [] or Find_Vertex_id(Vertices,[a,b]) = 0 then
			return false;
		fi;
		
		v := Get_Some_Vertex(Vertices,[a,b]);
		Print("Hier kommt ein Graph mit ",Length(Graph[1])," Knoten und ",Length(Graph[2])," Kanten. \nVertices:\n",Graph[1],"\nEdges:\n",Graph[2],"\n","Startknoten soll ",v," sein.");
		Aut := Vertices_To_Automaton(Vertices,Graph[2],v);
	
	#	for v in Aut do
	#		Print("State ",v[1],": \n");
	#		ViewObj(v);
	#		Print("\n\n");
	#	od;
		if a^Aut = b then
			Print("Alles wunderbar\n");
		else Print ("Hm ein Fehler ist passiert\n");
		fi;
	return Aut;

  end
);


