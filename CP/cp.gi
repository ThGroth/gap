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

RedispatchOnCondition(OrbitSignalizer,true,[IsFRElement],[IsBoundedFRElement],0);
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

InstallOtherMethod(OrbitSignalizer,
	"Returns the finite Orbit Signalizer for boundet Elements",
	[IsBoundedFRElement,IsString],
function(a,s)
	local OS_states,OS_Transitions,OS_Action,OS_states_unvisited,Elm_Ids,alphabet,OS_new,elm,elm_transitions,x, new, suc;
	suc := function(state,x)
		return  State(state^Size(IteratedOrbit(state,[x])),[x]);
	end;
	OS_states := [];
	OS_Transitions := [];
	OS_Action := [];
	OS_states_unvisited := [a];
	Elm_Ids := [a];
	alphabet := Alphabet(a);
	while Length(OS_states_unvisited) > 0 do
		OS_new := [];
		for elm in OS_states_unvisited do
			elm_transitions := [];
			for x in alphabet do
				new := suc(elm,x);
				if not new in Elm_Ids then
					Add(OS_new,new);
					Add(Elm_Ids,new);
				fi;
				Add(elm_transitions,[Position(Elm_Ids,new)]);
			od;
			Add(OS_Transitions,elm_transitions);
			Add(OS_Action,Activity(elm));
		od; 
		Append(OS_states,OS_states_unvisited);
		OS_states_unvisited := OS_new;
	od;
	return [OS_states,FRElement(OS_Transitions,OS_Action,[1])];
end
);

RedispatchOnCondition(Conjugate_FS,true,[IsFRElement,IsFRElement],[IsBoundedFRElement,IsBoundedFRElement],0); 
InstallMethod(Conjugate_FS,
	"Checks if two bounded automorphisms are Conjugate in FAut",
	[ IsBoundedFRElement,IsBoundedFRElement],
  function(a,b)
	local OS_a, OS_b, Vertices, Edges, c, d,CPI_cd, p, id, Alph, v, orbits, orb_repr, new_con_pair, new_action, new_v, change, found, e, all_found, i, j, tau, e_id, h, is_finished_subautom, Transitions, tran, orbit, New_Vertices, New_Edges, v_id, to_visit, AutomStates, start,actions,conjugator,Get_Vertex_by_Conj_Pair,Get_Vertex_by_Conj_Pair_and_action;
	
	

	
	
	Alph := Alphabet(a);
	OS_a := OrbitSignalizer(a);	
	OS_b := OrbitSignalizer(b);
	Vertices := [];
	Edges := [];
	#--------------------- Generate the Vertex list -------------------
	v_id := 1;
	for c in OS_a do
		for d in OS_b do
			CPI_cd := LevelPermConj(c,d);
			for p in CPI_cd do
				Add(Vertices,rec(	id:= v_id,
													conj_pair := [c,d],
													action := p));
				v_id := v_id+1;
			od;
		od;
	od;
	#Print("Vertexlist generated\n");
	
	#Finds the first Vertex in Vertices with the given Conj_Pair. If There is no such Pair, false is returned.
	Get_Vertex_by_Conj_Pair := function(Conj_Pair)
		local v;
		for v in Vertices do
			if v.conj_pair = Conj_Pair then;
				return v;
			fi;
		od;
		#Error("Not found...");
		return false;
	end;
	Get_Vertex_by_Conj_Pair_and_action := function(Conj_Pair,v_action)
		local v;
		for v in Vertices do
			if v.conj_pair = Conj_Pair and v.action = v_action then;
				return v;
			fi;
		od;
		#Error("Not found...");
		return false;
	end;
	#--------------------- Find the Edges  -------------------
	e_id := 1;
	for v in Vertices do
		#Print("Looking at ",v.id,"\n");
		c := v.conj_pair[1];
		d := v.conj_pair[2];
		orbits := Orbits(Group(c),Alph);
		#Print("orbits: ",orbits,"\n");
		orb_repr := List(orbits,Minimum);
		for i in [1..Length(orbits)] do
			new_con_pair := [State(c^Length(orbits[i]),orb_repr[i]),State(d^Length(orbits[i]),orb_repr[i]^v.action)];
			new_action := LevelPermConj(new_con_pair[1],new_con_pair[2]);
			for tau in new_action do
				new_v := Get_Vertex_by_Conj_Pair_and_action(new_con_pair,tau);
				if new_v <> 0 then
					#Print("Add Edge from ",v.id," to ",new_v.id," along ",orb_repr[i],"\n");
					Add(Edges,rec(	from:=v.id,
													to := new_v.id,
													read := orb_repr[i],
													write := orb_repr[i]^v.action,
													id := e_id));
					e_id := e_id +1;	
				else
					Error("Error the element is not in the vertex set!\n");
				fi;
			od;
		od;
	od;
	#Print("Edges generated\n");
	#Print("Very Long lists:\n\n","Vertices: ",Vertices,"\n\n Edges:",Edges,"\n");
	
	#--------------------- Delete dead Vertices  -------------------
	change:=true;
	while change do
		change := false;
		for v in Vertices do
			orbits := Orbits(Group(v.conj_pair[1]),Alph);
			orb_repr := List(orbits,Minimum);
			found := [];
			for e in Edges do
				if e.from = v.id then
					Add(found,e.read);
				fi;
			od;
			#Are all outgoing edges there?
			all_found := true;
			for i in orb_repr do
				if not i in found then
					all_found := false;
					#"At Vertex ",v[4]," no Edge ",i," was found. So remove it.\n");
					break;
				fi;
			od;
			if not all_found then
				Unbind(Vertices[v.id]);
				#Delete all Edges from or to the removed vertex
				for e in Edges do
					if e.from = v.id or e.to = v.id then
						Unbind(Edges[e.id]);
					fi;
				od;
				change:=true;
			fi;
		od;
	od;
	#Print("Dead Vertices removed\n");
	#Print("Complete Graph\n\n","Vertices: ",Vertices,"\n\n Edges:",Edges,"\n");
	#--------------------- Check wheater a and b are conjugate ------
	start := Get_Vertex_by_Conj_Pair([a,b]);
	if start = false then
		#a and b are not conjugate, so return false;
		#Print("Kein Startknoten mehr");
		return false;
	fi;
	#--------------------- Choose one subgraph, as automaton  -------------------
	AutomStates := [start.id]; #Contains IDs of vertices, which build the subgraph
	to_visit := [start.id]; 
	while Length(to_visit) > 0 do 
		new_v := [];
		for i in to_visit do
			v:= Vertices[i];
			found := ShallowCopy(Alph);
			for e in Edges do
				if e.from = v.id then
					if found[e.read] = true	then
						Unbind(Edges[e.id]);
					else 
						found[e.read] := true;
						if not e.to in AutomStates then
							Add(new_v,Vertices[e.to].id);
							Add(AutomStates,e.to);
						fi;
					fi;
				fi;
			od;
		od;
		to_visit := new_v;
	od;
	#Print("Long lists:\n","Start: ",start.id,"\nAutomstates: ",AutomStates,"\n\n","Vertices: ",Vertices,"\n\n Edges:",Edges,"\n");
	
	#Print("Subgraph choosen\n");
	#------------------- Shorten all Lists, and rename the ids s.t. they fit 
	
	New_Edges := [];
	e_id := 1;
	for e in Edges do
		if e.from in AutomStates and e.to in AutomStates then
			e.from := Position(AutomStates,e.from);
			e.to := Position(AutomStates,e.to);
			e.id := e_id;
			Add(New_Edges,e);
			e_id := e_id +1;	
		fi;
	od;
	Edges := New_Edges;
	v_id := 1;
	New_Vertices := [];
	for i in AutomStates do
		v := Vertices[i];
		v.id := v_id;
		Add(New_Vertices,v);
		v_id := v_id +1;
	od;
	Vertices := New_Vertices;
	AutomStates := [1..Length(AutomStates)];
	#Print("Short lists:\n","Automstates: ",AutomStates,"\n\n","Vertices: ",Vertices,"\n\n Edges:",Edges,"\n");

	#------------------------- Generate Transitions ----------------------------
	Transitions := [];
	actions := [];
	for i in AutomStates do
		tran := [];
		for e in Edges do
			if e.from = i then
				tran[e.read] := [e.to];
				#Mark the missing edges in the orbit of e.read under c
				c := Vertices[i].conj_pair[1];
				d := Vertices[i].conj_pair[2];
				orbit:=IteratedOrbit(c,e.read);
				for j in [2..Length(orbit)] do
					tran[orbit[j]] := [State(c^(j-1),e.read)^(-1),e.to,State(d^(j-1),e.read^(Vertices[i].action))];
				od;
			fi;
		od;
		Add(Transitions,tran);
		Add(actions,Vertices[i].action);
	od;
	#Print("Transitions generated\n");
	#Print("transitions: \n", Transitions,"\n");
	
	
	
	conjugator := FRElement(Transitions,actions,[start.id]);
	#Print("Short check, if everything is OK.\n");
	if a^conjugator = b then
		return conjugator;
	else
		Print("Komischer Fehler...\n");
		return false;
	fi;
end
);


