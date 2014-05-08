
InstallMethod( Conjugators,
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
  end;
);

InstallMethod(
