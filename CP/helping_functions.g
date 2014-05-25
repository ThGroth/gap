map :=function(list,func)
	local i, a,newlist;
	newlist := [];
	for a in list do
		Add(newlist,func(a));
	od;
	return newlist;
end;
map_r := function(list,func)	
	local i, a,newlist;
	newlist := [];
	for a in list do
		if IsList(a) then	
			Add(newlist,map_r(a,func));
		else	
			Add(newlist,func(a));
		fi;
	
		
	od;
	return newlist;
end;

red := function(func,val)
	local newfunc,x;
	newfunc := function(x)
		return func(x,val);
	end;
	return newfunc;
end;
commu := function(a,b)
	return a^(-1)*b^(-1)*a*b;
end;
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

