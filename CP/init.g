InfoFRCP := NewInfoClass("InfoFRCP");
SetInfoLevel(InfoFR, 1);

if not IsBound(AlreadyRead@) then
	ReadPackage("fr","gap/CP/cp.gd");
fi;
ReadPackage("fr","gap/CP/cp.gi");
ReadPackage("fr","gap/CP/examples.g");
