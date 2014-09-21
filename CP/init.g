InfoFRCP := NewInfoClass("InfoFRCP");
SetInfoLevel(InfoFR, 1);

if not IsBound(AlreadyRead@) then
	ReadPackage("fr","gap/CP/cp.gd");
	ReadPackage("fr","gap/CP/cp_branch.gd");
fi;
ReadPackage("fr","gap/CP/cp.gi");
ReadPackage("fr","gap/CP/examples.g");
ReadPackage("fr","gap/CP/cp_grig.g");
ReadPackage("fr","gap/CP/cp_branch.g");
ReadPackage("fr","gap/CP/helping_functions.g");

