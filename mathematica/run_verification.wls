#!/usr/bin/env wolframscript
root = DirectoryName[ExpandFileName[$InputFileName]];
Get[FileNameJoin[{root,"Chern4Verifier.wl"}]];
result = Chern4Verifier`VerifyChern4[root];
Print[result];
If[AssociationQ[result] && TrueQ[Lookup[result,"EndpointCertified",False]],
 Exit[0], Exit[1]];
