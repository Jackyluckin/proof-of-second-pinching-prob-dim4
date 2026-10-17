(* ::Package:: *)
(* Exact verification of the algebraic endpoint in
   "A computer-assisted proof of the second pinching theorem in dimension four".
   Data are included in the accompanying directory. No Python, numerical
   optimiser, floating-point eigensolver, or network connection is used.
   Tensor inner products sum over all ordered indices. *)

BeginPackage["Chern4Verifier`"];
VerifyChern4::usage =
 "VerifyChern4[] reconstructs the endpoint by two independent formulas and verifies the complete rational certificate. VerifyChern4[dir] uses the specified package directory.";
VerifyChern4SelfTests::usage =
 "VerifyChern4SelfTests[] runs deterministic tests of the monomial bookkeeping, exact Bernstein transforms and fail-closed checking.";
Begin["`Private`"];

$PackageDirectory = DirectoryName[ExpandFileName[$InputFileName]];
$EndpointHash = "e1426dde5d49594a2303ebf38d5c37b1a5001493c83770678874af87e3c86131";
$CertificateHash = "70f8aa19d9df2bda362a0873cbd45a9c2a4e6324c2f3b422a29376b013d88a48";
$Tag = "Chern4ExactVerificationFailure";
$Verbose = True;

fail[label_, details_:Null] := Throw[
 Failure["VerificationFailed", <|"Check"->label, "Details"->details|>], $Tag];
require[condition_, label_, details_:Null] := If[! TrueQ[condition], fail[label,details]];
zeroQ[expr_] := AllTrue[Flatten[{Expand[expr]}], # === 0 &];
exactRationalQ[x_] := IntegerQ[x] || Head[x] === Rational;
note[args___] := If[TrueQ[$Verbose], Print[args]];
writeResult[expr_,path_] := Module[{tmp=path<>".tmp-"<>CreateUUID[]},
 Check[Put[expr,tmp];RenameFile[tmp,path,OverwriteTarget->True],
   fail["atomic report write",path]]];

(* Integer strings are parsed as digits, never evaluated as Wolfram code. *)
readInteger[x_Integer] := x;
readInteger[s_String] := Module[{minus, body},
 require[StringMatchQ[s, RegularExpression["-?[0-9]+"]], "integer encoding",s];
 minus=StringStartsQ[s,"-"]; body=If[minus,StringDrop[s,1],s];
 If[minus,-1,1] FromDigits[body]
];
readInteger[x_] := fail["noninteger input",x];
readJSON[path_String] := Module[{a},
 require[FileExistsQ[path],"file exists",path];
 a=Check[Import[path,"RawJSON"],fail["JSON import",path]];
 require[AssociationQ[a],"JSON object",path]; a
];
fileHash[path_String] := ToLowerCase[FileHash[path,"SHA256","HexString"]];
combinations[n_,k_] := (#-Range[0,k-1]&)/@Subsets[Range[n+k-1],{k}];

(* Each coordinate carries its principal-frame sign character in F_2^4.
   The first four coordinates omit an index; the remaining eight form
   four repeated-singleton groups, two coordinates in each group. *)
bookkeeping[] := Module[{chars,mon,classes,blocks,pos,quart,labels,weights,counts,byblock,qOf},
 chars={14,13,11,7,1,1,2,2,4,4,8,8};
 mon=combinations[12,2];
 classes=Sort[DeleteDuplicates[(BitXor@@chars[[#]]&)/@mon]];
 blocks=Table[Select[Range[Length[mon]],(BitXor@@chars[[mon[[#]]]])===c&],{c,classes}];
 pos=Flatten[Table[Prepend[#,b]&/@combinations[Length[blocks[[b]]],2],{b,Length[blocks]}],1];
 qOf[vec_] := Module[{b,i,j,pair1,pair2},
   {b,i,j}=vec;pair1=mon[[blocks[[b,i]]]];pair2=mon[[blocks[[b,j]]]];
   Sort[Join[pair1,pair2]]
 ];
 quart=Sort[DeleteDuplicates[qOf/@pos]];
 labels=(First[FirstPosition[quart,qOf[#]]]&)/@pos;
 weights=If[#[[2]]===#[[3]],1,2]&/@pos;
 counts=Table[Total[Pick[weights,labels,k]],{k,Length[quart]}];
 byblock=Table[Flatten[Position[pos[[All,1]],b]],{b,Length[blocks]}];
 require[Length[mon]===78 && Length[pos]===442 && Length[quart]===196,
   "monomial dimensions"];
 require[Length/@blocks==={16,9,9,9,9,9,9,8},"sign block dimensions"];
 <|"Monomials"->mon,"Blocks"->blocks,"Positions"->pos,"Quartics"->quart,
   "Labels"->labels,"Weights"->weights,"Counts"->counts,"ByBlock"->byblock|>
];

(* Spectral coverage: permutations and reversal act on the three
   Hadamard coordinates as every signed permutation. Sorting their
   absolute values and dividing by the largest gives (1,r,r y),
   0<=r,y<=1; if the second coordinate is zero, take y=0. *)
checkSpectralGroup[] := Module[{hh,p4,p3,a,b},
 hh={{1,1,1},{1,-1,-1},{-1,1,-1},{-1,-1,1}}/2;
 p4=Permutations[Range[4]];p3=Permutations[Range[3]];
 a=Sort[DeleteDuplicates[Flatten[Table[sgn*Transpose[hh].(hh[[perm]]),
     {sgn,{-1,1}},{perm,p4}],1]]];
 b=Sort[DeleteDuplicates[Flatten[Table[DiagonalMatrix[sgn].(IdentityMatrix[3][[perm]]),
     {sgn,Tuples[{-1,1},3]},{perm,p3}],1]]];
 require[Transpose[hh].hh===IdentityMatrix[3],"Hadamard orthonormality"];
 require[Length[a]===48 && a===b,"complete signed-permutation action"];
 True
];

(* Symbolic unnormalised tensors. N is a positive sum of squares for
   nonzero amplitudes. The 2x2 minor of rows 2,3 of the repeated basis
   is (1+r)^2, so all fibres, including repeated spectra, are covered. *)
makeChart[] := Module[{r,y,x,ell,ls,mm3,mm4,cc,tt,nn,rr,dd,aa,bb,cs,idx,ii,kk},
 r=Unique["r"]; y=Unique["y"]; x=Table[Unique["x"],{12}];
 ell={1+r+r*y,1-r-r*y,-1+r-r*y,-1-r+r*y};
 ls=Expand[ell.ell];mm3=Expand[Total[ell^3]];mm4=Expand[Total[ell^4]];
 cc={{-1+r*y,-r+r*y},{1+r,0},{0,1+r},{-r-r*y,-1-r*y}};
 tt=Table[idx=Sort[{i,j,k}];
   If[Length[DeleteDuplicates[idx]]===3,x[[First[Complement[Range[4],idx]]]],
    {ii,kk}=If[idx[[1]]===idx[[2]],{idx[[1]],idx[[3]]},{idx[[3]],idx[[1]]}];
    cc[[ii]].x[[{2*kk+3,2*kk+4}]]],{i,4},{j,4},{k,4}];
 nn=Expand[Total[Flatten[tt]^2]];
 rr=Table[Expand[Sum[tt[[i,j,k]]*tt[[i,j,l]],{i,4},{j,4}]],{k,4},{l,4}];
 dd=Table[Expand[Sum[ell[[i]]^2*tt[[i,i,k]],{i,4}]],{k,4}];
 aa=Expand[Sum[ell[[i]]^2*tt[[i,j,k]]^2,{i,4},{j,4},{k,4}]];
 bb=Expand[Sum[ell[[i]]*ell[[j]]*tt[[i,j,k]]^2,{i,4},{j,4},{k,4}]];
 cs=Expand[Sum[ell[[i]]*tt[[i,j,k]]^2,{i,4},{j,4},{k,4}]];
 require[zeroQ[Total[ell]],"spectral trace"];
 require[zeroQ[ls-4(1+r^2+r^2*y^2)],"positive spectral normalisation"];
 require[zeroQ[Total[cc]],"ordinary cubic basis trace"];
 require[zeroQ[ell.cc],"weighted cubic basis trace"];
 require[zeroQ[Det[cc[[{2,3}]]]-(1+r)^2],"cubic basis independent on square"];
 require[zeroQ[Table[Sum[tt[[i,i,k]],{i,4}],{k,4}]],"ordinary cubic trace"];
 require[zeroQ[Table[Sum[ell[[i]]*tt[[i,i,k]],{i,4}],{k,4}]],"weighted cubic trace"];
 <|"r"->r,"y"->y,"x"->x,"ell"->ell,"L"->ls,"M3"->mm3,"M4"->mm4,
   "T"->tt,"N"->nn,"R"->rr,"d"->dd,"a"->aa,"b"->bb,"c"->cs|>
];

(* Knum = L K_A, acting on an unnormalised trace-free matrix. *)
kNumerator[ell_,ls_,f_] := Module[{aa=DiagonalMatrix[ell],tr1,tr2},
 tr1=ell.Diagonal[f];tr2=(ell^2).Diagonal[f];
 Expand[ls*f/6+(aa.aa.f+f.aa.aa)/4-aa.f.aa/6+
   7*tr1*aa/36-tr2*IdentityMatrix[4]/12]
];

(* First reconstruction, directly from the expanded endpoint in the paper.
   F=L^2 N B, wnum_i=ell_i sum_j ell_j^2 T_jji.
   All divisions below are fixed rational numbers. *)
closedPolynomial[ch_] := Module[
 {ell=ch["ell"],ls=ch["L"],nn=ch["N"],mm3=ch["M3"],mm4=ch["M4"],
  rr=ch["R"],tt=ch["T"],dd=ch["d"],aa=ch["a"],bb=ch["b"],cs=ch["c"],ff,kf,pp,ww,whom},
 pp=Expand[mm4*ls-mm3^2-ls^3/4];ww=ell*dd;
 ff=Table[Expand[KroneckerDelta[i,j]*nn*(5*ell[[i]]^2*ls/8-mm3*ell[[i]]/2-ls^2/32)
    -ls^2*rr[[i,j]]/2+7*Sum[(4*ell[[k]]-ell[[i]]-ell[[j]])*
       tt[[i,j,k]]*ell[[k]]*dd[[k]],{k,4}]/8],{i,4},{j,4}];
 require[zeroQ[Tr[ff]],"endpoint B is trace-free"];
 kf=kNumerator[ell,ls,ff];
 whom=21*ls^5*nn^2/32+13*pp*ls^2*nn^2/16-39*mm3^2*ls^2*nn^2/16
   -8*aa*ls^4*nn-189*bb*ls^4*nn/16+16*mm3*cs*ls^3*nn+24*(dd.dd)*ls^3*nn
   -8*ls*Total[Flatten[ff]^2]+16*Flatten[ff].Flatten[kf]
   -35*ls^2*nn*(ww.ww)/4+441*ls^2*(ww.rr.ww)/16;
 Expand[5625*(-whom-ls^5*nn^2/10000)/32]
];

(* Second reconstruction uses the 35 unordered symmetric fourth-tensor
   coordinates WITH their ordered multiplicities. C4 is the dual Gram
   tensor of the ordinary-trace-free orthogonal projection. The closed
   formulas for K_A, Z and H are not used to construct these matrices. *)
rawGram[ch_] := Module[
 {i2=combinations[4,2],i4=combinations[4,4],w2,w4,idx4,t0,cf,dm,metric,
  ell=ch["ell"],tt=ch["T"],ta,ca,nt,kraw,zraw,hraw,ix,p0},
 w2=(Length[Permutations[#]]&)/@i2;w4=(Length[Permutations[#]]&)/@i4;
 idx4[a_]:=First[FirstPosition[i4,Sort[a]]];
 t0=ConstantArray[0,{10,35}];
 Do[t0[[row,idx4[Join[{i,i},i2[[row]]]]]]+=1,{row,10},{i,4}];
 cf=DiagonalMatrix[1/w4];
 cf=cf-cf.Transpose[t0].Inverse[t0.cf.Transpose[t0]].t0.cf;
 dm=ConstantArray[0,{10,9}];
 Do[dm[[First[FirstPosition[i2,{i,i}]],i]]=1;dm[[10,i]]=-1,{i,3}];
 ix=Select[Range[10],Unequal@@i2[[#]]&];
 Do[dm[[ix[[i]],3+i]]=1,{i,6}];
 metric=Transpose[dm].DiagonalMatrix[w2].dm;
 ta=ConstantArray[0,{10,35}];
 Do[ta[[row,idx4[Join[{i,i},i2[[row]]]]]]+=ell[[i]],{row,10},{i,4}];
 ca=Expand[Transpose[dm].DiagonalMatrix[w2].ta];
 nt=ConstantArray[0,{4,35}];
 Do[nt[[l,idx4[{i,j,k,l}]]]+=tt[[i,j,k]],{i,4},{j,4},{k,4},{l,4}];nt=Expand[nt];
 kraw=Expand[ca.cf.Transpose[ca]];
 zraw=Expand[nt.cf.Transpose[ca]];hraw=Expand[nt.cf.Transpose[nt]];
 require[cf===Transpose[cf],"raw projection dual symmetry"];
 require[zeroQ[t0.cf],"raw projection kills ordinary trace"];
 require[cf.DiagonalMatrix[w4].cf===cf,"raw projection idempotence"];
 <|"I2"->i2,"C"->cf,"D"->dm,"W2"->DiagonalMatrix[w2],"W4"->DiagonalMatrix[w4],
   "T0"->t0,"Ta"->ca,"Nt"->nt,"K"->kraw,"Z"->zraw,"H"->hraw,"Metric"->metric|>
];

checkGramFormulas[ch_,gr_] := Module[{ell=ch["ell"],ls=ch["L"],tt=ch["T"],basis,km,zm,i2=gr["I2"]},
 basis=Table[Module[{a=ConstantArray[0,{4,4}]},
   Do[a[[i2[[k,1]],i2[[k,2]]]]=gr["D"][[k,j]];
      a[[i2[[k,2]],i2[[k,1]]]]=gr["D"][[k,j]],{k,10}];a],{j,9}];
 km=Table[Expand[Flatten[basis[[i]]].Flatten[kNumerator[ell,ls,basis[[j]]]]],{i,9},{j,9}];
 zm=Table[Expand[Sum[(4*ell[[k]]-ell[[i]]-ell[[j]])*tt[[i,j,k]]*basis[[b,i,j]],
    {i,4},{j,4}]/8],{k,4},{b,9}];
 require[zeroQ[gr["K"]-km],"35-coordinate K formula"];
 require[zeroQ[gr["Z"]-zm],"35-coordinate mixed Z formula"];
 require[zeroQ[gr["H"]-ch["N"]*IdentityMatrix[4]/4-9*ch["R"]/16],"35-coordinate H formula"];
 True
];

rawPolynomial[ch_,gr_] := Module[
 {ls=ch["L"],nn=ch["N"],ell=ch["ell"],tt=ch["T"],rr=ch["R"],dd=ch["d"],
  mm3=ch["M3"],mm4=ch["M4"],aa=ch["a"],bb=ch["b"],cs=ch["c"],t=1/2,
  pp,vn,bn,en,ecov,fcov,mi,un,mnorm,mk,tail,fbase,l4,l3,jj,base},
 pp=Expand[mm4*ls-mm3^2-ls^3/4];vn=-7*ell*dd;
 (* Reconstruct the cubic contraction of the Ricci correction. *)
 bn=Table[Expand[-3*Sum[If[i===l,0,(ell[[i]]-ell[[l]])*ell[[i]]*ell[[l]]*tt[[i,i,l]]],
       {i,4}]/2],{l,4}];
 require[zeroQ[bn+3*ell*dd/2],"Ricci contraction b0"];
 en=Table[Expand[KroneckerDelta[i,j]*nn*(5*ell[[i]]^2*ls/8-mm3*ell[[i]]/2-ls^2/32)
      -ls^2*rr[[i,j]]/2],{i,4},{j,4}];
 ecov=Transpose[gr["D"]].gr["W2"].(Extract[en,#]&/@gr["I2"]);
 fcov=Expand[ecov-Transpose[gr["Z"]].vn];mi=Inverse[gr["Metric"]];
 mnorm=fcov.mi.fcov;mk=fcov.mi.gr["K"].mi.fcov;
 un=Expand[Transpose[gr["Nt"]].vn];
 tail=2*ls^2*nn*(bn.vn)-ls^2*(un.gr["C"].un);
 (* Assemble the three zero-average terms separately, rather than using
    the expanded endpoint coefficients in closedPolynomial. *)
 fbase=3*t*(aa-2*bb)*ls^2+nn*(t*(35*t-28)*ls^3/16-3*pp/2);
 l4=t*((2*aa+bb)*ls^2-mm4*ls*nn);
 l3=t*(-mm3^2*nn+2*mm3*cs*ls+3*(dd.dd)*ls);
 jj=t*(aa-2*bb)*ls^2-nn*pp-t*ls^3*nn/4;
 base=fbase-89*l4/8+16*l3+13*jj/4;
 Expand[5625*(-ls^2*nn*base+8*ls*mnorm-16*mk+tail-ls^5*nn^2/10000)/32]
];

(* Data reader: the stored polynomial is an exact object to be compared,
   not a substitute for either reconstruction. All index conventions in
   JSON are zero based and are converted explicitly below. *)
loadData[root_,book_] := Module[{data,cert,integrity,leaves,power,terms,seen,i,j,k,c,path},
 data=readJSON[FileNameJoin[{root,"data","endpoint.json"}]];
 cert=readJSON[FileNameJoin[{root,"data","certificate.json"}]];
 require[fileHash[FileNameJoin[{root,"data","endpoint.json"}]]===$EndpointHash,"endpoint SHA256"];
 require[fileHash[FileNameJoin[{root,"data","certificate.json"}]]===$CertificateHash,"certificate SHA256"];
 require[cert["input_sha256"]===$EndpointHash,"manifest refers to endpoint"];
 require[data["endpoint"]==="1/2" && data["epsilon"]==="1/10000", "endpoint and epsilon"];
 require[data["degrees"]==={14,14} && cert["degrees"]==={14,14},"bidegrees"];
 require[data["quartic_monomials"]+1===book["Quartics"],"stored quartic order"];
 require[data["positive_scale"]==="5625/32", "normalisation scale"];
 require[Length[data["polynomials"]]===196,"number of coefficient polynomials"];
 power=ConstantArray[0,{15,15,197}];
 Do[terms=If[k<=196,data["polynomials"][[k]],data["denominator_L5"]];
   require[ListQ[terms],"coefficient table",k];seen={};
   Do[require[ListQ[row] && Length[row]===3,"coefficient row",{k,row}];
     {i,j,c}={readInteger[row[[1]]],readInteger[row[[2]]],readInteger[row[[3]]]};
     require[0<=i<=14 && 0<=j<=14 && c!=0,"nonzero in-range coefficient",{k,row}];
     require[!MemberQ[seen,{i,j}],"duplicate coefficient",{k,i,j}];
     AppendTo[seen,{i,j}];power[[i+1,j+1,k]]=c,{row,terms}],{k,197}];
 require[AllTrue[Flatten[power],IntegerQ],"integer coefficient array"];
 require[Count[Flatten[power[[All,All,1;;196]]],Except[0]]===19020,"coefficient count"];
 leaves=cert["leaves"];require[Length[leaves]===24,"24 leaves"];
 require[cert["integer_PD_checks"]===43200 && cert["total_controls"]===5400,"full certificate counts"];
 require[readInteger[cert["null_denominator"]]>0,"positive null denominator"];
 integrity=readJSON[FileNameJoin[{root,"data_integrity.json"}]];
 Do[path=FileNameJoin[Prepend[StringSplit[item["path"],"/"],root]];
   require[FileExistsQ[path],"data file",path];
   require[fileHash[path]===item["sha256"],"data-file SHA256",item["path"]],{item,integrity["files"]}];
 <|"Data"->data,"Certificate"->cert,"Power"->power|>
];

comparePolynomial[pol_,ch_,book_,power_,label_] := Module[{cr,expected,got,den,q},
 require[FreeQ[pol,_Real],label<>" has no approximate numbers"];
 cr=CoefficientRules[pol,ch["x"]];
 expected=Sort[Table[Count[q,i],{q,book["Quartics"]},{i,12}]];
 require[Sort[First/@cr]===expected,label<>" has precisely the 196 monomials"];
 Do[q=book["Quartics"][[k]];
   (* Coefficient with a compound monomial is deliberately NOT used:
      exponent-vector extraction is unambiguous for multivariate polynomials. *)
   got=Last[First[Select[cr,First[#]===Table[Count[q,i],{i,12}]&]]];
   den=Sum[power[[i+1,j+1,k]]*ch["r"]^i*ch["y"]^j,{i,0,14},{j,0,14}];
   require[zeroQ[got-den],label<>" coefficient identity",<|"Monomial"->q,"Index"->k|>],
   {k,196}];
 den=Sum[power[[i+1,j+1,197]]*ch["r"]^i*ch["y"]^j,{i,0,14},{j,0,14}];
 require[zeroQ[den-5625*ch["L"]^5/32],label<>" denominator identity"];
 True
];

(* Exact integer transformations. Every control array is scaled by one
   COMMON POSITIVE integer; P and D are transformed with the same scale.
   Global power-to-Bernstein scale: n!. Each midpoint restriction: 2^n.
   Affine scale: n! q^n, where q clears both rational interval endpoints. *)
integerTransforms[n_] := {
 Table[If[j<=i,Binomial[i,j]*j!*(n-j)!,0],{i,0,n},{j,0,n}],
 Table[If[j<=i,2^(n-i)*Binomial[i,j],0],{i,0,n},{j,0,n}],
 Table[If[j>=i,2^i*Binomial[n-i,j-i],0],{i,0,n},{j,0,n}]
};
affineTransform[n_,lo_,hi_] := Module[{qq,aa,hh},
 require[exactRationalQ[lo] && exactRationalQ[hi] && hi>lo,"rational interval"];
 qq=LCM[Denominator[lo],Denominator[hi]];aa=qq*lo;hh=qq*(hi-lo);
 Table[qq^(n-k)*Sum[Binomial[k,s]*If[k===s,1,aa^(k-s)]*hh^s*Binomial[i,s]*s!*(n-s)!,
       {s,0,Min[i,k]}],{i,0,n},{k,0,n}]
];
act[array_,mat_,axis_] := Module[{a,sh,result},
 require[MemberQ[{1,2},axis],"transform axis"];
 a=If[axis===1,array,Transpose[array,{2,1,3}]];sh=Dimensions[a];
 result=ArrayReshape[mat.ArrayReshape[a,{sh[[1]],Times@@Rest[sh]}],sh];
 If[axis===1,result,Transpose[result,{2,1,3}]]
];
rectangle[path_String] := Module[{a=0,b=1,c=0,d=1,mid,chars=Characters[path]},
 Do[require[MemberQ[{"0","1"},chars[[k]]],"binary path",path];
   If[OddQ[k],mid=(a+b)/2;If[chars[[k]]==="0",b=mid,a=mid],
      mid=(c+d)/2;If[chars[[k]]==="0",d=mid,c=mid]],{k,Length[chars]}];
 {a,b,c,d}
];
checkCover[leaves_] := Module[{paths,prefixes},
 paths=Lookup[leaves,"path"];
 require[AllTrue[paths,StringQ] && DuplicateFreeQ[paths],"unique binary leaves"];
 require[AllTrue[paths,StringMatchQ[#,RegularExpression["[01]*"]]&],"binary leaf syntax"];
 prefixes=DeleteDuplicates[Flatten[Table[StringTake[p,k],{p,paths},{k,0,StringLength[p]}]]];
 Do[If[MemberQ[paths,p],
    require[!MemberQ[prefixes,p<>"0"] && !MemberQ[prefixes,p<>"1"],"leaf has no descendants",p],
    require[MemberQ[prefixes,p<>"0"] && MemberQ[prefixes,p<>"1"],"both children present",p]],
   {p,prefixes}];
 require[Max[StringLength/@paths]===8,"maximum tree depth"];
 require[Total[(With[{q=rectangle[#]},(q[[2]]-q[[1]])*(q[[4]]-q[[3]])]&)/@paths]===1,
    "exact area coverage"];
 True
];

(* Verify one leaf. A Gram entry is reconstructed, not trusted:
     up = C_P*(nd*14*14/count) + C_D*interpolated_null_numerator.
   The four null vectors must each represent the ZERO quartic. Thus
   aggregating entries must recover nd*14*14 times the actual control
   polynomial. Witness matrices are arbitrary integer matrices; checking
   U.G.Transpose[U] strictly diagonally dominant with positive diagonal
   implies G positive definite and in particular U nonsingular. *)
verifyLeaf[control_,leaf_,root_,book_,nd_] := Module[
 {nulls,den,labels=book["Labels"],weights=book["Weights"],counts=book["Counts"],
  pos=book["Positions"],blocks=book["Blocks"],byblock=book["ByBlock"],groupidx,
  wp,wit,pools,assign,i,j,nu,up,aggregated,g,uu,cong,margins,matrices=0,gramCount=0,
  b,siz,q,h,idx,fn,rows=0,minMargin=Infinity},
 require[Dimensions[control]==={15,15,197} && AllTrue[Flatten[control],IntegerQ],"integer control array",leaf["path"]];
 require[Min[Flatten[control[[All,All,197]]]]>0,"positive Bernstein denominator",leaf["path"]];
 nulls=Map[readInteger,leaf["null_corners"],{2}];
 require[Dimensions[nulls]==={4,442},"four null corner vectors",leaf["path"]];
 groupidx=Table[Flatten[Position[labels,k]],{k,196}];
 Do[aggregated=Table[Total[(weights*row)[[groupidx[[k]]]]],{k,196}];
   require[aggregated===ConstantArray[0,196],"null vector is zero polynomial",leaf["path"]],{row,nulls}];
 den=nd*14*14;require[And@@Thread[Mod[den,counts]==0],"exact Gram denominator"];
 fn=leaf["witness_file"];
 require[StringMatchQ[fn,RegularExpression["leaf_[0-9]{4}\\.npz"]],"witness filename",fn];
 wp=FileNameJoin[{root,"data","witnesses",StringReplace[fn,".npz"->".json"]}];wit=readJSON[wp];
 pools=Table[wit["pool"<>ToString[b-1]],{b,8}];
 assign=Table[wit["index"<>ToString[b-1]],{b,8}];
 Do[siz=Length[blocks[[b]]];
   require[Length[Dimensions[pools[[b]]]]===3 && Rest[Dimensions[pools[[b]]]]==={siz,siz},"witness pool dimensions",{fn,b}];
   require[AllTrue[Flatten[pools[[b]]],IntegerQ],"integer congruences",{fn,b}];
   require[Dimensions[assign[[b]]]==={225} && AllTrue[assign[[b]],IntegerQ],"assignment dimensions",{fn,b}];
   require[Min[assign[[b]]]>=0 && Max[assign[[b]]]<Length[pools[[b]]],"assignment range",{fn,b}],{b,8}];
 Do[
   nu=(14-i)*(14-j)*nulls[[1]]+i*(14-j)*nulls[[2]]+(14-i)*j*nulls[[3]]+i*j*nulls[[4]];
   up=control[[i+1,j+1,labels]]*(den/counts[[labels]])+control[[i+1,j+1,197]]*nu;
   require[VectorQ[up,IntegerQ],"integer Gram entries",{leaf["path"],i,j}];
   aggregated=Table[Total[(weights*up)[[groupidx[[k]]]]],{k,196}];
   require[aggregated===den*control[[i+1,j+1,1;;196]],"full Gram polynomial identity",{leaf["path"],i,j}];gramCount++;
   h=15*i+j+1;
   Do[siz=Length[blocks[[b]]];g=ConstantArray[0,{siz,siz}];
     Do[{q,idx}=pos[[k,{2,3}]];g[[q,idx]]=up[[k]];g[[idx,q]]=up[[k]],{k,byblock[[b]]}];
     uu=pools[[b,assign[[b,h]]+1]];cong=uu.g.Transpose[uu];
     require[cong===Transpose[cong] && MatrixQ[cong,IntegerQ],"exact symmetric congruence",{leaf["path"],i,j,b}];
     margins=Table[cong[[k,k]]-Total[Abs[cong[[k]]]]+Abs[cong[[k,k]]],{k,siz}];
     require[Min[margins]>0,"strict integer diagonal dominance",<|"Path"->leaf["path"],"Control"->{i,j},"Block"->b,"Margins"->margins|>];
     rows+=Length[margins];minMargin=Min[minMargin,Min[margins]];
     matrices++,{b,8}],{i,0,14},{j,0,14}];
 require[matrices===1800 && gramCount===225,"complete leaf count",leaf["path"]];
 <|"Path"->leaf["path"],"GramIdentities"->gramCount,"IntegerMatrixChecks"->matrices,
   "StrictRowInequalities"->rows,"MinimumIntegerMargin"->minMargin|>
];

replay[method_,power_,cert_,root_,book_] := Module[
 {leaves=cert["leaves"],nd=readInteger[cert["null_denominator"]],report={},start=AbsoluteTime[],
  tr,rootControl,visit,leafMap,control,rect,ans,axis,path,check},
 check[cc_,leaf_] := (ans=verifyLeaf[cc,leaf,root,book,nd];AppendTo[report,ans];
   note[method,"  ",Length[report],"/24  ",leaf["path"],"  PASS"]);
 If[method==="Affine",
   Do[rect=rectangle[leaf["path"]];
    control=act[act[power,affineTransform[14,rect[[1]],rect[[2]]],1],
       affineTransform[14,rect[[3]],rect[[4]]],2];check[control,leaf],{leaf,leaves}],
   require[method==="Midpoint","certificate method",method];
   tr=integerTransforms[14];rootControl=act[act[power,tr[[1]],1],tr[[1]],2];
   leafMap=Association[Rule[#["path"],#]&/@leaves];
   visit[path_String,cc_] := If[KeyExistsQ[leafMap,path],check[cc,leafMap[path]],
     axis=1+Mod[StringLength[path],2];
     visit[path<>"0",act[cc,tr[[2]],axis]];
     axis=1+Mod[StringLength[path],2];
     visit[path<>"1",act[cc,tr[[3]],axis]]];
   visit["",rootControl]
 ];
 require[Length[report]===24 && Total[Lookup[report,"IntegerMatrixChecks"]]===43200 &&
   Total[Lookup[report,"GramIdentities"]]===5400,"full replay totals",method];
 <|"Method"->method,"Status"->"PASS","Rectangles"->Length[report],
   "ControlQuartics"->Total[Lookup[report,"GramIdentities"]],
   "IntegerMatrixChecks"->Total[Lookup[report,"IntegerMatrixChecks"]],
   "StrictRowInequalities"->Total[Lookup[report,"StrictRowInequalities"]],
   "MinimumIntegerMargin"->ToString[Min[Lookup[report,"MinimumIntegerMargin"]],InputForm],
   "ElapsedSeconds"->AbsoluteTime[]-start|>
];

(* Small tests check both exact conversion algorithms against direct
   substitution and tagged failure propagation. The separate synthetic
   certificate test below checks null corrections and a singular witness. *)
selfTests[] := Module[{r,y,s,t,p,a,controls,tr,path,rect,left,right,n=3,c=0,failure},
 Do[r=Unique["r"];y=Unique["y"];s=Unique["s"];t=Unique["t"];
   p=1+2*r+3*y+5*r*y+7*r^2*y^3+11*r^3*y^2;
   a=Table[{Coefficient[Coefficient[p,r,i],y,j]},{i,0,n},{j,0,n}];
   rect=rectangle[path];
   controls=act[act[a,affineTransform[n,rect[[1]],rect[[2]]],1],affineTransform[n,rect[[3]],rect[[4]]],2];
   left=Sum[controls[[i+1,j+1,1]]*Binomial[n,i]*s^i*(1-s)^(n-i)*Binomial[n,j]*t^j*(1-t)^(n-j),{i,0,n},{j,0,n}];
   right=(n!^2*LCM[Denominator[rect[[1]]],Denominator[rect[[2]]]]^n*LCM[Denominator[rect[[3]]],Denominator[rect[[4]]]]^n)*
       (p/.{r->rect[[1]]+(rect[[2]]-rect[[1]])*s,y->rect[[3]]+(rect[[4]]-rect[[3]])*t});
   require[zeroQ[left-right],"affine transform self-test",path];c++;
   tr=integerTransforms[n];controls=act[act[a,tr[[1]],1],tr[[1]],2];
   Do[controls=act[controls,tr[[If[StringTake[path,{k}]==="0",2,3]]],1+Mod[k-1,2]],{k,StringLength[path]}];
   left=Sum[controls[[i+1,j+1,1]]*Binomial[n,i]*s^i*(1-s)^(n-i)*Binomial[n,j]*t^j*(1-t)^(n-j),{i,0,n},{j,0,n}];
   right=n!^2*2^(n*StringLength[path])*(p/.{r->rect[[1]]+(rect[[2]]-rect[[1]])*s,y->rect[[3]]+(rect[[4]]-rect[[3]])*t});
   require[zeroQ[left-right],"midpoint transform self-test",path];c++,
   {path,{"","0","1","001","101011","00000000"}}];
 require[readInteger["-123456789012345678901234567890"]===-123456789012345678901234567890,"big integer parser"];c++;
 failure=Catch[require[False,"intentional failure test"],$Tag];
 require[FailureQ[failure],"fail-closed control flow"];c++;
 <|"Status"->"PASS","Checks"->c|>
];

(* A complete 225-control, 8-block synthetic replay exercises JSON I/O,
   integer Gram reconstruction, a nonzero null correction, and rejection
   of a deliberately singular witness. No synthetic data enter the proof. *)
certificateSelfTest[book_] := Module[{tmp,wdir,fn,wit,leaf,coeff,control,null,entries,
    ii,jj,ww,good,bad,result},
 tmp=CreateDirectory[];wdir=FileNameJoin[{tmp,"data","witnesses"}];
 CreateDirectory[wdir,CreateIntermediateDirectories->True];
 fn=FileNameJoin[{wdir,"leaf_9999.json"}];
 wit=Association[Flatten[Table[{
    ("pool"<>ToString[b-1])->{IdentityMatrix[Length[book["Blocks"][[b]]]]},
    ("index"<>ToString[b-1])->ConstantArray[0,225]},{b,8}],1]];
 Export[fn,wit,"RawJSON"];
 coeff=Map[Which[Length[DeleteDuplicates[#]]===1,48,
    Sort[Last/@Tally[#]]==={2,2},3,True,0]&,book["Quartics"]];
 control=Table[Join[coeff,{1}],{15},{15}];
 null=ConstantArray[0,442];
 entries=Flatten[Position[book["Labels"],First[FirstPosition[book["Quartics"],{1,1,2,2}]]]];
 ii=First[Select[entries,book["Weights"][[#]]===1&]];
 jj=First[Select[entries,book["Weights"][[#]]===2&]];
 null[[ii]]=-2;null[[jj]]=1;
 leaf=<|"path"->"000","null_corners"->ConstantArray[null,4],"witness_file"->"leaf_9999.npz"|>;
 good=verifyLeaf[control,leaf,tmp,book,12];
 require[good["IntegerMatrixChecks"]===1800,"synthetic full leaf"];
 bad=wit;ww=bad["pool0"];ww[[1,1]]=ConstantArray[0,16];AssociateTo[bad,"pool0"->ww];
 Export[fn,bad,"RawJSON"];
 result=Catch[verifyLeaf[control,leaf,tmp,book,12],$Tag];
 require[FailureQ[result],"singular-witness rejection"];
 DeleteDirectory[tmp,DeleteContents->True];
 <|"Status"->"PASS","SyntheticIntegerMatrixChecks"->1800,"NegativeControlRejected"->True|>
];

Options[VerifyChern4]={"Methods"->{"Midpoint","Affine"},"Verbose"->True,"WriteReport"->True};
VerifyChern4[root_:Automatic,OptionsPattern[]] := Block[{$Verbose=OptionValue["Verbose"],$HistoryLength=0},
 Module[{dir,methods=OptionValue["Methods"],start=AbsoluteTime[],book,loaded,ch,gr,pc,pr,result,replays={},reportFile,runID=CreateUUID[],runDir,started},
 dir=If[root===Automatic,$PackageDirectory,ExpandFileName[root]];
 started=DateString[Now,{"ISODate","T","Time","Z"},TimeZone->0];
 reportFile=FileNameJoin[{dir,"verification_result.wl"}];
 runDir=FileNameJoin[{dir,"runs",runID}];
 result=CheckAbort[Catch[
   require[DirectoryQ[dir],"package directory",dir];
   If[TrueQ[OptionValue["WriteReport"]],
     CreateDirectory[runDir,CreateIntermediateDirectories->True];
     writeResult[<|"Status"->"RUNNING","EndpointCertified"->False,"RunID"->runID,"StartedUTC"->started|>,reportFile]];
   require[ListQ[methods] && Length[methods]>=1 && DuplicateFreeQ[methods] &&
      AllTrue[methods,MemberQ[{"Midpoint","Affine"},#]&],"requested complete replay methods",methods];
   note["Checking exact transformations and data ..."];
   selfTests[];book=bookkeeping[];checkSpectralGroup[];certificateSelfTest[book];loaded=loadData[dir,book];
   checkCover[loaded["Certificate"]["leaves"]];
   note["Reconstructing all endpoint coefficients from the closed tensor formulas ..."];
   ch=makeChart[];pc=closedPolynomial[ch];
   comparePolynomial[pc,ch,book,loaded["Power"],"closed reconstruction"];
   note["PASS: 196 quartics / 19020 bivariate coefficient terms."];
   note["Reconstructing from the 35-coordinate fourth-tensor projection ..."];
   gr=rawGram[ch];checkGramFormulas[ch,gr];pr=rawPolynomial[ch,gr];
   comparePolynomial[pr,ch,book,loaded["Power"],"raw reconstruction"];
   require[zeroQ[pc-pr],"the two complete reconstructions agree"];
   note["PASS: raw reconstruction and Gram identities."];
   Clear[pc,pr,ch,gr];
   Do[AppendTo[replays,replay[method,loaded["Power"],loaded["Certificate"],dir,book]],{method,methods}];
   <|"Status"->"PASS","EndpointCertified"->True,"Endpoint"->"t=1/2",
     "Bound"->"W <= -1/10000","PolynomialReconstructions"->2,
     "RawFourthTensorGramIdentities"->"PASS","QuarticMonomials"->196,
     "BivariateCoefficientTerms"->19020,"SpectralCover"->"PASS",
     "CertificateReplays"->replays,"TotalIntegerMatrixChecks"->43200*Length[methods],
     "EndpointSHA256"->$EndpointHash,"CertificateSHA256"->$CertificateHash,
     "RunID"->runID,"StartedUTC"->started,
     "FinishedUTC"->DateString[Now,{"ISODate","T","Time","Z"},TimeZone->0],
     "VerifierSHA256"->fileHash[FileNameJoin[{dir,"Chern4Verifier.wl"}]],
     "DataIntegritySHA256"->fileHash[FileNameJoin[{dir,"data_integrity.json"}]],
     "WolframVersion"->$Version,"ElapsedSeconds"->AbsoluteTime[]-start|>, $Tag],
   Failure["Aborted",<|"Message"->"Verification was interrupted; no endpoint certification was issued."|>]];
 If[TrueQ[OptionValue["WriteReport"]] && DirectoryQ[dir],
   If[DirectoryQ[runDir],writeResult[result,FileNameJoin[{runDir,"verification_result.wl"}]]];
   writeResult[result,reportFile]];
 If[AssociationQ[result] && TrueQ[Lookup[result,"EndpointCertified",False]],
   note["ALL CHECKS PASSED. Exact endpoint certified: W <= -1/10000."],
   Print["VERIFICATION FAILED OR ABORTED. No certification issued."]];
 result
 ]
];
VerifyChern4SelfTests[] := Catch[Module[{b=bookkeeping[]},
 <|"TransformsAndFailure"->selfTests[],"SpectralGroup"->checkSpectralGroup[],
   "SyntheticCertificate"->certificateSelfTest[b]|>],$Tag];
End[];
EndPackage[];
