(* ::Package:: *)

(* Mathematica Package *)

BeginPackage["quasinormalTables`"]

qnm::usage =
 "qnm[n,l,m,Aa_,Mf_]";

Begin["`Private`"]



(* ::Input:: *)
(**)

fileLocation="/home/vishal/Waveforms/s2_QNM_small.h5"
Do[Do[qnm[n,l,m,Aa_,Mf_]=Module[{dataset=Evaluate["/n"<>ToString[n]<>"l"<>ToString[l]<>"m"<>ToString[m]]},{wr22,wi22}=Hold@{Interpolation[QNM22[[All,{1,2}]]],Interpolation[QNM22[[All,{1,3}]]]}/.
QNM22:> Import[fileLocation,{"Datasets",dataset}][[All,1;;3]]//ReleaseHold;
{wr22[Aa],wi22[Aa]}/Mf];,{n,1,2},{m,0,l}],{l,2,3}]

Do[Do[qnm[n,l,-m,Aa_,Mf_]=Module[{dataset=Evaluate["/n"<>ToString[n]<>"l"<>ToString[l]<>"mm"<>ToString[m]]},{wr22,wi22}=Hold@{Interpolation[QNM22[[All,{1,2}]]],Interpolation[QNM22[[All,{1,3}]]]}/.
QNM22:> Import[fileLocation,{"Datasets",dataset}][[All,1;;3]]//ReleaseHold;
{wr22[Aa],wi22[Aa]}/Mf];,{n,1,2},{m,1,l}],{l,2,3}]

End[ ]

EndPackage[ ]


