(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["QuasiNormalModes`"];

QuasiNormalMode::usage = "QuasiNormalMode[s, l, m, n, a] calculates the quasinormal mode frequencies for a black hole, using Leaver's continued fraction method. The convention used is M = 1.";

QuasiNormalMode::SchwarzUntrusted = "Currently, for a Schwarzschild black hole, the results for this combination of l = `1` and n = `2` are not valid."

QuasiNormalMode::KerrUntrusted = "Currently, for a Kerr black hole, the results for this value of l = `1` are not valid. Only the results for the first 2-3 modes are trusted."

QuasiNormalMode::UntrustedSpin = "Currently, the results for this value of a = `1` are not valid. Currently, the algorithm is not trusted near the extremal limit."

Begin["`Private`"];           (* Beginning private context which will contain all functions which the user doesn't need to access (and which may conflict with their own code*)

M = 1; (* Mass. This is the standard convention *)


(* These are definition of some useful functions *)

\[Beta][s_] := s^2 -1;
k1[m_, s_] := 1/2 Abs[m-s];
k2[m_, s_] := 1/2 Abs[m+s];

(* Functions for the Continued Fraction used in Leaver's method for Schwarzschild *)
\[Alpha][i_, \[Omega]_]  := i^2 - 4 M I \[Omega] i + 2 i - 4 M I \[Omega] + 1;
\[Delta][i_, \[Omega]_,s_, l_] := -2 i^2 - (2 - 16 M I \[Omega])i + 32 M^2 \[Omega]^2 + 8 M I \[Omega] - l(l + 1) + \[Beta][s];
\[Gamma][i_, \[Omega]_, s_] := i^2 - 8 M I \[Omega] i - 16 M^2 \[Omega]^2 - \[Beta][s] - 1;

b[a_] := b[a] = Sqrt[4 M^2 - 4 a^2];

(* Functions for the Continued Fraction used in Leaver's method for Kerr *)
\[Alpha]freq[i_,\[Omega]_, s_, m_, a_]:= i^2 + (2-s-2 M I \[Omega] -2 I/b[a] (2 M^2 \[Omega] - a m))i + 1 - s - 2 M I \[Omega] -2 I/b[a] (2 M^2 \[Omega] - a m);
\[Beta]freq[i_,\[Omega]_, Alm_, s_, m_, a_]:= -2 i^2 +(-2 + 2(4 M + b[a]) I \[Omega] + 4 I/b[a] (2 M^2 \[Omega] - a m)) i + (16 M^2 + 4 M b[a] - a^2) \[Omega]^2 - s - 1 - 2 a m \[Omega] - Alm +(4 M + b[a]) I \[Omega] + (8 M \[Omega] + 2 I)/b[a] (2 M^2 \[Omega] - a m);
\[Gamma]freq[i_, \[Omega]_, s_, m_, a_]:= i^2 + (s - 6 M I \[Omega] - 2 I/b[a] (2 M^2 \[Omega] - a m)) i - 8 M^2 \[Omega]^2 - 4 M I \[Omega] s - 8 M \[Omega]/b[a] (2 M^2 \[Omega] - a m);

\[Alpha]ang[i_, \[Omega]_, s_, m_, a_]:= -2 (i + 1) (i + 2 k1[m, s] + 1);
\[Beta]ang[i_, \[Omega]_, Alm_, s_, m_, a_]:= i (i - 1) + 2 i (k1[m, s] + k2[m, s] + 1 - 2 a \[Omega]) - (2 a \[Omega] (2 k1[m, s] + s + 1) - (k1[m, s] + k2[m, s]) (k1[m, s] + k2[m, s] + 1)) - (a^2 \[Omega]^2 + s(s+1) + Alm);
\[Gamma]ang[i_, \[Omega]_, s_, m_, a_]:= 2 a \[Omega] (i + k1[m, s] + k2[m, s] + s);


(* Initial guesses used as seeds in FindRoot *)
(* Multiple asymptotic expansions are used for Schwarzschild, with different expansions providing better seeds for 
different values of l and n *)

(* l > n *)
Schwarzfinit1[s_, l_, n_]:= ((I*(n+1/2)*(\[Beta][s]^2/27 + (\[Beta][s]*(1100*(n+1/2)^2 - 2719))/46656 + (11273136*(n+1/2)^4 - 52753800*(n+1/2)^2 + 66480535)/2902376448))/(l+1/2)^4 + 
   (-(\[Beta][s]^2/27) + (\[Beta][s]*(204*(n+1/2)^2 + 211))/3888 + (854160*(n+1/2)^4 - 1664760*(n+1/2)^2 - 776939)/40310784)/(l+1/2)^3 - (I*(n+1/2)*(\[Beta][s]/9 + (235*(n+1/2)^2)/3888 - 1415/15552))/(l+1/2)^2 + 
   (\[Beta][s]/3 - (5*(n+1/2)^2)/36 - 115/432)/(l+1/2) + (l+1/2) - I*(n+1/2))/(Sqrt[27]*M);

(* n \[GreaterEqual] 6, l\[LessEqual]2*)    
Schwarzfinit2[n_] := Log[3]/(8 \[Pi] M) - I (n+1/2)/(4 M);

(* Spectral method using hyperboloidal slicing *)
(* n >= 6, 2<l<=n*)
SpectralInitialGuess[s_, l_, n_]:= Module[{L1a, L1b, L2a, L2b, L2c, Prec, Ndiv, ndiv, \[Sigma], \[Sigma]0, \[Sigma]1, \[CapitalDelta]\[Sigma], x, Id, Z, c, d\[Sigma], D\[Sigma], D2\[Sigma], L1, L2, M, Eigens, Filtered},
(* Operators appearing in the wave equation in coordinated (\[Tau], \[Sigma]), excluding radial derivatives *)
L1a = -((2 \[Sigma])/(\[Sigma]+1));
L1b = (1-2\[Sigma]^2)/(\[Sigma]+1);
L2a = (-l(l+1) - \[Sigma](1-s^2))/(\[Sigma]+1);
L2b = (\[Sigma](2-3\[Sigma]))/(\[Sigma]+1);
L2c = (\[Sigma]^2 (1-\[Sigma]))/(\[Sigma]+1);

Prec = 100; (*Numerical precision, machine precision found to be insufficient*)
			(* Make optional for users to set? Requires more testing as well *)
Ndiv = 5n; (* Subdivision of radial domain \[Sigma] \[Element] [0,1] used for discretization of radial derivs *)
ndiv = Ndiv +1; (* Matrix dimension *)

\[Sigma]0 = 0;
\[Sigma]1 = 1;
\[CapitalDelta]\[Sigma] = \[Sigma]1-\[Sigma]0;

x[i_]:= Cos[(i \[Pi])/Ndiv]; (* Chebyshev points *)
\[Sigma] = N[Table[\[Sigma]0 + \[CapitalDelta]\[Sigma]  (1+x[i])/2, {i, 0, Ndiv}], Prec]; (* Radial coordinate grid *)

Id = IdentityMatrix[ndiv];
Z = ConstantArray[0, {ndiv, ndiv}]; (* Zero matrix *)
c[i_] := If[i(i-Ndiv) ==0, 2, 1];

(* Radial derivative using Chebyshev-Lobatto method *)
d\[Sigma][i_, j_] := 2/\[CapitalDelta]\[Sigma] Which[i==j && i == 0, (2 Ndiv^2+1)/6, i==j && i == Ndiv, -((2 Ndiv^2+1)/6), i==j,  -x[i]/(2(1-x[i]^2)) , i!=j, c[i]/c[j] (-1)^(i+j)/(x[i]-x[j])] ;

(* First deriv matrix *)
D\[Sigma]=N[Table[d\[Sigma][i, j], {i, 0, Ndiv}, {j, 0, Ndiv}], Prec];
(* Second deriv matrix *)
D2\[Sigma] = D\[Sigma].D\[Sigma];

(* Full opertors in wave eq *)
L1 = L1b D\[Sigma] + L1a Id;
L2 = L2c D2\[Sigma] + L2b D\[Sigma] + L2a Id;

M = ArrayFlatten[{{Z, Id}, {L2, L1}}];

(* Solve for eigenvalues *)
Eigens = Eigenvalues[M] ;

(* Remove all values with Im[\[Omega]] = 0 *)
Filtered = Reverse[DeleteCases[Eigens,x_/;(Im[x]>=0. )]];

(*Pick out eigenvalue corresponding to the desired overtone *)
(*Would be nice to save this and use the other elements for initial seeds for other values of n *)
(*However, the accuracy decreases as one goes down the list *)
I/4 Filtered[[n+1]]
];





(* For Kerr, an initial guess is needed for both the frequency, and the spheroidal eigevalue Alm *)

Kerrfinit[s_, l_, m_, n_, a_] := Module[{b, \[CapitalDelta], \[Mu], Eikonal, Rp, \[CapitalOmega]r, \[CapitalOmega]i, finit},
\[CapitalDelta][r_] := r^2 -2 M r + a^2;
\[Mu] = m/(l+1/2);(* Useful parameter *)
Eikonal[rp_]:= 2(rp/M)^4(rp/M - 3)^2 + 4 (rp/M)^2((1 - \[Mu]^2)(rp/M)^2 - 2(rp/M) - 3(1 - \[Mu]^2))(a/M)^2 + (1 - \[Mu]^2) ( (2 - \[Mu]^2) (rp/M)^2 + 2 (2 + \[Mu]^2) (rp/M) + (2 - \[Mu]^2)) (a/M)^4;

(*2(rp/M)^4(rp/M - 3)^2 + 4 (rp/M)^2((1 - \[Mu]^2)(rp/M)^2 - 2(rp/M) - 3(1 - \[Mu]^2))(a/M)^2 + (1 - \[Mu]^2) ( (2 - \[Mu]^2) (rp/M)^2 + 2 (2 + \[Mu]^2) (rp/M) + (2 - \[Mu]^2)) (a/M)^4;*)

(*Eikonal2[rp_] := 2((3-rp)rp^2 - a^2(rp + 1))^2 -\[Mu]^2 a^2 (4rp^2(rp^2 -3) + a^2( 3rp^2 + 2rp + 3 - \[Mu]^2(rp -1)^2)); (* Needed to find eikonal limit for QNM frequencies*)*)

Rp = FindRoot[Eikonal[rp]==0, {rp, 3}] [[1]][[2]]; (* ISO? *)

\[CapitalOmega]r = -If[\[Mu] == 0, \[Pi]/2 Sqrt[\[CapitalDelta][Rp]]/((Rp^2 + a^2) EllipticE[(a^2 \[CapitalDelta][Rp])/((Rp^2 + a^2)^2)] ) , (M - Rp) \[Mu] a / ((Rp - 3M)Rp^2 + (Rp + M) a^2)];
(*If[\[Mu] \[Equal] 0, \[Pi]/2 Sqrt[\[CapitalDelta][Rp]]/((Rp^2 + a^2) EllipticE[(a^2 \[CapitalDelta][Rp])/((Rp^2 + a^2)^2)] ) , (M - Rp) \[Mu] a / ((Rp - 3M)Rp^2 + (Rp + M) a^2)];*)

(*(Sqrt[2](Rp-1))/(Sqrt[4Rp^2(Rp^2 -3) + a^2(3Rp^2 + 2Rp + 3 - \[Mu]^2(Rp -1)^2)]); *)
\[CapitalOmega]i = \[CapitalDelta][Rp](Sqrt[4(6Rp^2 \[CapitalOmega]r^2 -1) + 2a^2\[CapitalOmega]r^2(3 - \[Mu]^2)])/(2 Rp^4 \[CapitalOmega]r - 4 a M Rp \[Mu] + a^2 Rp \[CapitalOmega]r(Rp(3 - \[Mu]^2) + 2 M(1+\[Mu]^2)) + a^4\[CapitalOmega]r(1-\[Mu]^2));

(*\[CapitalDelta][Rp](Sqrt[4(6Rp^2 \[CapitalOmega]r^2 -1) + 2a^2\[CapitalOmega]r^2(3 - \[Mu]^2)])/(2 Rp^4 \[CapitalOmega]r - 4 a M Rp \[Mu] + a^2 Rp \[CapitalOmega]r(Rp(3 - \[Mu]^2) + 2 M(1+\[Mu]^2)) + a^4\[CapitalOmega]r(1-\[Mu]^2));*)

finit = (l + 1/2) \[CapitalOmega]r - I (n + 1/2) \[CapitalOmega]i
];

KerrAinit[s_, l_, m_, n_, a_] := (l+1/2)^2 - (a Kerrfinit[s, l, m, n, a])^2 /2 (1 - (m/(l+1/2))^2);(* l(l+1) - s(s+1);*)


(* The functions for the continued fraction provide the actual equations of which the QNMs and spheroidal eigenvalues are roots *)
(* These functions allow for the n-th inversion to be easily identified, and make use of memoization to improve eficiency by
avoiding repeated calls to the same functions. *)

(*Would be nice to remove the While loops and replace with something like FixedPoint *)

ContFrac[\[Omega]_,s_, l_, nInv_] := Module [{A,B,ak,bk,res=Indeterminate, j = nInv+1},
A[(nInv+1)-2, \[Omega]]=1;
B[(nInv+1)-2, \[Omega]]=0;
ak[k_, \[Omega]]:=ak[k, \[Omega]]=-\[Alpha][k-1, \[Omega]] \[Gamma][k, \[Omega], s];
bk[k_, \[Omega]]:=bk[k, \[Omega]]=\[Delta][k, \[Omega], s, l];
A[(nInv+1)-1, \[Omega]](*/;(n+1)-1 \[NotEqual] 0*)=0(*bk[n0-1]*);
(*A[(n+1)-1, \[Omega]]/;(n+1)-1 \[Equal]  0=bk[n-1, \[Omega]];*)
B[(nInv+1)-1, \[Omega]]=1;
A[k_, \[Omega]]:=A[k, \[Omega]]=bk[k, \[Omega]] A[k-1, \[Omega]]+ak[k, \[Omega]] A[k-2, \[Omega]];
B[k_, \[Omega]]:= B[k, \[Omega]]=bk[k, \[Omega]] B[k-1, \[Omega]]+ak[k, \[Omega]] B[k-2, \[Omega]];
res = A[j-1, \[Omega]]/B[j-1, \[Omega]];
While[res =!=(res=A[j, \[Omega]]/B[j, \[Omega]]),res = A[j, \[Omega]]/B[j, \[Omega]]; j++];
(*FixedPoint[A[#]/B[#], j]*)
res
];

ContFracfreq[\[Omega]_, Alm_,s_, m_, a_, nInv_] := Module [{A,B,ak,bk,res=Indeterminate, j = nInv+1},
A[(nInv+1)-2, \[Omega]]=1;
B[(nInv+1)-2, \[Omega]]=0;
ak[k_, \[Omega]]:=ak[k, \[Omega]]=-\[Alpha]freq[k-1, \[Omega], s, m, a] \[Gamma]freq[k, \[Omega], s, m, a];
bk[k_, \[Omega]]:=bk[k, \[Omega]]=\[Beta]freq[k, \[Omega], Alm, s, m, a];
A[(nInv+1)-1, \[Omega]](*/;(n+1)-1 \[NotEqual] 0*)=0(*bk[n0-1]*);
(*A[(n+1)-1, \[Omega]]/;(n+1)-1 \[Equal]  0=bk[n-1, \[Omega]];*)
B[(nInv+1)-1, \[Omega]]=1;
A[k_, \[Omega]]:=A[k, \[Omega]]=bk[k, \[Omega]] A[k-1, \[Omega]]+ak[k, \[Omega]] A[k-2, \[Omega]];
B[k_, \[Omega]]:= B[k, \[Omega]]=bk[k, \[Omega]] B[k-1, \[Omega]]+ak[k, \[Omega]] B[k-2, \[Omega]];
res = A[j-1, \[Omega]]/B[j-1, \[Omega]];
While[res =!=(res=A[j, \[Omega]]/B[j, \[Omega]]),res = A[j, \[Omega]]/B[j, \[Omega]]; j++];
(*FixedPoint[A[#]/B[#], j]*)
res
];

ContFracang[\[Omega]_,Alm_,s_, m_, a_, nInv_] := Module [{A,B,ak,bk,res=Indeterminate, j = nInv+1},
A[(nInv+1)-2, \[Omega]]=1;
B[(nInv+1)-2, \[Omega]]=0;
ak[k_, \[Omega]]:=ak[k, \[Omega]]=-\[Alpha]ang[k-1, \[Omega], s, m, a] \[Gamma]ang[k, \[Omega], s, m, a];
bk[k_, \[Omega]]:=bk[k, \[Omega]]=\[Beta]ang[k, \[Omega], Alm, s, m, a];
A[(nInv+1)-1, \[Omega]](*/;(n+1)-1 \[NotEqual] 0*)=0(*bk[n0-1]*);
(*A[(n+1)-1, \[Omega]]/;(n+1)-1 \[Equal]  0=bk[n-1, \[Omega]];*)
B[(nInv+1)-1, \[Omega]]=1;
A[k_, \[Omega]]:=A[k, \[Omega]]=bk[k, \[Omega]] A[k-1, \[Omega]]+ak[k, \[Omega]] A[k-2, \[Omega]];
B[k_, \[Omega]]:= B[k, \[Omega]]=bk[k, \[Omega]] B[k-1, \[Omega]]+ak[k, \[Omega]] B[k-2, \[Omega]];
res = A[j-1, \[Omega]]/B[j-1, \[Omega]];
While[res =!=(res=A[j, \[Omega]]/B[j, \[Omega]]),res = A[j, \[Omega]]/B[j, \[Omega]]; j++];
(*FixedPoint[A[#]/B[#], j]*)
res
];

Leaver[\[Omega]_?NumericQ, s_?IntegerQ, l_?IntegerQ, nInv_?IntegerQ] := \[Delta][nInv,\[Omega], s, l] + ContinuedFractionK[-\[Alpha][nInv-i, \[Omega]] \[Gamma][nInv-i+1, \[Omega], s],\[Delta][nInv-i,\[Omega],s, l],{i,1,nInv}] + ContFrac[\[Omega], s, l, nInv];

Leaver31[\[Omega]_?NumericQ, Alm_?NumericQ, s_?IntegerQ, m_?IntegerQ, a_?NumericQ, nInv_?IntegerQ] := \[Beta]freq[nInv,\[Omega], Alm, s, m, a]+ContinuedFractionK[-\[Alpha]freq[nInv-i, \[Omega], s, m, a] \[Gamma]freq[nInv-i+1, \[Omega], s, m, a],\[Beta]freq[nInv-i,\[Omega], Alm, s, m, a],{i,1,nInv}] + ContFracfreq[\[Omega], Alm,s, m, a, nInv];
Leaver31ang[\[Omega]_?NumericQ, Alm_?NumericQ, s_?IntegerQ, m_?IntegerQ, a_?NumericQ, nInv_?IntegerQ] := \[Beta]ang[nInv,\[Omega], Alm, s, m, a]+ContinuedFractionK[-\[Alpha]ang[nInv-i, \[Omega], s, m, a] \[Gamma]ang[nInv-i+1, \[Omega], s, m, a],\[Beta]ang[nInv-i,\[Omega], Alm, s, m, a],{i,1,nInv}] + ContFracang[\[Omega], Alm,s, m, a, nInv];




QNMSchwarzschild[s_Integer, l_Integer, n_Integer] /; l < Abs[s] := 0; 

QNMSchwarzschild[s_Integer, l_Integer, n_Integer] := Module[{NInv, finit, Sol, freq},
NInv = n;

If[n >= 6 && 3 <= l && l < n, Message[QuasiNormalMode::SchwarzUntrusted, l, n]];

(*Selection of initial seed method *)
(*Ideally, we would first check how well this satisfies the eq to be solved.
 If within the user's desired accuracy, just return the initial guess.
 Would be faster *)
Which[l< 2, finit = Schwarzfinit2[n], n < 6 && l >=  2, finit = Schwarzfinit1[s, l, n], n >=6 && l>=2 && l <=n, finit=SpectralInitialGuess[s, l, n], n >=6 && l>n, finit=Schwarzfinit1[s, l, n]];

Sol = FindRoot[{Re[Leaver[x +I y, s, l, NInv]] == 0, Im[Leaver[x + I y, s, l, NInv]] == 0}, {x,Re[finit]}, {y, Im[finit]}];

freq = Sol[[1]][[2]] + I Sol[[2]][[2]];

(*Print["Is this a solution?", " ", Leaver[freq, s, l, NInv]];*)

freq
];


QNMKerr[s_Integer, l_Integer, m_Integer, n_Integer, a_Real] /; l < Abs[s] || l < Abs[m]  := 0; (* Imposing condition on QNMKerr as QNMSchwarzschild should be independent of m *)

QNMKerr[s_Integer, l_Integer, m_Integer, n_Integer, a_Real] :=Module[{\[Epsilon], err, NInv, Ainit,finit, Sol,freq, A},
NInv = n;

If[ 2 <= l, Message[QuasiNormalMode::KerrUntrusted, l]];
If[ 0.9 < a, Message[QuasiNormalMode::UntrustedSpin, a]];

Ainit = KerrAinit[s, l, m, n, a];
finit = Kerrfinit[s, l, m, n, a];
(*Print[finit, " ", Ainit];*)

(*If[l < 4, Sol = FindRoot[{Re[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Re[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0},{\[Omega]x, Re[finit]}, {\[Omega]y, Im[finit]}, {Ax, Re[Ainit]}, {Ay, Im[Ainit]}], Sol = FindRoot[{Re[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Re[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0},{\[Omega]x, Re[finit]}, {\[Omega]y, Im[finit]}, {Ax, Re[Ainit], 0.6 Re[Ainit], 10 Re[Ainit]}, {Ay, Im[Ainit], 0.6 Im[Ainit], 10 Im[Ainit]}]];*)
Sol = FindRoot[{Re[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Re[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0},{\[Omega]x, Re[finit]}, {\[Omega]y, Im[finit]}, {Ax, Re[Ainit](*, 0.6 Re[Ainit], 100 Re[Ainit]*)}, {Ay, Im[Ainit](*, 0.6 Im[Ainit], 100 Im[Ainit]*)}];
(*
\[Epsilon] = 0.1;

While[err \[Equal] Quiet@Check[Sol = FindRoot[{Re[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Re[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0, Im[Leaver31ang[\[Omega]x + \[Omega]y I, Ax + Ay I, s, m, a, NInv]]==0},{\[Omega]x, Re[finit]}, {\[Omega]y, Im[finit]}, {Ax, Re[Ainit], 0.5 Re[Ainit], (1+\[Epsilon]) Re[Ainit]}, {Ay, Im[Ainit], 0.5 Im[Ainit], (1+\[Epsilon]) Im[Ainit]}], err],
Print[Sol];
\[Epsilon] += 0.1
];
*)

(*Print["Alm = ", Sol[[3]][[2]] + I Sol[[4]][[2]]];*)

(*Print[steps];*)

freq = Sol[[1]][[2]] + I Sol[[2]][[2]];
A = Sol[[3]][[2]] + I Sol[[4]][[2]];

(*Print["Are these solutions?", " ", Leaver31[freq, A, s, m, a, NInv], " ", Leaver31ang[freq, A, s, m, a, NInv]];*)

If[Sol[[1]][[2]] < 0, freq = -Sol[[1]][[2]] + I Sol[[2]][[2]]]; (* Want to return all solutions in lower right quadrant for consistency *)
(*A = Sol[[3]][[2]] + I Sol[[4]][[2]];*) (*May allow this to be returned as well, but for now the package is designed entirely to be QNMs only*)

freq
];


(*Consolidation of the above into a single function *)

SyntaxInformation[QuasiNormalMode] = {ArgumentsPattern->{_, _, _, _, _}}; (* This specifies that QuasiNormalMode takes exactly 5 arguments*)

(*QuasiNormalMode[s_Integer, l_Integer, m_Integer, n_Integer, a_Real] /; l < Abs[s] := 0;*)
QuasiNormalMode[s_Integer, l_Integer, m_Integer, n_Integer, a_Real] /; Abs[s] > 2 := 0;
QuasiNormalMode[s_Integer, l_Integer, m_Integer, n_Integer, a_Real] /; a > 0.999 || a < 0 := 0;
QuasiNormalMode[s_Integer, l_Integer, m_Integer, n_Integer, a_Real] /; a == 0. := QNMSchwarzschild[s, l, n];
QuasiNormalMode[s_Integer, l_Integer, m_Integer, n_Integer, a_Integer] /; a == 0 := QNMSchwarzschild[s, l, n];
QuasiNormalMode[s_Integer, l_Integer, m_Integer, n_Integer, a_Real] := QNMKerr[s, l, m, n, a];
QuasiNormalMode[s_Integer, l_Integer, m_Integer, n_Integer, a_Integer] := QNMKerr[s, l, m, n, N[a]]; (* Unusual behaviour in the case where a was an integer (in these units, 0 is the only possible integer value) was encounterd and the function would not evaluate. *)

SetAttributes[QuasiNormalMode, {NumericFunction, Listable, Protected}]; (* This function will be assumed to have a numerical value, if its arguments are numeric.
																		It will also be automatically threaded over lists (so can compute QNMs for a list of modes.*)


End[];

EndPackage[];
