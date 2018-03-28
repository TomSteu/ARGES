Needs["SARGES`", "~/ARGES/SARGES.m"];
Reset[];

NumberOfSubgroups = 2;

Gauge[g1, SU, N1, {N1^2 - 1, 1}];
Gauge[g2, SU, N2, {1, N2^2-1}];

ChiralSuperField[psiL, Nf, {N1, 1}];
ChiralSuperField[psiR, Nf, {N1, 1}];
ChiralSuperField[PsiL, 1, {N1, N2}];
ChiralSuperField[PsiR, 1, {N1, N2}];
ChiralSuperField[chiL, Nf, {1, N2}];
ChiralSuperField[chiR, Nf, {1, N2}];
ChiralSuperField[QL, NQ, {1, N2}];
ChiralSuperField[QR, NQ, {1, N2}];

SuperYukawa[y, psiL, PsiL, chiL, {KroneckerDelta[#1, #2]&, KroneckerDelta[#2,#3]&}, KroneckerDelta[#1,#3]&];
SuperYukawa[y, psiR, PsiR, chiR, {KroneckerDelta[#1, #2]&, KroneckerDelta[#2,#3]&}, KroneckerDelta[#1,#3]&];

ComputeInvariants[];

simp[x_] := Expand[x //. subInvariants //. {
	conj[A_] :> A,
	g1 -> 4 Pi Sqrt[\[Alpha]1/N1],
	g2 -> 4 Pi Sqrt[\[Alpha]2/N2],
	y -> 4 Pi Sqrt[\[Alpha]y/N1],
	N2 -> N1 R, 
	Nf -> N1 \[Epsilon] - N2 + 3 N1,
	NQ -> P R (Nf + N2 - 3 N1) + 3 N2 - N1 - Nf
}];

lim[x_] := Expand[Limit[x, N1->Infinity]];
