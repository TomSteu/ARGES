Needs["ARGES`"]
Reset[];
NumberOfSubgroups = 1;
Gauge[g, SU, Nc, {Sqr[Nc] - 1}];
WeylFermion[QL, Nf, {Nc}];
WeylFermion[QR, Nf, {Nc}];
ComplexScalar[H, Sqr[Nf], {1}];
GenInd1[a_]:=If[Mod[a,Nf] == 0, Quotient[a]-1, Quotient[a]];
GenInd2[a_]:=If[Mod[a,Nf] == 0, Nf, Mod[a,Nf]];
YukawaY[y, H, QL, QR, {KroneckerDelta[#2,#3] &}, (KroneckerDelta[Nf(#2 - 1) + #3 - #1])&];
Quartic\[Lambda]abcd[v, adj[H], H, adj[H], H, {1&}, (KroneckerDelta[#1, #4] KroneckerDelta[#2, #3] KroneckerDelta[#5, #8] KroneckerDelta[#6, #7])&];
Quartic\[Lambda]abcd[u, adj[H], H, adj[H], H, {1&}, (KroneckerDelta[#2, #3] KroneckerDelta[#4, #5] KroneckerDelta[#6, #7] KroneckerDelta[#8, #1])&];
ComputeInvariants[];
