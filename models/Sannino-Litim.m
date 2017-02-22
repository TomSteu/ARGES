Needs["ARGES`"]
Reset[];
NumberOfSubgroups = 1;
Gauge[g, SU, Nc, {Sqr[Nc] - 1}];
WeylFermion[QL, Nf, {Nc}];
WeylFermion[QR, Nf, {Nc}];
ComplexScalar[H, {Nf, Nf}, {1}];
YukawaY[y, H, QL, QR, {KroneckerDelta[#2,#3] &}, (KroneckerDelta[#1,#3] KroneckerDelta[#2,#4])&];
Quartic\[Lambda]abcd[v, adj[H], H, adj[H], H, {1&}, (KroneckerDelta[#1, #4] KroneckerDelta[#2, #3] KroneckerDelta[#5, #8] KroneckerDelta[#6, #7])&];
Quartic\[Lambda]abcd[u, adj[H], H, adj[H], H, {1&}, (KroneckerDelta[#2, #3] KroneckerDelta[#4,#5] KroneckerDelta[#6,#7] KroneckerDelta[#8,#1])&];
ComputeInvariants[];
